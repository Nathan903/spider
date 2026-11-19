//! Verified regular-task completion counting.

use std::sync::Arc;

use vstd::atomic_ghost::AtomicInvariantPredicate;
use vstd::atomic_ghost::AtomicUsize;
use vstd::atomic_ghost::atomic_with_ghost;
#[cfg(not(verus_only))]
use vstd::pcm::Loc;
use vstd::prelude::*;
#[cfg(verus_only)]
use vstd::resource::Loc;
#[cfg(verus_only)]
use vstd::resource::map::GhostMapAuth;
#[cfg(verus_only)]
use vstd::resource::map::GhostPointsTo;
#[cfg(not(verus_only))]
use vstd::tokens::map::GhostMapAuth;
#[cfg(not(verus_only))]
use vstd::tokens::map::GhostPointsTo;

verus! {

broadcast use vstd::map::group_map_axioms;

/// Relates the executable counter to the authoritative set of unfinished tasks.
struct CounterPredicate;

impl AtomicInvariantPredicate<(usize, Loc), usize, GhostMapAuth<usize, ()>> for CounterPredicate {
    closed spec fn atomic_inv(
        constant: (usize, Loc),
        value: usize,
        auth: GhostMapAuth<usize, ()>,
    ) -> bool {
        &&& auth.id() == constant.1
        &&& auth.dom().finite()
        &&& auth.dom().len() == value
        &&& value <= constant.0
        &&& forall|task: usize| auth.dom().contains(task) ==> task < constant.0
    }
}

/// The task identity and linear resource carried by a completion token.
struct CompletionCore {
    task: usize,
    point: Tracked<GhostPointsTo<usize, ()>>,
}

impl CompletionCore {
    /// # Returns
    ///
    /// Whether this core belongs to `id` and represents one of `num_tasks` regular tasks.
    closed spec fn invariant(&self, id: Loc, num_tasks: usize) -> bool {
        &&& self.point@.id() == id
        &&& self.point@.key() == self.task
        &&& self.task < num_tasks
    }
}

/// An atomic count backed by linear authority for each unfinished regular task.
///
/// The atomic invariant equates the executable value with the cardinality of the authoritative
/// unfinished-task map. A decrement requires and consumes the corresponding task's token, which
/// proves that the value is positive before subtraction. Therefore the count cannot underflow, and
/// only the final token can produce a remaining count of zero.
pub struct CompletionCounter {
    atomic: AtomicUsize<(usize, Loc), GhostMapAuth<usize, ()>, CounterPredicate>,
}

impl CompletionCounter {
    /// # Returns
    ///
    /// The mathematical initial number of regular tasks.
    pub closed spec fn num_tasks_spec(&self) -> usize {
        self.atomic.constant().0
    }

    /// # Returns
    ///
    /// The mathematical identity shared by the counter and its completion tokens.
    pub closed spec fn id_spec(&self) -> Loc {
        self.atomic.constant().1
    }

    /// # Returns
    ///
    /// Whether the executable value equals the cardinality of the authoritative unfinished-task
    /// map.
    pub closed spec fn invariant(&self) -> bool {
        self.atomic.well_formed()
    }

    /// Creates a shared counter and one completion token for each regular task.
    ///
    /// Every token retains the counter that created it. This prevents ordinary Rust callers from
    /// applying a valid token to a different counter, where Verus preconditions are not checked.
    ///
    /// # Returns
    ///
    /// The initialized counter and its completion tokens.
    ///
    /// # Panics
    ///
    /// Panics if the internal completion-core vector loses an element while it is converted into
    /// tokens.
    #[must_use]
    pub fn new(num_tasks: usize) -> (result: (Arc<Self>, Vec<CompletionToken>))
        ensures
            result.0.invariant(),
            result.0.num_tasks_spec() == num_tasks,
            result.1@.len() == num_tasks,
            forall|i: int| 0 <= i < result.1@.len() ==> {
                &&& #[trigger] result.1@[i].invariant()
                &&& result.1@[i].counter_id_spec() == result.0.id_spec()
                &&& result.1@[i].task_spec() == num_tasks - 1 - i
            },
    {
        /* C7 needs a distinct linear resource for each regular task and one shared atomic
         * invariant.
         * Origin Rust: <none; new executable code>
         */
        let tracked (mut auth, _empty) = GhostMapAuth::<usize, ()>::new(Map::empty());
        let mut cores: Vec<CompletionCore> = Vec::new();
        let mut task = 0;
        while task < num_tasks
            invariant
                task <= num_tasks,
                auth.dom().finite(),
                auth@.len() == task,
                forall|i: usize| auth.dom().contains(i) <==> i < task,
                cores@.len() == task,
                forall|i: int| 0 <= i < cores@.len() ==> {
                    &&& #[trigger] cores@[i].invariant(auth.id(), num_tasks)
                    &&& cores@[i].task == i
                },
            decreases num_tasks - task
        {
            let tracked point = auth.insert(task, ());
            cores.push(CompletionCore {
                task,
                point: Tracked(point),
            });
            task += 1;
        }
        let _id = Ghost(auth.id());
        let atomic = AtomicUsize::new(Ghost((num_tasks, _id@)), num_tasks, Tracked(auth));
        let counter = Arc::new(Self { atomic });
        let mut tokens: Vec<CompletionToken> = Vec::new();
        while !cores.is_empty()
            invariant
                counter.invariant(),
                counter.num_tasks_spec() == num_tasks,
                cores@.len() + tokens@.len() == num_tasks,
                forall|i: int| 0 <= i < cores@.len() ==> {
                    &&& #[trigger] cores@[i].invariant(counter.id_spec(), num_tasks)
                    &&& cores@[i].task == i
                },
                forall|i: int| 0 <= i < tokens@.len() ==> {
                    &&& #[trigger] tokens@[i].invariant()
                    &&& tokens@[i].counter_id_spec() == counter.id_spec()
                    &&& tokens@[i].task_spec() == num_tasks - 1 - i
                },
            decreases cores.len()
        {
            let _last_index = cores.len() - 1;
            proof {
                assert(cores@[_last_index as int].invariant(counter.id_spec(), num_tasks));
                assert(cores@[_last_index as int].task == _last_index);
            }
            let core = cores.pop().expect("completion core should exist");
            proof {
                assert(core.task == _last_index);
                assert(cores@.len() + tokens@.len() + 1 == num_tasks);
            }
            tokens.push(CompletionToken {
                counter: Arc::clone(&counter),
                core,
            });
        }
        (counter, tokens)
    }

    /// Reads the atomic count without changing it.
    ///
    /// # Returns
    ///
    /// The current number of unfinished regular tasks.
    #[must_use]
    pub fn remaining(&self) -> (remaining: usize)
        requires
            self.invariant(),
        ensures
            remaining <= self.num_tasks_spec(),
    {
        /* Tests and cache diagnostics need a verified snapshot of the new counter.
         * Origin Rust: <none; new executable code>
         */
        atomic_with_ghost!(
            &self.atomic => load();
            returning ret;
            ghost auth => {}
        )
    }
}

/// Linear authority to report one regular task's successful completion.
///
/// A token retains the counter that created it. Consuming the token removes the same task from that
/// counter's authoritative unfinished set. Rust ownership prevents reuse.
pub struct CompletionToken {
    counter: Arc<CompletionCounter>,
    core: CompletionCore,
}

impl CompletionToken {
    /// # Returns
    ///
    /// The mathematical identity of this token's counter.
    pub closed spec fn counter_id_spec(&self) -> Loc {
        self.counter.id_spec()
    }

    /// # Returns
    ///
    /// The mathematical task index represented by this token.
    pub closed spec fn task_spec(&self) -> usize {
        self.core.task
    }

    /// # Returns
    ///
    /// The mathematical initial task count of this token's counter.
    pub closed spec fn num_tasks_spec(&self) -> usize {
        self.counter.num_tasks_spec()
    }

    /// # Returns
    ///
    /// Whether the token has valid authority for one task in its retained counter.
    pub closed spec fn invariant(&self) -> bool {
        &&& self.counter.invariant()
        &&& self.core.invariant(self.counter.id_spec(), self.counter.num_tasks_spec())
    }

    /// Consumes this regular task's completion authority and atomically decrements its counter.
    ///
    /// # Returns
    ///
    /// The remaining number of unfinished regular tasks. Zero identifies the unique transition on
    /// which the authoritative unfinished-task map became empty.
    #[must_use]
    pub fn complete(self) -> (remaining: usize)
        requires
            self.invariant(),
        ensures
            remaining < self.num_tasks_spec(),
    {
        /* The retained counter prevents cross-counter token use. The ghost update proves that the
         * original subtraction cannot underflow and strengthens its ordering to SeqCst.
         * Origin Rust:
         * let num_incomplete_tasks =
         *     job.num_incomplete_tasks.fetch_sub(1, Ordering::AcqRel) - 1;
         */
        let Self {
            counter: retained_counter,
            core: completion_core,
        } = self;
        let CompletionCore {
            task: task_index,
            point: Tracked(point),
        } = completion_core;
        let _ = task_index;
        let previous = atomic_with_ghost!(
            &retained_counter.atomic => fetch_sub(1);
            update prev -> next;
            returning ret;
            ghost auth => {
                point.agree(&auth);
                assert(auth.dom().contains(point.key()));
                assert(auth.dom().len() > 0);
                auth.delete_points_to(point);
            }
        );
        previous - 1
    }
}

}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    /// Every completion observes a distinct remaining count, including exactly one zero.
    #[test]
    fn concurrent_completions_have_one_final_reporter() {
        // Exercise the counter under concurrent executable calls.
        // Origin Rust: <none; new executable code>
        const NUM_TASKS: usize = 16;

        let (counter, tokens) = CompletionCounter::new(NUM_TASKS);
        let mut reporters = Vec::new();
        for token in tokens {
            reporters.push(std::thread::spawn(move || token.complete()));
        }

        let mut remaining = reporters
            .into_iter()
            .map(|reporter| {
                reporter
                    .join()
                    .expect("completion reporter should not panic")
            })
            .collect::<Vec<_>>();
        remaining.sort_unstable();
        assert_eq!(remaining, (0..NUM_TASKS).collect::<Vec<_>>());
        assert_eq!(counter.remaining(), 0);
        assert_eq!(Arc::strong_count(&counter), 1);
    }
}
