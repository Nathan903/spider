//! Runtime-free DAG construction and task-readiness primitives.

use vstd::prelude::*;

verus! {

/// An edge in a task graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edge {
    parent: usize,
    child: usize,
}

impl Edge {
    /// # Returns
    ///
    /// The mathematical parent task index.
    pub closed spec fn parent_spec(&self) -> usize {
        self.parent
    }

    /// # Returns
    ///
    /// The mathematical child task index.
    pub closed spec fn child_spec(&self) -> usize {
        self.child
    }

    /// # Returns
    ///
    /// The parent task index.
    #[must_use]
    pub const fn parent(&self) -> usize {
        self.parent
    }

    /// # Returns
    ///
    /// The child task index.
    #[must_use]
    pub const fn child(&self) -> usize {
        self.child
    }
}

/// Errors returned when inserting a task into a [`Dag`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DagError {
    DuplicateParent { parent: usize },
    ParentOutOfRange { parent: usize, child: usize },
    TaskCountOverflow,
}

/// A task DAG whose task indices form a topological ordering.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Dag {
    num_tasks: usize,
    edges: Vec<Edge>,
}

impl Dag {
    /// # Returns
    ///
    /// The mathematical task count.
    pub closed spec fn num_tasks_spec(&self) -> usize {
        self.num_tasks
    }

    /// # Returns
    ///
    /// The mathematical edge sequence.
    pub closed spec fn edges_spec(&self) -> Seq<Edge> {
        self.edges@
    }

    /// # Returns
    ///
    /// Whether every edge references existing tasks and strictly increases the task index.
    pub closed spec fn is_topologically_ordered_spec(&self) -> bool {
        forall|position: int| 0 <= position < self.edges@.len() ==> {
            let edge = #[trigger] self.edges@[position];
            edge.parent < edge.child && edge.child < self.num_tasks
        }
    }

    /// # Returns
    ///
    /// Whether no two stored edges have the same parent and child.
    pub closed spec fn has_unique_edges_spec(&self) -> bool {
        forall|left: int, right: int|
            0 <= left < self.edges@.len()
                && 0 <= right < self.edges@.len()
                && left != right
                ==> {
                    let left_edge = #[trigger] self.edges@[left];
                    let right_edge = #[trigger] self.edges@[right];
                    left_edge.parent != right_edge.parent || left_edge.child != right_edge.child
                }
    }

    /// # Returns
    ///
    /// Whether the DAG's representation invariant holds.
    pub closed spec fn invariant(&self) -> bool {
        self.is_topologically_ordered_spec() && self.has_unique_edges_spec()
    }

    /// # Returns
    ///
    /// Whether the DAG contains `parent -> child`.
    pub closed spec fn has_edge_spec(&self, parent: nat, child: nat) -> bool {
        exists|position: int| 0 <= position < self.edges@.len() && {
            let edge = #[trigger] self.edges@[position];
            edge.parent == parent && edge.child == child
        }
    }

    /// # Returns
    ///
    /// Whether a nonempty path of at most `fuel` edges connects `from` to `to`.
    pub closed spec fn reaches_spec(&self, from: nat, to: nat, fuel: nat) -> bool
        decreases fuel,
    {
        fuel > 0 && (
            self.has_edge_spec(from, to)
                || exists|next: nat|
                    self.has_edge_spec(from, next)
                        && self.reaches_spec(next, to, (fuel - 1) as nat)
        )
    }

    /// # Returns
    ///
    /// Whether no task can reach itself through a nonempty path.
    pub closed spec fn is_acyclic_spec(&self) -> bool {
        forall|task: nat, fuel: nat| !self.reaches_spec(task, task, fuel)
    }

    /// Proves that the topological task-index ordering excludes cycles.
    pub proof fn lemma_is_acyclic(&self)
        requires
            self.invariant(),
        ensures
            self.is_acyclic_spec(),
    {
        reveal(Dag::is_acyclic_spec);
        assert forall|task: nat, fuel: nat| !self.reaches_spec(task, task, fuel) by {
            if self.reaches_spec(task, task, fuel) {
                self.lemma_reaches_increases(task, task, fuel);
            }
        }
    }

    /// Creates an empty DAG.
    ///
    /// # Returns
    ///
    /// An empty DAG.
    #[must_use]
    pub const fn new() -> (result: Self)
        ensures
            result.invariant(),
            result.num_tasks_spec() == 0,
            result.edges_spec() == Seq::<Edge>::empty(),
    {
        Self {
            num_tasks: 0,
            edges: Vec::new(),
        }
    }

    /// Inserts a task whose parents have already been inserted.
    ///
    /// # Returns
    ///
    /// The new task's index on success.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    ///
    /// * [`DagError::DuplicateParent`] if `parent_indices` contains a duplicate.
    /// * [`DagError::ParentOutOfRange`] if a parent has not already been inserted.
    /// * [`DagError::TaskCountOverflow`] if the task count cannot be incremented.
    pub fn insert_task(
        &mut self,
        parent_indices: &[usize],
    ) -> (result: Result<usize, DagError>)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            match result {
                Ok(child) => {
                    &&& child == old(self).num_tasks_spec()
                    &&& final(self).num_tasks_spec() == old(self).num_tasks_spec() + 1
                    &&& final(self).edges_spec().len()
                        == old(self).edges_spec().len() + parent_indices@.len()
                    &&& final(self).edges_spec().take(
                        old(self).edges_spec().len() as int,
                    ) == old(self).edges_spec()
                    &&& forall|position: int| 0 <= position < parent_indices@.len() ==> {
                        let edge = #[trigger] final(self).edges_spec()[
                            old(self).edges_spec().len() + position
                        ];
                        &&& parent_indices@[position] < child
                        &&& edge.parent_spec() == parent_indices@[position]
                        &&& edge.child_spec() == child
                    }
                    &&& forall|left: int, right: int|
                        0 <= left < right < parent_indices@.len()
                            ==> parent_indices@[left] != parent_indices@[right]
                }
                Err(_) => {
                    &&& final(self).num_tasks_spec() == old(self).num_tasks_spec()
                    &&& final(self).edges_spec() == old(self).edges_spec()
                }
            },
    {
        let child = self.num_tasks;
        let Some(next_num_tasks) = self.num_tasks.checked_add(1) else {
            return Err(DagError::TaskCountOverflow);
        };

        /*
         * Verus does not support the composed `enumerate`/`copied` slice iterator.
         *
         * Origin Rust:
         * for (position, parent) in parent_indices.iter().copied().enumerate() {
         *     if parent >= child {
         *         return Err(DagError::ParentOutOfRange { parent, child });
         *     }
         *     if parent_indices[..position].contains(&parent) {
         *         return Err(DagError::DuplicateParent { parent });
         *     }
         * }
         */
        let mut position = 0;
        while position < parent_indices.len()
            invariant
                self.invariant(),
                self.num_tasks_spec() == old(self).num_tasks_spec(),
                self.edges_spec() == old(self).edges_spec(),
                child == old(self).num_tasks_spec(),
                next_num_tasks == child + 1,
                position <= parent_indices@.len(),
                forall|index: int| 0 <= index < position ==> {
                    #[trigger] parent_indices@[index] < child
                },
                forall|left: int, right: int| 0 <= left < right < position ==> {
                    #[trigger] parent_indices@[left] != #[trigger] parent_indices@[right]
                },
            decreases parent_indices.len() - position
        {
            let parent = parent_indices[position];
            if parent >= child {
                return Err(DagError::ParentOutOfRange { parent, child });
            }
            let mut previous_position = 0;
            while previous_position < position
                invariant
                    self.invariant(),
                    self.num_tasks_spec() == old(self).num_tasks_spec(),
                    self.edges_spec() == old(self).edges_spec(),
                    child == old(self).num_tasks_spec(),
                    next_num_tasks == child + 1,
                    previous_position <= position,
                    position < parent_indices@.len(),
                    parent == parent_indices@[position as int],
                    parent < child,
                    forall|index: int| 0 <= index < position ==> {
                        #[trigger] parent_indices@[index] < child
                    },
                    forall|left: int, right: int| 0 <= left < right < position ==> {
                        #[trigger] parent_indices@[left] != #[trigger] parent_indices@[right]
                    },
                    forall|index: int| 0 <= index < previous_position ==> {
                        #[trigger] parent_indices@[index] != parent
                    },
                decreases position - previous_position
            {
                if parent_indices[previous_position] == parent {
                    return Err(DagError::DuplicateParent { parent });
                }
                previous_position += 1;
            }
            position += 1;
        }

        self.num_tasks = next_num_tasks;
        /*
         * Verus does not support the composed `map` iterator passed to [`Vec::extend`].
         *
         * Origin Rust:
         * self.edges.extend(
         *     parent_indices
         *         .iter()
         *         .copied()
         *         .map(|parent| Edge { parent, child }),
         * );
         */
        let mut position = 0;
        while position < parent_indices.len()
            invariant
                old(self).invariant(),
                child == old(self).num_tasks_spec(),
                next_num_tasks == child + 1,
                self.num_tasks_spec() == next_num_tasks,
                position <= parent_indices@.len(),
                self.edges_spec().len() == old(self).edges_spec().len() + position,
                self.edges_spec().take(old(self).edges_spec().len() as int)
                    == old(self).edges_spec(),
                forall|index: int| 0 <= index < parent_indices@.len() ==> {
                    #[trigger] parent_indices@[index] < child
                },
                forall|left: int, right: int|
                    0 <= left < right < parent_indices@.len() ==> {
                        #[trigger] parent_indices@[left] != #[trigger] parent_indices@[right]
                    },
                forall|index: int| 0 <= index < position ==> {
                    let edge = #[trigger]
                        self.edges_spec()[old(self).edges_spec().len() + index];
                    edge.parent == parent_indices@[index] && edge.child == child
                },
            decreases parent_indices.len() - position
        {
            self.edges.push(Edge {
                parent: parent_indices[position],
                child,
            });
            position += 1;
        }

        proof {
            Dag::lemma_insert_task_preserves_invariant(
                old(self),
                self,
                parent_indices@,
                child,
            );
        }
        Ok(child)
    }

    /// # Returns
    ///
    /// The number of tasks in the DAG.
    #[must_use]
    pub const fn num_tasks(&self) -> usize {
        self.num_tasks
    }

    /// # Returns
    ///
    /// The DAG's edges.
    #[must_use]
    pub fn edges(&self) -> &[Edge] {
        &self.edges
    }

    /// # Returns
    ///
    /// Whether every edge points from a lower task index to a higher task index.
    #[must_use]
    pub fn is_topologically_ordered(&self) -> bool {
        /*
         * Verus does not support [`Iterator::all`] for this slice iterator.
         *
         * Origin Rust:
         * self.edges.iter().all(|edge| {
         *     let parent_precedes_child = edge.parent < edge.child;
         *     let child_exists = edge.child < self.num_tasks;
         *     parent_precedes_child && child_exists
         * })
         */
        let mut position = 0;
        while position < self.edges.len()
            invariant
                position <= self.edges.len(),
            decreases self.edges.len() - position
        {
            let edge = self.edges[position];
            let parent_does_not_precede_child = edge.parent >= edge.child;
            let child_does_not_exist = edge.child >= self.num_tasks;
            if parent_does_not_precede_child || child_does_not_exist {
                return false;
            }
            position += 1;
        }
        true
    }

    proof fn lemma_insert_task_preserves_invariant(
        old_self: &Dag,
        new_self: &Dag,
        parent_indices: Seq<usize>,
        child: usize,
    )
        requires
            old_self.invariant(),
            child == old_self.num_tasks_spec(),
            new_self.num_tasks_spec() == child + 1,
            new_self.edges_spec().len()
                == old_self.edges_spec().len() + parent_indices.len(),
            new_self.edges_spec().take(old_self.edges_spec().len() as int)
                == old_self.edges_spec(),
            forall|position: int| 0 <= position < parent_indices.len() ==> {
                let edge = #[trigger]
                    new_self.edges_spec()[old_self.edges_spec().len() + position];
                &&& parent_indices[position] < child
                &&& edge.parent == parent_indices[position]
                &&& edge.child == child
            },
            forall|left: int, right: int| 0 <= left < right < parent_indices.len()
                ==> parent_indices[left] != parent_indices[right],
        ensures
            new_self.invariant(),
    {
        reveal(Dag::invariant);
        reveal(Dag::is_topologically_ordered_spec);
        reveal(Dag::has_unique_edges_spec);
        let old_edge_count = old_self.edges_spec().len();

        assert forall|edge_position: int|
            0 <= edge_position < new_self.edges_spec().len()
        implies {
            let edge = #[trigger] new_self.edges_spec()[edge_position];
            edge.parent < edge.child && edge.child < new_self.num_tasks_spec()
        } by {
            if edge_position < old_edge_count {
                assert(new_self.edges_spec()[edge_position]
                    == old_self.edges_spec()[edge_position]);
                assert(old_self.is_topologically_ordered_spec());
                assert(old_self.edges_spec()[edge_position].parent
                    < old_self.edges_spec()[edge_position].child);
                assert(old_self.edges_spec()[edge_position].child
                    < old_self.num_tasks_spec());
                assert(old_self.num_tasks_spec() < new_self.num_tasks_spec());
            } else {
                let parent_position = edge_position - old_edge_count;
                assert(0 <= parent_position < parent_indices.len());
                assert(new_self.edges_spec()[old_edge_count + parent_position].parent
                    == parent_indices[parent_position]);
                assert(new_self.edges_spec()[old_edge_count + parent_position].child
                    == child);
                assert(old_edge_count + parent_position == edge_position);
                assert(new_self.edges_spec()[edge_position].parent
                    == parent_indices[parent_position]);
                assert(new_self.edges_spec()[edge_position].child == child);
                assert(parent_indices[parent_position] < child);
                assert(child < new_self.num_tasks_spec());
            }
        }

        assert forall|left: int, right: int|
            0 <= left < new_self.edges_spec().len()
                && 0 <= right < new_self.edges_spec().len()
                && left != right
        implies {
            let left_edge = #[trigger] new_self.edges_spec()[left];
            let right_edge = #[trigger] new_self.edges_spec()[right];
            left_edge.parent != right_edge.parent || left_edge.child != right_edge.child
        } by {
            if left < old_edge_count && right < old_edge_count {
                assert(new_self.edges_spec()[left] == old_self.edges_spec()[left]);
                assert(new_self.edges_spec()[right] == old_self.edges_spec()[right]);
                assert(old_self.has_unique_edges_spec());
                assert(old_self.edges_spec()[left].parent
                        != old_self.edges_spec()[right].parent
                    || old_self.edges_spec()[left].child
                        != old_self.edges_spec()[right].child);
            } else if left < old_edge_count {
                assert(new_self.edges_spec()[left] == old_self.edges_spec()[left]);
                let parent_position = right - old_edge_count;
                assert(0 <= parent_position < parent_indices.len());
                assert(new_self.edges_spec()[old_edge_count + parent_position].child
                    == child);
                assert(old_edge_count + parent_position == right);
                assert(new_self.edges_spec()[right].child == child);
                assert(old_self.edges_spec()[left].child < old_self.num_tasks_spec());
                assert(old_self.num_tasks_spec() == child);
            } else if right < old_edge_count {
                assert(new_self.edges_spec()[right] == old_self.edges_spec()[right]);
                let parent_position = left - old_edge_count;
                assert(0 <= parent_position < parent_indices.len());
                assert(new_self.edges_spec()[old_edge_count + parent_position].child
                    == child);
                assert(old_edge_count + parent_position == left);
                assert(new_self.edges_spec()[left].child == child);
                assert(old_self.edges_spec()[right].child < old_self.num_tasks_spec());
                assert(old_self.num_tasks_spec() == child);
            } else {
                let left_parent_position = left - old_edge_count;
                let right_parent_position = right - old_edge_count;
                assert(0 <= left_parent_position < parent_indices.len());
                assert(0 <= right_parent_position < parent_indices.len());
                assert(new_self.edges_spec()[old_edge_count + left_parent_position].parent
                    == parent_indices[left_parent_position]);
                assert(new_self.edges_spec()[old_edge_count + right_parent_position].parent
                    == parent_indices[right_parent_position]);
                assert(old_edge_count + left_parent_position == left);
                assert(old_edge_count + right_parent_position == right);
                assert(new_self.edges_spec()[left].parent
                    == parent_indices[left_parent_position]);
                assert(new_self.edges_spec()[right].parent
                    == parent_indices[right_parent_position]);
                if left_parent_position < right_parent_position {
                    assert(parent_indices[left_parent_position]
                        != parent_indices[right_parent_position]);
                } else {
                    assert(right_parent_position < left_parent_position);
                    assert(parent_indices[right_parent_position]
                        != parent_indices[left_parent_position]);
                }
            }
        }

        assert(new_self.invariant());
    }

    proof fn lemma_edge_increases(&self, parent: nat, child: nat)
        requires
            self.invariant(),
            self.has_edge_spec(parent, child),
        ensures
            parent < child,
    {
        reveal(Dag::invariant);
        reveal(Dag::has_edge_spec);
        reveal(Dag::is_topologically_ordered_spec);
        let position = choose|position: int| 0 <= position < self.edges_spec().len() && {
            let edge = #[trigger] self.edges_spec()[position];
            edge.parent == parent && edge.child == child
        };
        assert(0 <= position < self.edges_spec().len());
        assert(self.edges_spec()[position].parent == parent);
        assert(self.edges_spec()[position].child == child);
        assert(self.edges_spec()[position].parent < self.edges_spec()[position].child);
    }

    proof fn lemma_reaches_increases(&self, from: nat, to: nat, fuel: nat)
        requires
            self.invariant(),
            self.reaches_spec(from, to, fuel),
        ensures
            from < to,
        decreases fuel,
    {
        reveal(Dag::reaches_spec);
        if self.has_edge_spec(from, to) {
            self.lemma_edge_increases(from, to);
        } else {
            assert(fuel > 0);
            assert(exists|next: nat|
                self.has_edge_spec(from, next)
                    && self.reaches_spec(next, to, (fuel - 1) as nat));
            let next = choose|next: nat|
                self.has_edge_spec(from, next)
                    && self.reaches_spec(next, to, (fuel - 1) as nat);
            self.lemma_edge_increases(from, next);
            self.lemma_reaches_increases(next, to, (fuel - 1) as nat);
        }
    }
}

/// The result of recording one parent task's successful completion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParentCompletion {
    AlreadyCompleted,
    BecameReady,
    StillPending,
    UnknownParent,
}

/// Tracks which parents of one task have completed successfully.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TaskReadiness {
    parent_indices: Vec<usize>,
    completed: Vec<bool>,
}

impl TaskReadiness {
    /// # Returns
    ///
    /// The mathematical parent task indices.
    pub closed spec fn parent_indices_spec(&self) -> Seq<usize> {
        self.parent_indices@
    }

    /// # Returns
    ///
    /// Whether `parent` is a parent task whose successful completion has been recorded.
    pub closed spec fn has_completed_spec(&self, parent: usize) -> bool {
        exists|position: int|
            0 <= position < self.parent_indices@.len() && #[trigger] self.parent_indices@[position]
                == parent && self.completed@[position]
    }

    /// # Returns
    ///
    /// Whether every parent task's successful completion has been recorded.
    pub closed spec fn is_ready_spec(&self) -> bool {
        forall|parent: usize|
            self.parent_indices@.contains(parent) ==> #[trigger] self.has_completed_spec(parent)
    }

    /// # Returns
    ///
    /// Whether the completion flags match the parent list and agree for repeated parents.
    pub closed spec fn invariant(&self) -> bool {
        &&& self.completed@.len() == self.parent_indices@.len()
        &&& forall|left: int, right: int|
            0 <= left < self.parent_indices@.len() && 0 <= right < self.parent_indices@.len()
                && #[trigger] self.parent_indices@[left] == #[trigger] self.parent_indices@[right]
                ==> self.completed@[left] == self.completed@[right]
    }

    /// Creates readiness state for a task.
    ///
    /// # Returns
    ///
    /// Readiness state with no parent completion recorded.
    #[must_use]
    pub fn new(parent_indices: Vec<usize>) -> (result: Self)
        ensures
            result.invariant(),
            result.parent_indices_spec() == parent_indices@,
            forall|parent: usize| !#[trigger] result.has_completed_spec(parent),
    {
        let mut completed: Vec<bool> = Vec::with_capacity(parent_indices.len());
        while completed.len() < parent_indices.len()
            invariant
                completed@.len() <= parent_indices@.len(),
                forall|position: int|
                    0 <= position < completed@.len() ==> !#[trigger] completed@[position],
            decreases parent_indices.len() - completed.len()
        {
            completed.push(false);
        }
        Self {
            parent_indices,
            completed,
        }
    }

    /// Records the successful completion of the parent task `parent`.
    ///
    /// # Returns
    ///
    /// * [`ParentCompletion::UnknownParent`] if `parent` is not a parent of this task.
    /// * [`ParentCompletion::AlreadyCompleted`] if the completion of `parent` was already recorded.
    /// * [`ParentCompletion::BecameReady`] if `parent` was the last parent without a recorded
    ///   completion.
    /// * [`ParentCompletion::StillPending`] if another parent has no recorded completion.
    pub fn parent_completed(&mut self, parent: usize) -> (result: ParentCompletion)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            final(self).parent_indices_spec() == old(self).parent_indices_spec(),
            forall|other: usize|
                #[trigger] final(self).has_completed_spec(other) <==> old(self).has_completed_spec(other) || (other == parent && old(self).parent_indices_spec().contains(parent)),
            (result == ParentCompletion::UnknownParent) <==> !old(self).parent_indices_spec().contains(parent),
            (result == ParentCompletion::AlreadyCompleted) <==> old(self).has_completed_spec(parent),
            (result == ParentCompletion::BecameReady) <==> !old(self).is_ready_spec() && final(self).is_ready_spec(),
            (result == ParentCompletion::StillPending) <==> old(self).parent_indices_spec().contains(parent) && !old(self).has_completed_spec(parent)
                && !final(self).is_ready_spec(),
    {
        let mut found = false;
        let mut newly_completed = false;
        let ghost mut found_position: int = 0;
        let ghost mut newly_completed_position: int = 0;
        let mut position = 0;
        while position < self.parent_indices.len()
            invariant
                old(self).invariant(),
                self.parent_indices@ == old(self).parent_indices@,
                self.completed@.len() == old(self).completed@.len(),
                position <= self.parent_indices@.len(),
                forall|index: int|
                    0 <= index < position ==> #[trigger] self.completed@[index] == (old(self).completed@[index] || self.parent_indices@[index] == parent),
                forall|index: int|
                    position <= index < self.completed@.len() ==> #[trigger] self.completed@[index]
                        == old(self).completed@[index],
                found ==> 0 <= found_position < position && self.parent_indices@[found_position]
                    == parent,
                !found ==> forall|index: int|
                    0 <= index < position ==> #[trigger] self.parent_indices@[index] != parent,
                newly_completed ==> 0 <= newly_completed_position < position
                    && self.parent_indices@[newly_completed_position] == parent
                    && !old(self).completed@[newly_completed_position],
                !newly_completed ==> forall|index: int|
                    0 <= index < position && #[trigger] self.parent_indices@[index] == parent
                        ==> old(self).completed@[index],
            decreases self.parent_indices.len() - position
        {
            if self.parent_indices[position] == parent {
                found = true;
                proof {
                    found_position = position as int;
                }
                if !self.completed[position] {
                    newly_completed = true;
                    proof {
                        newly_completed_position = position as int;
                    }
                    self.completed[position] = true;
                }
            }
            position += 1;
        }

        proof {
            TaskReadiness::lemma_parent_completed(
                old(self),
                self,
                parent,
                found,
                newly_completed,
                found_position,
                newly_completed_position,
            );
        }

        if !found {
            return ParentCompletion::UnknownParent;
        }
        if !newly_completed {
            return ParentCompletion::AlreadyCompleted;
        }
        if self.is_ready() {
            ParentCompletion::BecameReady
        } else {
            ParentCompletion::StillPending
        }
    }

    /// Clears every recorded parent completion.
    pub fn reset(&mut self)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            final(self).parent_indices_spec() == old(self).parent_indices_spec(),
            forall|parent: usize| !#[trigger] final(self).has_completed_spec(parent),
    {
        let mut position = 0;
        while position < self.completed.len()
            invariant
                self.parent_indices@ == old(self).parent_indices@,
                self.completed@.len() == old(self).completed@.len(),
                old(self).invariant(),
                position <= self.completed@.len(),
                forall|index: int| 0 <= index < position ==> !#[trigger] self.completed@[index],
            decreases self.completed.len() - position
        {
            self.completed[position] = false;
            position += 1;
        }
    }

    /// # Returns
    ///
    /// Whether every parent task has completed successfully.
    #[must_use]
    pub fn is_ready(&self) -> (result: bool)
        requires
            self.invariant(),
        ensures
            result == self.is_ready_spec(),
    {
        let mut position = 0;
        while position < self.completed.len()
            invariant
                self.invariant(),
                position <= self.completed@.len(),
                forall|index: int| 0 <= index < position ==> #[trigger] self.completed@[index],
            decreases self.completed.len() - position
        {
            if !self.completed[position] {
                proof {
                    self.lemma_is_ready_iff_all_completed();
                }
                return false;
            }
            position += 1;
        }
        proof {
            self.lemma_is_ready_iff_all_completed();
        }
        true
    }

    proof fn lemma_is_ready_iff_all_completed(&self)
        requires
            self.invariant(),
        ensures
            self.is_ready_spec() <==> forall|position: int|
                0 <= position < self.completed@.len() ==> #[trigger] self.completed@[position],
    {
        reveal(TaskReadiness::is_ready_spec);
        reveal(TaskReadiness::has_completed_spec);
        if forall|position: int|
            0 <= position < self.completed@.len() ==> #[trigger] self.completed@[position] {
            assert forall|parent: usize| self.parent_indices@.contains(parent) implies #[trigger] self.has_completed_spec(parent) by {
                let position = choose|position: int|
                    0 <= position < self.parent_indices@.len() && self.parent_indices@[position]
                        == parent;
                assert(self.completed@[position]);
            }
        }
        if self.is_ready_spec() {
            assert forall|position: int|
                0 <= position < self.completed@.len() implies #[trigger] self.completed@[position] by {
                let parent = self.parent_indices@[position];
                assert(self.parent_indices@.contains(parent));
                assert(self.has_completed_spec(parent));
                let witness = choose|witness: int|
                    0 <= witness < self.parent_indices@.len() && #[trigger] self.parent_indices@[witness]
                        == parent && self.completed@[witness];
                assert(self.completed@[witness] == self.completed@[position]);
            }
        }
    }

    proof fn lemma_parent_completed(
        old_self: &TaskReadiness,
        new_self: &TaskReadiness,
        parent: usize,
        found: bool,
        newly_completed: bool,
        found_position: int,
        newly_completed_position: int,
    )
        requires
            old_self.invariant(),
            new_self.parent_indices@ == old_self.parent_indices@,
            new_self.completed@.len() == old_self.completed@.len(),
            forall|index: int|
                0 <= index < new_self.completed@.len() ==> #[trigger] new_self.completed@[index] == (old_self.completed@[index] || new_self.parent_indices@[index] == parent),
            found ==> 0 <= found_position < new_self.parent_indices@.len()
                && new_self.parent_indices@[found_position] == parent,
            !found ==> forall|index: int|
                0 <= index < new_self.parent_indices@.len() ==> #[trigger] new_self.parent_indices@[index] != parent,
            newly_completed ==> 0 <= newly_completed_position < new_self.parent_indices@.len()
                && new_self.parent_indices@[newly_completed_position] == parent
                && !old_self.completed@[newly_completed_position],
            !newly_completed ==> forall|index: int|
                0 <= index < new_self.parent_indices@.len() && #[trigger] new_self.parent_indices@[index] == parent
                    ==> old_self.completed@[index],
        ensures
            new_self.invariant(),
            found == old_self.parent_indices@.contains(parent),
            old_self.has_completed_spec(parent) == (found && !newly_completed),
            forall|other: usize| #[trigger] new_self.has_completed_spec(other) <==> (old_self.has_completed_spec(other) || (other == parent && found)),
            !newly_completed && new_self.is_ready_spec() ==> old_self.is_ready_spec(),
            newly_completed ==> !old_self.is_ready_spec(),
    {
        assert forall|left: int, right: int|
            0 <= left < new_self.parent_indices@.len() && 0 <= right < new_self.parent_indices@.len()
                && #[trigger] new_self.parent_indices@[left] == #[trigger] new_self.parent_indices@[right]
        implies new_self.completed@[left] == new_self.completed@[right] by {
            assert(old_self.completed@[left] == old_self.completed@[right]);
        }
        assert(found == old_self.parent_indices@.contains(parent)) by {
            if found {
                assert(old_self.parent_indices@[found_position] == parent);
            }
        }
        if old_self.has_completed_spec(parent) {
            let witness = choose|witness: int|
                0 <= witness < old_self.parent_indices@.len()
                    && #[trigger] old_self.parent_indices@[witness] == parent
                    && old_self.completed@[witness];
            assert(new_self.parent_indices@[witness] == parent);
            if newly_completed {
                assert(old_self.completed@[witness]
                    == old_self.completed@[newly_completed_position]);
            }
        }
        if found && !newly_completed {
            assert(old_self.completed@[found_position]);
            assert(old_self.parent_indices@[found_position] == parent);
        }
        assert forall|other: usize| #[trigger] new_self.has_completed_spec(other) <==> (old_self.has_completed_spec(other) || (other == parent && found)) by {
            if new_self.has_completed_spec(other) {
                let witness = choose|witness: int|
                    0 <= witness < new_self.parent_indices@.len()
                        && #[trigger] new_self.parent_indices@[witness] == other
                        && new_self.completed@[witness];
                assert(old_self.parent_indices@[witness] == other);
            }
            if old_self.has_completed_spec(other) {
                let witness = choose|witness: int|
                    0 <= witness < old_self.parent_indices@.len()
                        && #[trigger] old_self.parent_indices@[witness] == other
                        && old_self.completed@[witness];
                assert(new_self.completed@[witness]);
                assert(new_self.parent_indices@[witness] == other);
            }
            if other == parent && found {
                assert(new_self.completed@[found_position]);
                assert(new_self.parent_indices@[found_position] == other);
            }
        }
        if !newly_completed && new_self.is_ready_spec() {
            assert forall|other: usize| old_self.parent_indices@.contains(other) implies #[trigger] old_self.has_completed_spec(other) by {
                assert(new_self.parent_indices@.contains(other));
                assert(new_self.has_completed_spec(other));
            }
        }
        if newly_completed {
            assert(old_self.parent_indices@[newly_completed_position] == parent);
            assert(old_self.parent_indices@.contains(parent));
            assert(!old_self.has_completed_spec(parent));
        }
    }
}

} // verus!

#[cfg(test)]
mod tests {
    use super::*;

    /// Inserts a task and converts [`DagError`] into an [`anyhow::Error`].
    ///
    /// # Returns
    ///
    /// The inserted task index on success.
    ///
    /// # Errors
    ///
    /// Returns an error if [`Dag::insert_task`] rejects the parent indices.
    fn insert_task(dag: &mut Dag, parent_indices: &[usize]) -> anyhow::Result<usize> {
        dag.insert_task(parent_indices)
            .map_err(|error| anyhow::anyhow!("{error:?}"))
    }

    #[test]
    fn inserts_diamond_dag() -> anyhow::Result<()> {
        let mut dag = Dag::new();
        assert_eq!(insert_task(&mut dag, &[])?, 0);
        assert_eq!(insert_task(&mut dag, &[0])?, 1);
        assert_eq!(insert_task(&mut dag, &[0])?, 2);
        assert_eq!(insert_task(&mut dag, &[1, 2])?, 3);

        assert_eq!(dag.num_tasks(), 4);
        assert_eq!(
            dag.edges(),
            &[
                Edge {
                    parent: 0,
                    child: 1,
                },
                Edge {
                    parent: 0,
                    child: 2,
                },
                Edge {
                    parent: 1,
                    child: 3,
                },
                Edge {
                    parent: 2,
                    child: 3,
                },
            ]
        );
        assert!(dag.is_topologically_ordered());
        Ok(())
    }

    #[test]
    fn rejects_invalid_parents_without_mutation() -> anyhow::Result<()> {
        let mut dag = Dag::new();
        insert_task(&mut dag, &[])?;
        let original = dag.clone();

        assert_eq!(
            dag.insert_task(&[1]),
            Err(DagError::ParentOutOfRange {
                parent: 1,
                child: 1,
            })
        );
        assert_eq!(dag, original);
        assert_eq!(
            dag.insert_task(&[0, 0]),
            Err(DagError::DuplicateParent { parent: 0 })
        );
        assert_eq!(dag, original);
        Ok(())
    }

    #[test]
    fn exhaustively_accepts_topologically_ordered_dags() -> anyhow::Result<()> {
        for num_tasks in 0_usize..=5 {
            let num_possible_edges = num_tasks * num_tasks.saturating_sub(1) / 2;
            for edge_mask in 0_usize..(1_usize << num_possible_edges) {
                let mut dag = Dag::new();
                let mut edge_position = 0;
                for child in 0..num_tasks {
                    let mut parents = Vec::new();
                    for parent in 0..child {
                        if edge_mask & (1_usize << edge_position) != 0 {
                            parents.push(parent);
                        }
                        edge_position += 1;
                    }
                    assert_eq!(insert_task(&mut dag, &parents)?, child);
                }
                assert_eq!(dag.num_tasks(), num_tasks);
                assert!(dag.is_topologically_ordered());
            }
        }
        Ok(())
    }

    /// # Returns
    ///
    /// Every sequence of length at most `max_len` whose elements are below `num_values`.
    fn all_sequences(num_values: usize, max_len: usize) -> Vec<Vec<usize>> {
        let mut sequences = vec![Vec::new()];
        let mut previous_level = vec![Vec::new()];
        for _ in 0..max_len {
            let mut level = Vec::new();
            for prefix in &previous_level {
                for value in 0..num_values {
                    let mut sequence = prefix.clone();
                    sequence.push(value);
                    level.push(sequence);
                }
            }
            sequences.extend(level.iter().cloned());
            previous_level = level;
        }
        sequences
    }

    #[test]
    fn becomes_ready_after_every_distinct_parent() {
        let mut readiness = TaskReadiness::new(vec![4, 7, 9]);
        assert!(!readiness.is_ready());
        assert_eq!(
            readiness.parent_completed(7),
            ParentCompletion::StillPending
        );
        assert_eq!(
            readiness.parent_completed(7),
            ParentCompletion::AlreadyCompleted
        );
        assert!(!readiness.is_ready());
        assert_eq!(
            readiness.parent_completed(4),
            ParentCompletion::StillPending
        );
        assert_eq!(readiness.parent_completed(9), ParentCompletion::BecameReady);
        assert!(readiness.is_ready());
        assert_eq!(
            readiness.parent_completed(4),
            ParentCompletion::AlreadyCompleted
        );
        assert_eq!(
            readiness.parent_completed(5),
            ParentCompletion::UnknownParent
        );
    }

    #[test]
    fn reset_restores_initial_readiness() {
        let mut input_task = TaskReadiness::new(Vec::new());
        assert!(input_task.is_ready());
        assert_eq!(
            input_task.parent_completed(0),
            ParentCompletion::UnknownParent
        );
        input_task.reset();
        assert!(input_task.is_ready());

        let mut dependent_task = TaskReadiness::new(vec![0, 1]);
        assert_eq!(
            dependent_task.parent_completed(0),
            ParentCompletion::StillPending
        );
        dependent_task.reset();
        assert!(!dependent_task.is_ready());
        assert_eq!(
            dependent_task.parent_completed(0),
            ParentCompletion::StillPending
        );
    }

    #[test]
    fn exhaustively_matches_parent_set_model() {
        const NUM_TASKS: usize = 4;
        for parents in all_sequences(NUM_TASKS - 1, 3) {
            for completions in all_sequences(NUM_TASKS, 4) {
                let mut readiness = TaskReadiness::new(parents.clone());
                let mut completed = std::collections::BTreeSet::new();
                for &parent in &completions {
                    let expected = if !parents.contains(&parent) {
                        ParentCompletion::UnknownParent
                    } else if !completed.insert(parent) {
                        ParentCompletion::AlreadyCompleted
                    } else if parents.iter().all(|parent| completed.contains(parent)) {
                        ParentCompletion::BecameReady
                    } else {
                        ParentCompletion::StillPending
                    };
                    assert_eq!(
                        readiness.parent_completed(parent),
                        expected,
                        "parents {parents:?}, completions {completions:?}"
                    );
                    assert_eq!(
                        readiness.is_ready(),
                        parents.iter().all(|parent| completed.contains(parent)),
                        "parents {parents:?}, completions {completions:?}"
                    );
                }
            }
        }
    }
}
