//! Verify from the repository root with `python3 verification/verify_job_counters.py`.
//! The driver builds the handler module from Spider's Rust sources.
use vstd::prelude::*;
use vstd::set_lib::{lemma_len_subset, lemma_set_disjoint_lens, lemma_set_subset_finite};

mod handler;

verus! {

type Task = nat;
type Reporter = nat;

// One running job's regular graph. Commit and cleanup have separate handlers.
struct Job {
    children: Map<Task, Seq<Task>>,
    predecessors: Map<Task, Set<Task>>,
}

impl Job {
    spec fn tasks(self) -> Set<Task> { self.children.dom() }

    spec fn well_formed(self) -> bool {
        &&& self.tasks().finite()
        &&& self.tasks().len() <= usize::MAX
        &&& self.predecessors.dom() == self.tasks()
        &&& forall|c| self.tasks().contains(c) ==>
            (#[trigger] self.predecessors[c]).subset_of(self.tasks())
        &&& forall|p| self.tasks().contains(p) ==> #[trigger] self.children[p].no_duplicates()
        &&& forall|p, c| self.tasks().contains(p) ==>
            (#[trigger] self.children[p].contains(c) <==>
                self.tasks().contains(c) && self.predecessors[c].contains(p))
    }
}

// Cursor -1 is before the task's success flip. Cursors 0..len are the number
// of child decrements applied. len+1 is after the job's atomic decrement.
struct Call {
    cursor: int,
    reporter: Reporter,
    stopped: bool,
}

struct State {
    succeeded: Set<Task>,
    calls: Map<Task, Call>,
    job_left: int,
    parents_left: Map<Task, int>,
    zero_observers: Seq<Reporter>,
}

spec fn initial(g: Job) -> State {
    State {
        succeeded: Set::empty(),
        calls: g.tasks().mk_map(|_task| Call { cursor: -1, reporter: 0, stopped: false }),
        job_left: g.tasks().len() as int,
        parents_left: g.tasks().mk_map(|c| g.predecessors[c].len() as int),
        zero_observers: Seq::empty(),
    }
}

spec fn uncharged(g: Job, s: State) -> Set<Task> {
    g.tasks().filter(|p| s.calls[p].cursor <= g.children[p].len())
}

spec fn unnotified(g: Job, s: State, child: Task) -> Set<Task> {
    g.predecessors[child].filter(|p| s.calls[p].cursor <= g.children[p].index_of(child))
}

spec fn drained(g: Job, s: State) -> bool {
    forall|p| g.tasks().contains(p) ==>
        (#[trigger] s.calls[p].cursor < 0 || s.calls[p].cursor > g.children[p].len())
}

spec fn accounting(g: Job, s: State) -> bool {
    &&& s.calls.dom() == g.tasks()
    &&& s.parents_left.dom() == g.tasks()
    &&& s.succeeded.subset_of(g.tasks())
    &&& forall|p| g.tasks().contains(p) ==>
        -1 <= #[trigger] s.calls[p].cursor <= g.children[p].len() + 1
    &&& forall|p| g.tasks().contains(p) ==>
        (s.succeeded.contains(p) <==> #[trigger] s.calls[p].cursor >= 0)
    &&& s.job_left == uncharged(g, s).len()
    &&& forall|c| g.tasks().contains(c) ==>
        #[trigger] s.parents_left[c] == unnotified(g, s, c).len()
    &&& s.zero_observers.len() == (if g.tasks().len() > 0 && s.job_left == 0 { 1int } else { 0int })
}

enum Event {
    Attempt(Task, Reporter, bool),
    Resume(Task, Reporter),
    Abandon(Task, Reporter),
    Idle,
}

enum Effect {
    Flip(Task, Reporter),
    Child(Task, Task),
    Job(Task),
    Stop(Task),
    Idle,
}

// Project execution at the handler's three mutation sites. A rejected attempt,
// an await or a stop performs no accounting. Dropping a partial report can
// leave its cursor parked indefinitely. Finishing the updates is a condition.
spec fn dispatch(g: Job, s: State, event: Event) -> Effect {
    match event {
        Event::Attempt(t, r, eligible) =>
            if g.tasks().contains(t) { handler::attempt(t, r, s.succeeded.contains(t), eligible) }
            else { Effect::Idle },
        Event::Resume(t, r) => {
            if g.tasks().contains(t) && s.calls[t].reporter == r && !s.calls[t].stopped {
                handler::next_update(t, g.children[t], s.calls[t].cursor)
            } else { Effect::Idle }
        },
        Event::Abandon(t, r) => {
            if g.tasks().contains(t) && s.calls[t].reporter == r
                && 0 <= s.calls[t].cursor <= g.children[t].len() {
                Effect::Stop(t)
            } else { Effect::Idle }
        },
        Event::Idle => Effect::Idle,
    }
}

spec fn advance(s: State, t: Task) -> Map<Task, Call> {
    s.calls.insert(t, Call { cursor: s.calls[t].cursor + 1, ..s.calls[t] })
}

spec fn step(g: Job, s: State, event: Event) -> State {
    match dispatch(g, s, event) {
        Effect::Idle => s,
        Effect::Stop(t) => State {
            calls: s.calls.insert(t, Call { stopped: true, ..s.calls[t] }), ..s
        },
        Effect::Flip(t, reporter) => State {
            succeeded: s.succeeded.insert(t),
            calls: s.calls.insert(t, Call { cursor: 0, reporter, stopped: false }),
            ..s
        },
        Effect::Child(t, child) => State {
            calls: advance(s, t),
            parents_left: s.parents_left.insert(child, handler::parent_after(s.parents_left[child])),
            ..s
        },
        Effect::Job(t) => State {
            calls: advance(s, t),
            job_left: handler::job_after(s.job_left),
            zero_observers: if handler::observed(s.job_left) == 0 {
                s.zero_observers.push(s.calls[t].reporter)
            } else { s.zero_observers },
            ..s
        },
    }
}

proof fn edge_position(g: Job, p: Task, c: Task)
    requires g.well_formed(), g.tasks().contains(c), g.predecessors[c].contains(p),
    ensures ({
        let children = g.children[p];
        let i = children.index_of(c);
        &&& g.tasks().contains(p)
        &&& 0 <= i < children.len()
        &&& children[i] == c
        &&& forall|j: int| 0 <= j < children.len() ==> (#[trigger] children[j] == c <==> j == i)
    }),
{
    assert(g.predecessors[c].subset_of(g.tasks()));
    assert(g.tasks().contains(p));
    let children = g.children[p];
    assert(children.contains(c));
    assert(children[children.index_of(c)] == c);
    assert(children.no_duplicates());
}

proof fn initial_accounting(g: Job)
    requires g.well_formed(),
    ensures accounting(g, initial(g)),
{
    let s = initial(g);
    assert(uncharged(g, s) =~= g.tasks());
    assert forall|c| g.tasks().contains(c) implies
        #[trigger] s.parents_left[c] == unnotified(g, s, c).len() by {
        assert forall|p| g.predecessors[c].contains(p) implies unnotified(g, s, c).contains(p) by {
            edge_position(g, p, c);
        }
        assert(unnotified(g, s, c) =~= g.predecessors[c]);
    }
}

// Every decrement is licensed by one distinct element of a finite set. This
// bounds the previous value and excludes both checked and wrapping underflow.
proof fn debit(g: Job, pending: Set<Task>, p: Task)
    requires g.well_formed(), pending.subset_of(g.tasks()), pending.contains(p),
    ensures 0 < pending.len() <= usize::MAX, pending.remove(p).len() + 1 == pending.len(),
{
    lemma_set_subset_finite(g.tasks(), pending);
    lemma_len_subset(pending, g.tasks());
    vstd::set::axiom_set_remove_len(pending, p);
}

proof fn step_accounting(g: Job, s: State, e: Event)
    requires g.well_formed(), accounting(g, s),
    ensures accounting(g, step(g, s, e)),
        match dispatch(g, s, e) {
            Effect::Child(_, c) => 0 < s.parents_left[c] <= usize::MAX,
            Effect::Job(p) => {
                let n = step(g, s, e);
                &&& 0 < s.job_left <= usize::MAX
                &&& handler::observed(s.job_left) == n.job_left
                &&& (handler::observed(s.job_left) == 0 <==> s.job_left == 1)
                &&& n.zero_observers == (if s.job_left == 1 {
                    s.zero_observers.push(s.calls[p].reporter)
                } else { s.zero_observers })
            },
            _ => true,
        },
{
    let n = step(g, s, e);
    match dispatch(g, s, e) {
        Effect::Idle => {},
        Effect::Stop(_) => {
            assert(uncharged(g, n) =~= uncharged(g, s));
            assert forall|c| g.tasks().contains(c) implies
                #[trigger] n.parents_left[c] == unnotified(g, n, c).len() by {
                assert(unnotified(g, n, c) =~= unnotified(g, s, c));
            }
        },
        Effect::Flip(p, _) => {
            assert(s.calls[p].cursor == -1);
            assert(n.calls.dom() =~= g.tasks());
            assert(uncharged(g, n) =~= uncharged(g, s));
            assert forall|c| g.tasks().contains(c) implies
                #[trigger] n.parents_left[c] == unnotified(g, n, c).len() by {
                if g.predecessors[c].contains(p) { edge_position(g, p, c); }
                assert(unnotified(g, n, c) =~= unnotified(g, s, c));
            }
        },
        Effect::Child(p, child) => {
            assert(g.children[p].contains(child));
            edge_position(g, p, child);
            let pending = unnotified(g, s, child);
            assert(pending.contains(p));
            assert(g.predecessors[child].subset_of(g.tasks()));
            debit(g, pending, p);
            assert(uncharged(g, n) =~= uncharged(g, s));
            assert forall|c| g.tasks().contains(c) implies
                #[trigger] n.parents_left[c] == unnotified(g, n, c).len() by {
                if g.predecessors[c].contains(p) { edge_position(g, p, c); }
                if c == child {
                    assert(unnotified(g, n, c) =~= pending.remove(p));
                } else {
                    assert(unnotified(g, n, c) =~= unnotified(g, s, c));
                }
            }
        },
        Effect::Job(p) => {
            let pending = uncharged(g, s);
            assert(pending.contains(p));
            debit(g, pending, p);
            assert(uncharged(g, n) =~= pending.remove(p));
            assert forall|c| g.tasks().contains(c) implies
                #[trigger] n.parents_left[c] == unnotified(g, n, c).len() by {
                if g.predecessors[c].contains(p) { edge_position(g, p, c); }
                assert(unnotified(g, n, c) =~= unnotified(g, s, c));
            }
        },
    }
    assert(n.calls.dom() =~= g.tasks());
    assert(n.parents_left.dom() =~= g.tasks());
    assert(n.succeeded.subset_of(g.tasks()));
    assert forall|t| g.tasks().contains(t) implies
        -1 <= #[trigger] n.calls[t].cursor <= g.children[t].len() + 1 by {
        assert(-1 <= s.calls[t].cursor <= g.children[t].len() + 1);
    }
    assert forall|t| g.tasks().contains(t) implies
        (n.succeeded.contains(t) <==> #[trigger] n.calls[t].cursor >= 0) by {
        assert(s.succeeded.contains(t) <==> s.calls[t].cursor >= 0);
    }
}

spec fn run(g: Job, trace: Seq<Event>) -> State
    decreases trace.len(),
{
    if trace.len() == 0 { initial(g) }
    else { step(g, run(g, trace.drop_last()), trace.last()) }
}

proof fn every_interleaving(g: Job, trace: Seq<Event>)
    requires g.well_formed(),
    ensures accounting(g, run(g, trace)),
    decreases trace.len(),
{
    if trace.len() == 0 { initial_accounting(g); }
    else {
        every_interleaving(g, trace.drop_last());
        step_accounting(g, run(g, trace.drop_last()), trace.last());
    }
}

// Each stored count partitions into tasks yet to succeed and successes whose
// corresponding decrement has not run. The latter may include an abandoned call.
proof fn split_pending(group: Set<Task>, pending: Set<Task>, succeeded: Set<Task>)
    requires group.finite(), pending.subset_of(group), group.difference(succeeded).subset_of(pending),
    ensures pending.len() == group.difference(succeeded).len() + pending.intersect(succeeded).len(),
{
    let waiting = group.difference(succeeded);
    let owed = pending.intersect(succeeded);
    lemma_set_subset_finite(group, pending);
    assert(waiting.disjoint(owed));
    assert(waiting.union(owed) =~= pending);
    lemma_set_disjoint_lens(waiting, owed);
}

proof fn in_flight_counters(g: Job, trace: Seq<Event>)
    requires g.well_formed(),
    ensures ({
        let s = run(g, trace);
        &&& s.job_left == g.tasks().difference(s.succeeded).len()
            + uncharged(g, s).intersect(s.succeeded).len()
        &&& forall|c| g.tasks().contains(c) ==> #[trigger] s.parents_left[c] ==
            g.predecessors[c].difference(s.succeeded).len()
                + unnotified(g, s, c).intersect(s.succeeded).len()
    }),
{
    every_interleaving(g, trace);
    let s = run(g, trace);
    assert forall|p| g.tasks().difference(s.succeeded).contains(p)
        implies #[trigger] uncharged(g, s).contains(p) by { assert(s.calls[p].cursor == -1); }
    split_pending(g.tasks(), uncharged(g, s), s.succeeded);
    assert forall|c| g.tasks().contains(c) implies #[trigger] s.parents_left[c] ==
        g.predecessors[c].difference(s.succeeded).len()
            + unnotified(g, s, c).intersect(s.succeeded).len() by {
        lemma_set_subset_finite(g.tasks(), g.predecessors[c]);
        assert forall|p| g.predecessors[c].difference(s.succeeded).contains(p)
            implies #[trigger] unnotified(g, s, c).contains(p) by {
            edge_position(g, p, c);
            assert(s.calls[p].cursor == -1);
        }
        split_pending(g.predecessors[c], unnotified(g, s, c), s.succeeded);
    }
}

proof fn counters_and_unique_reporter(g: Job, trace: Seq<Event>)
    requires g.well_formed(),
    ensures ({
        let s = run(g, trace);
        &&& s.zero_observers.len() <= 1
        &&& (s.job_left == 0 <==> drained(g, s) && s.succeeded == g.tasks())
        &&& drained(g, s) ==> s.job_left == g.tasks().difference(s.succeeded).len()
        &&& forall|c| drained(g, s) && g.tasks().contains(c) ==>
            #[trigger] s.parents_left[c] == g.predecessors[c].difference(s.succeeded).len()
        &&& s.zero_observers.len() == (if g.tasks().len() > 0
            && drained(g, s) && s.succeeded == g.tasks() { 1int } else { 0int })
    }),
{
    every_interleaving(g, trace);
    let s = run(g, trace);
    let pending = uncharged(g, s);
    if s.job_left == 0 {
        lemma_set_subset_finite(g.tasks(), pending);
        pending.lemma_len0_is_empty();
        assert forall|p| g.tasks().contains(p) implies
            #[trigger] s.calls[p].cursor > g.children[p].len() by {
            assert(!pending.contains(p));
        }
        assert forall|p| g.tasks().contains(p) implies #[trigger] s.succeeded.contains(p) by {
            assert(s.calls[p].cursor > g.children[p].len());
        }
        assert(s.succeeded =~= g.tasks());
    }
    if drained(g, s) {
        assert(pending =~= g.tasks().difference(s.succeeded));
        if s.succeeded == g.tasks() { assert(pending =~= Set::empty()); }
        assert forall|c| g.tasks().contains(c) implies
            #[trigger] s.parents_left[c] == g.predecessors[c].difference(s.succeeded).len() by {
            assert forall|p| #[trigger] g.predecessors[c].contains(p) implies
                (unnotified(g, s, c).contains(p) <==> !s.succeeded.contains(p)) by {
                edge_position(g, p, c);
            }
            assert(unnotified(g, s, c) =~= g.predecessors[c].difference(s.succeeded));
        }
    }
}

// A reachable witness for both sides of the crash window. A recovery that
// rebuilds a Running job creates a new initial counter for the same graph.
proof fn one_task_crash_window(t: Task, first: Reporter, retry: Reporter)
{
    let g = Job { children: map![t => Seq::empty()], predecessors: map![t => Set::empty()] };
    assert(g.tasks() =~= set![t]);
    assert(g.well_formed());
    let start = initial(g);
    assert(start.job_left == 1);
    let accepted = step(g, start, Event::Attempt(t, first, true));
    assert(accepted.succeeded.contains(t) && accepted.job_left == 1);
    let parked = step(g, accepted, Event::Abandon(t, first));
    assert(parked.calls[t].cursor == 0);
    assert(!drained(g, parked));
    assert(step(g, parked, Event::Resume(t, first)) == parked);
    assert(step(g, parked, Event::Attempt(t, retry, true)) == parked);

    let finished = step(g, accepted, Event::Resume(t, first));
    assert(finished.job_left == 0 && finished.zero_observers =~= seq![first]);
    let recovered = step(g, initial(g), Event::Attempt(t, retry, true));
    let finished_again = step(g, recovered, Event::Resume(t, retry));
    assert(finished_again.job_left == 0 && finished_again.zero_observers =~= seq![retry]);
}

} // verus!
