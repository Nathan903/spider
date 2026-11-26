//! Standalone Verus model of one fixed job graph. A report is one atomic step.
//! Success is permanent. A zero observation is the return value of the report
//! that performs the final decrement. Later reads of a zero counter are separate.
//! From the repository root:
//! `verus --no-cheating --crate-type=lib --out-dir /tmp verification/job_counters.rs`

use vstd::prelude::*;
use vstd::set_lib::lemma_set_subset_finite;

verus! {

type TaskId = nat;
type ReporterId = nat;

struct Job {
    regular: Set<TaskId>,
    predecessors: Map<TaskId, Set<TaskId>>,
}

impl Job {
    spec fn well_formed(self) -> bool {
        let tasks = self.predecessors.dom();
        &&& tasks.finite()
        &&& self.regular.subset_of(tasks)
        &&& forall|t| tasks.contains(t) ==> #[trigger] self.predecessors[t].subset_of(tasks)
    }
}

struct State {
    succeeded: Set<TaskId>,
    unfinished: int,
    unfinished_parents: Map<TaskId, int>,
}

spec fn initial(job: Job) -> State {
    State {
        succeeded: Set::empty(),
        unfinished: job.regular.len() as int,
        unfinished_parents: job.predecessors.dom().mk_map(
            |t| job.predecessors[t].len() as int),
    }
}

spec fn counters_match(job: Job, s: State) -> bool {
    &&& s.unfinished == job.regular.difference(s.succeeded).len()
    &&& s.unfinished_parents.dom() == job.predecessors.dom()
    &&& forall|t| job.predecessors.dom().contains(t) ==>
        #[trigger] s.unfinished_parents[t] == job.predecessors[t].difference(s.succeeded).len()
}

struct Report {
    reporter: ReporterId,
    task: TaskId,
    success: bool,
}

// Return the updated counters and the reporting caller's completion flag.
spec fn report(job: Job, s: State, r: Report) -> (State, bool) {
    if !r.success || !job.predecessors.dom().contains(r.task) || s.succeeded.contains(r.task) {
        (s, false)
    } else {
        let regular = job.regular.contains(r.task);
        (State {
            succeeded: s.succeeded.insert(r.task),
            unfinished: s.unfinished - (if regular { 1int } else { 0int }),
            unfinished_parents: job.predecessors.dom().mk_map(|child|
                s.unfinished_parents[child] -
                    (if job.predecessors[child].contains(r.task) { 1int } else { 0int })),
        }, regular && s.unfinished == 1)
    }
}

proof fn initial_counters_match(job: Job)
    ensures counters_match(job, initial(job)),
{
    assert(job.regular.difference(Set::empty()) =~= job.regular);
    assert forall|t| job.predecessors.dom().contains(t) implies
        #[trigger] initial(job).unfinished_parents[t] ==
            job.predecessors[t].difference(Set::empty()).len() by {
        assert(job.predecessors[t].difference(Set::empty()) =~= job.predecessors[t]);
    }
}

// The same cardinality argument applies to the job's regular tasks and to
// each child's predecessor set, including children with multiple parents.
proof fn one_success(group: Set<TaskId>, succeeded: Set<TaskId>, task: TaskId)
    requires group.finite(), !succeeded.contains(task),
    ensures
        group.difference(succeeded.insert(task)).len() ==
            group.difference(succeeded).len() - (if group.contains(task) { 1int } else { 0int }),
{
    let pending = group.difference(succeeded);
    assert(group.difference(succeeded.insert(task)) =~= pending.remove(task));
    vstd::set::axiom_set_remove_len(pending, task);
}

proof fn report_preserves_counters(job: Job, s: State, r: Report)
    requires job.well_formed(), counters_match(job, s),
    ensures ({
        let (next, saw_zero) = report(job, s, r);
        &&& counters_match(job, next)
        &&& next.unfinished <= s.unfinished
        &&& saw_zero == (s.unfinished > 0 && next.unfinished == 0)
    }),
{
    if r.success && job.predecessors.dom().contains(r.task) && !s.succeeded.contains(r.task) {
        lemma_set_subset_finite(job.predecessors.dom(), job.regular);
        one_success(job.regular, s.succeeded, r.task);
        let next = report(job, s, r).0;
        assert forall|t| job.predecessors.dom().contains(t) implies
            #[trigger] next.unfinished_parents[t] ==
                job.predecessors[t].difference(next.succeeded).len() by {
            lemma_set_subset_finite(job.predecessors.dom(), job.predecessors[t]);
            one_success(job.predecessors[t], s.succeeded, r.task);
        }
    }
}

// Record one reporter ID per true return. A sequence counts two calls by the
// same reporter twice, so deduplicating caller IDs cannot hide a second win.
spec fn run(job: Job, reports: Seq<Report>) -> (State, Seq<ReporterId>)
    decreases reports.len(),
{
    if reports.len() == 0 {
        (initial(job), Seq::empty())
    } else {
        let (s, winners) = run(job, reports.drop_last());
        let r = reports.last();
        let (next, saw_zero) = report(job, s, r);
        (next, if saw_zero { winners.push(r.reporter) } else { winners })
    }
}

/// For every finite prefix, count all zero observations from the actual
/// return flags. Exactly one has occurred iff a nonempty regular set finished.
proof fn counters_and_unique_reporter(job: Job, reports: Seq<Report>)
    requires job.well_formed(),
    ensures ({
        let (s, winners) = run(job, reports);
        &&& counters_match(job, s)
        &&& (s.unfinished == 0 <==> job.regular.subset_of(s.succeeded))
        &&& winners.len() == (if job.regular.len() > 0 && s.unfinished == 0 { 1int } else { 0int })
    }),
    decreases reports.len(),
{
    lemma_set_subset_finite(job.predecessors.dom(), job.regular);
    if reports.len() == 0 {
        initial_counters_match(job);
    } else {
        let prefix = reports.drop_last();
        let (s, _) = run(job, prefix);
        counters_and_unique_reporter(job, prefix);
        report_preserves_counters(job, s, reports.last());
        if job.regular.len() == 0 {
            job.regular.lemma_len0_is_empty();
            assert(job.regular.difference(s.succeeded) =~= Set::empty());
        }
    }
    let s = run(job, reports).0;
    let pending = job.regular.difference(s.succeeded);
    if pending.len() == 0 {
        pending.lemma_len0_is_empty();
        assert forall|t| job.regular.contains(t) implies s.succeeded.contains(t) by {
            assert(!pending.contains(t));
        }
    }
    if job.regular.subset_of(s.succeeded) {
        assert(pending =~= Set::empty());
    }
}

} // verus!
