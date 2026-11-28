//! Formal Verification of Spider Job Cache Contract Invariant C6 (Section 7.2) in Verus.
//!
//! Target specification (Spider development doc, Section 7.2 Invariants C1-C15 & Section 8.5):
//!
//!   C6: Task state machine, and one success per task.
//!       `Pending -> Ready -> Running -> Succeeded`, `Failed` or `Cancelled`,
//!       with `Running -> Ready` on a retry (and on dead-EM force-removal of the last
//!       live instance, per Section 8.5). A terminal task accepts no new instance,
//!       and an unknown instance is rejected.
//!
//! Verified against Spider's actual Rust implementation in:
//!   - `components/spider-core/src/task/mod.rs` (`TaskState`, `TaskState::is_terminal`)
//!   - `components/spider-storage/src/cache/error.rs` (`CacheError`, `StaleStateError`, `InternalError`)
//!   - `components/spider-storage/src/cache/task.rs` (`InstancePool`, `RetryCounter`,
//!     `TaskControlBlockBase`, `SharedTaskControlBlock`, `SharedTerminationTaskControlBlock`,
//!     `TaskGraph`)
//!   - `components/spider-storage/src/task_instance_pool.rs` (dead-EM `force_remove_task_instance`
//!     and monotonic `TaskInstanceId` allocation)
//!
//! Structure of this verification file:
//!   1. Core types (`TaskState`, error enums) and the formal C6 transition relation
//!      `valid_task_transition`, with proofs that terminal states are absorbing and
//!      all illegal transitions are excluded.
//!   2. Faithful executable Verus verification of `InstancePool`, `RetryCounter`,
//!      `TaskControlBlockBase`, and regular-task output-count precheck, matching
//!      `cache/task.rs` check-for-check and proving:
//!        - Inductive invariant preservation (including pool/state coupling and bounds)
//!        - C6 valid edge transitions on every operation
//!        - Terminal permanence & rejection of new instances on terminal tasks
//!        - Rejection of unknown / duplicate / straggler instances
//!        - One success per task (`success_count <= 1`, `state == Succeeded <==> success_count == 1`)
//!        - Unreachability of `InternalError::TaskNotRunning`
//!   3. Verified race & straggler scenario lemmas matching Section 8.8(a) and `cache/task.rs` tests.
//!   4. Full multi-task DAG & concurrent interleaving transition system (`TaskGraph` with regular
//!      tasks, commit task, and cleanup task), proving C6 inductively over arbitrary finite traces
//!      of operations, including proving `Pending -> Ready` via parent-counter tracking and
//!      uniqueness of accepted success steps per task.

use std::collections::HashSet;
use vstd::prelude::*;
use vstd::std_specs::hash::obeys_key_model;

verus! {

broadcast use {
    vstd::seq::group_seq_axioms,
    vstd::set::group_set_axioms,
    vstd::std_specs::hash::group_hash_axioms,
};

// ============================================================================
// Section 1: Core Types & Formal C6 Transition Relation
// ============================================================================

/// Matches `spider_core::types::id::TaskInstanceId = u64`.
pub type TaskInstanceId = u64;

/// Matches `spider_core::task::TaskIndex = usize`.
pub type TaskIndex = usize;

/// Opaque error-message handle abstracting `String` in `TaskState::Failed(String)`.
/// C6 depends only on the failure discriminant and equality, never on message bytes.
pub type ErrorMsgId = u64;

/// Matches `spider_core::task::TaskState` (`components/spider-core/src/task/mod.rs:42-63`).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum TaskState {
    Pending,
    Ready,
    Running,
    Succeeded,
    Failed(ErrorMsgId),
    Cancelled,
}

impl TaskState {
    /// Spec counterpart of `TaskState::is_terminal`.
    pub open spec fn is_terminal_spec(self) -> bool {
        matches!(self, TaskState::Succeeded | TaskState::Failed(_) | TaskState::Cancelled)
    }

    /// Matches `TaskState::is_terminal(&self) -> bool` (`spider-core/src/task/mod.rs:60-62`).
    pub fn is_terminal(&self) -> (res: bool)
        ensures
            res == self.is_terminal_spec(),
    {
        matches!(self, Self::Succeeded | Self::Failed(_) | Self::Cancelled)
    }
}

/// Matches `StaleStateError` task-level variants (`spider-storage/src/cache/error.rs:158-167`).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum StaleStateError {
    TaskInstanceLimitExceeded,
    TaskAlreadyTerminated(TaskState),
    InvalidTaskInstanceId,
}

/// Matches `InternalError` task-level variants (`spider-storage/src/cache/error.rs:40-55`).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum InternalError {
    TaskNotRunning,
    TaskNotReady,
    TaskGraphCorrupted,
}

/// Matches `CacheError` (`spider-storage/src/cache/error.rs:11-23`).
#[derive(PartialEq, Eq, Clone, Copy)]
pub enum CacheError {
    Internal(InternalError),
    StaleState(StaleStateError),
    TaskOutputsLengthMismatch { expected: usize, actual: usize },
}

/// Formal single-step transition relation for Invariant C6 (Sections 7.2 & 8.5).
///
/// Allowed transitions:
///   - Stuttering: `s -> s` (rejected operations, additional instance registrations,
///     non-last retry failures, non-last force-removals, cancel on already-terminal tasks)
///   - `Pending -> Ready` (last unfinished parent succeeds)
///   - `Ready -> Running` (first live instance registered)
///   - `Running -> Ready` (retry with no other live instance, or dead-EM force-remove of last live instance)
///   - `Running -> Succeeded` (valid live instance succeeds)
///   - `Running -> Failed(_)` (valid live instance fails with 0 retries left)
///   - `Pending | Ready | Running -> Cancelled` (`cancel_non_terminal` on job deactivation)
///
/// All other transitions — especially any exit from a terminal state — are forbidden.
pub open spec fn valid_task_transition(pre: TaskState, post: TaskState) -> bool {
    if pre == post {
        true
    } else {
        match (pre, post) {
            (TaskState::Pending, TaskState::Ready) => true,
            (TaskState::Ready, TaskState::Running) => true,
            (TaskState::Running, TaskState::Ready) => true,
            (TaskState::Running, TaskState::Succeeded) => true,
            (TaskState::Running, TaskState::Failed(_)) => true,
            (TaskState::Pending, TaskState::Cancelled) => true,
            (TaskState::Ready, TaskState::Cancelled) => true,
            (TaskState::Running, TaskState::Cancelled) => true,
            _ => false,
        }
    }
}

/// Meta-property: terminal states are strictly absorbing under `valid_task_transition`.
pub proof fn lemma_terminal_is_absorbing(pre: TaskState, post: TaskState)
    requires
        pre.is_terminal_spec(),
        valid_task_transition(pre, post),
    ensures
        post == pre,
        post.is_terminal_spec(),
{
}

/// Meta-property: explicitly verify every illegal transition edge is rejected.
pub proof fn lemma_forbidden_transitions(err1: ErrorMsgId, err2: ErrorMsgId)
    ensures
        !valid_task_transition(TaskState::Pending, TaskState::Running),
        !valid_task_transition(TaskState::Pending, TaskState::Succeeded),
        !valid_task_transition(TaskState::Pending, TaskState::Failed(err1)),
        !valid_task_transition(TaskState::Ready, TaskState::Pending),
        !valid_task_transition(TaskState::Ready, TaskState::Succeeded),
        !valid_task_transition(TaskState::Ready, TaskState::Failed(err1)),
        !valid_task_transition(TaskState::Running, TaskState::Pending),
        !valid_task_transition(TaskState::Succeeded, TaskState::Pending),
        !valid_task_transition(TaskState::Succeeded, TaskState::Ready),
        !valid_task_transition(TaskState::Succeeded, TaskState::Running),
        !valid_task_transition(TaskState::Succeeded, TaskState::Failed(err1)),
        !valid_task_transition(TaskState::Succeeded, TaskState::Cancelled),
        !valid_task_transition(TaskState::Failed(err1), TaskState::Pending),
        !valid_task_transition(TaskState::Failed(err1), TaskState::Ready),
        !valid_task_transition(TaskState::Failed(err1), TaskState::Running),
        !valid_task_transition(TaskState::Failed(err1), TaskState::Succeeded),
        !valid_task_transition(TaskState::Failed(err1), TaskState::Cancelled),
        (err1 != err2) ==> !valid_task_transition(TaskState::Failed(err1), TaskState::Failed(err2)),
        !valid_task_transition(TaskState::Cancelled, TaskState::Pending),
        !valid_task_transition(TaskState::Cancelled, TaskState::Ready),
        !valid_task_transition(TaskState::Cancelled, TaskState::Running),
        !valid_task_transition(TaskState::Cancelled, TaskState::Succeeded),
        !valid_task_transition(TaskState::Cancelled, TaskState::Failed(err1)),
{
}

// ============================================================================
// Section 2: Faithful Executable `InstancePool`, `RetryCounter`, `TaskControlBlockBase`
//            (matching `components/spider-storage/src/cache/task.rs:835-1094`)
// ============================================================================

/// Matches `InstancePool` (`cache/task.rs:835-888`).
pub struct InstancePool {
    instance_ids: HashSet<TaskInstanceId>,
    max_num_instances: usize,
}

impl InstancePool {
    pub closed spec fn view(&self) -> Set<TaskInstanceId> {
        self.instance_ids@
    }

    pub closed spec fn max_limit(&self) -> nat {
        self.max_num_instances as nat
    }

    pub closed spec fn wf(&self) -> bool {
        &&& obeys_key_model::<TaskInstanceId>()
        &&& self.instance_ids@.finite()
        &&& self.max_num_instances >= 1
        &&& self.instance_ids@.len() <= self.max_num_instances as nat
    }

    /// Matches `InstancePool::create` (`cache/task.rs:850-855`).
    pub fn create(max_num_instances: usize) -> (res: Self)
        ensures
            res.wf(),
            res@ == Set::<TaskInstanceId>::empty(),
            res.max_limit() == if max_num_instances >= 1 { max_num_instances as nat } else { 1nat },
    {
        let limit = if max_num_instances >= 1 { max_num_instances } else { 1 };
        Self {
            instance_ids: HashSet::new(),
            max_num_instances: limit,
        }
    }

    /// Matches `InstancePool::is_full` (`cache/task.rs:860-862`).
    pub fn is_full(&self) -> (res: bool)
        requires
            self.wf(),
        ensures
            res == (self@.len() >= self.max_limit()),
    {
        self.instance_ids.len() >= self.max_num_instances
    }

    /// Matches `InstancePool::add` (`cache/task.rs:865-867`).
    /// Requires `!self.is_full()` (enforced by `ensure_registrable` prior to `add_task_instance`).
    pub fn add(&mut self, instance_id: TaskInstanceId)
        requires
            old(self).wf(),
            old(self)@.len() < old(self).max_limit(),
        ensures
            final(self).wf(),
            final(self)@ == old(self)@.insert(instance_id),
            final(self).max_limit() == old(self).max_limit(),
            !final(self)@.is_empty(),
            final(self)@.contains(instance_id),
    {
        self.instance_ids.insert(instance_id);
        proof {
            assert(self@.contains(instance_id));
            if old(self)@.contains(instance_id) {
                assert(self@ =~= old(self)@);
            }
        }
    }

    /// Matches `InstancePool::remove` (`cache/task.rs:874-876`).
    pub fn remove(&mut self, instance_id: TaskInstanceId) -> (existed: bool)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            existed == old(self)@.contains(instance_id),
            final(self)@ == old(self)@.remove(instance_id),
            final(self).max_limit() == old(self).max_limit(),
            !final(self)@.contains(instance_id),
            !existed ==> final(self)@ == old(self)@,
    {
        let existed = self.instance_ids.remove(&instance_id);
        proof {
            if !existed {
                assert(self@ =~= old(self)@);
            }
        }
        existed
    }

    /// Matches `InstancePool::is_empty` (`cache/task.rs:881-883`).
    pub fn is_empty(&self) -> (res: bool)
        requires
            self.wf(),
        ensures
            res == self@.is_empty(),
    {
        let res = self.instance_ids.is_empty();
        proof {
            assert((self@.len() == 0) == self@.is_empty());
        }
        res
    }
}

/// Matches `RetryCounter` (`cache/task.rs:891-927`).
pub struct RetryCounter {
    max_num_retries_allowed: usize,
    retry_count: usize,
}

impl RetryCounter {
    pub closed spec fn count(&self) -> nat {
        self.retry_count as nat
    }

    pub closed spec fn max_allowed(&self) -> nat {
        self.max_num_retries_allowed as nat
    }

    pub closed spec fn wf(&self) -> bool {
        self.retry_count <= self.max_num_retries_allowed
    }

    /// Matches `RetryCounter::new` (`cache/task.rs:902-907`).
    pub fn new(max_num_retries_allowed: usize) -> (res: Self)
        ensures
            res.wf(),
            res.count() == max_num_retries_allowed as nat,
            res.max_allowed() == max_num_retries_allowed as nat,
    {
        Self {
            max_num_retries_allowed,
            retry_count: max_num_retries_allowed,
        }
    }

    /// Matches `RetryCounter::retry` (`cache/task.rs:913-922`).
    pub fn retry(&mut self) -> (remaining_before: usize)
        requires
            old(self).wf(),
        ensures
            final(self).wf(),
            final(self).max_allowed() == old(self).max_allowed(),
            remaining_before as nat == old(self).count(),
            old(self).count() == 0 ==> final(self).count() == 0,
            old(self).count() > 0 ==> final(self).count() == old(self).count() - 1,
    {
        if self.retry_count == 0 {
            return 0;
        }
        let num_retries_left = self.retry_count;
        self.retry_count = self.retry_count - 1;
        num_retries_left
    }
}

/// Matches `TaskControlBlockBase` (`cache/task.rs:933-1094`) augmented with ghost
/// verification history (`success_count`, `succeeded_by`) to state and prove C6's
/// "one success per task" property directly on the executable implementation.
pub struct TaskControlBlockBase {
    state: TaskState,
    instance_pool: InstancePool,
    retry_counter: RetryCounter,
    success_count: Ghost<nat>,
    succeeded_by: Ghost<Option<TaskInstanceId>>,
}

impl TaskControlBlockBase {
    pub closed spec fn state_spec(&self) -> TaskState {
        self.state
    }

    pub closed spec fn pool_spec(&self) -> Set<TaskInstanceId> {
        self.instance_pool@
    }

    pub closed spec fn max_instances_spec(&self) -> nat {
        self.instance_pool.max_limit()
    }

    pub closed spec fn retries_left_spec(&self) -> nat {
        self.retry_counter.count()
    }

    pub closed spec fn success_count_spec(&self) -> nat {
        self.success_count@
    }

    pub closed spec fn succeeded_by_spec(&self) -> Option<TaskInstanceId> {
        self.succeeded_by@
    }

    /// Inductive C6 + structural invariant on `TaskControlBlockBase`.
    pub closed spec fn inv(&self) -> bool {
        &&& self.instance_pool.wf()
        &&& self.retry_counter.wf()
        // Pool-state coupling:
        //   - Pending/Ready tasks have zero live instances.
        //   - Running tasks have at least one live instance.
        //   - Terminal tasks may still retain surviving straggler IDs in the pool
        //     until they report or are force-removed (per Section 8.5).
        &&& (self.state == TaskState::Pending ==> self.instance_pool@.is_empty())
        &&& (self.state == TaskState::Ready ==> self.instance_pool@.is_empty())
        &&& (self.state == TaskState::Running ==> !self.instance_pool@.is_empty())
        // C6: One success per task.
        &&& self.success_count@ <= 1
        &&& ((self.state == TaskState::Succeeded) <==> (self.success_count@ == 1))
        &&& ((self.state == TaskState::Succeeded) <==> self.succeeded_by@.is_some())
    }

    /// Matches regular TCB initialization (`SharedTaskControlBlock::create`, `cache/task.rs:613-623`).
    pub fn new_regular(
        has_parents: bool,
        max_num_instances: usize,
        max_num_retry: usize,
    ) -> (res: Self)
        ensures
            res.inv(),
            res.state_spec() == if has_parents { TaskState::Pending } else { TaskState::Ready },
            res.pool_spec() == Set::<TaskInstanceId>::empty(),
            res.max_instances_spec() == if max_num_instances >= 1 { max_num_instances as nat } else { 1nat },
            res.retries_left_spec() == max_num_retry as nat,
            res.success_count_spec() == 0,
            res.succeeded_by_spec().is_none(),
    {
        let state = if has_parents {
            TaskState::Pending
        } else {
            TaskState::Ready
        };
        Self {
            state,
            instance_pool: InstancePool::create(max_num_instances),
            retry_counter: RetryCounter::new(max_num_retry),
            success_count: Ghost(0nat),
            succeeded_by: Ghost(None),
        }
    }

    /// Matches termination (commit / cleanup) TCB initialization
    /// (`SharedTerminationTaskControlBlock::create`, `cache/task.rs:813-831`).
    pub fn new_termination(max_num_instances: usize, max_num_retry: usize) -> (res: Self)
        ensures
            res.inv(),
            res.state_spec() == TaskState::Ready,
            res.pool_spec() == Set::<TaskInstanceId>::empty(),
            res.max_instances_spec() == if max_num_instances >= 1 { max_num_instances as nat } else { 1nat },
            res.retries_left_spec() == max_num_retry as nat,
            res.success_count_spec() == 0,
            res.succeeded_by_spec().is_none(),
    {
        Self {
            state: TaskState::Ready,
            instance_pool: InstancePool::create(max_num_instances),
            retry_counter: RetryCounter::new(max_num_retry),
            success_count: Ghost(0nat),
            succeeded_by: Ghost(None),
        }
    }

    /// Matches `TaskControlBlockBase::ensure_registrable` (`cache/task.rs:968-979`).
    pub fn ensure_registrable(&self) -> (res: Result<(), CacheError>)
        requires
            self.inv(),
        ensures
            self.state_spec().is_terminal_spec()
                ==> res == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(self.state_spec()))),
            self.state_spec() == TaskState::Pending
                ==> res == Err::<(), CacheError>(CacheError::Internal(InternalError::TaskNotReady)),
            (!self.state_spec().is_terminal_spec()
                && self.state_spec() != TaskState::Pending
                && self.pool_spec().len() >= self.max_instances_spec())
                ==> res == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::TaskInstanceLimitExceeded)),
            res.is_ok() <==> (
                (self.state_spec() == TaskState::Ready || self.state_spec() == TaskState::Running)
                && self.pool_spec().len() < self.max_instances_spec()
            ),
    {
        if self.state.is_terminal() {
            return Err(CacheError::StaleState(
                StaleStateError::TaskAlreadyTerminated(self.state),
            ));
        }
        if !matches!(self.state, TaskState::Ready | TaskState::Running) {
            return Err(CacheError::Internal(InternalError::TaskNotReady));
        }
        if self.instance_pool.is_full() {
            return Err(CacheError::StaleState(
                StaleStateError::TaskInstanceLimitExceeded,
            ));
        }
        Ok(())
    }

    /// Matches `TaskControlBlockBase::add_task_instance` (`cache/task.rs:983-986`).
    pub fn add_task_instance(&mut self, instance_id: TaskInstanceId)
        requires
            old(self).inv(),
            old(self).state_spec() == TaskState::Ready || old(self).state_spec() == TaskState::Running,
            old(self).pool_spec().len() < old(self).max_instances_spec(),
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            final(self).state_spec() == TaskState::Running,
            final(self).pool_spec() == old(self).pool_spec().insert(instance_id),
            final(self).max_instances_spec() == old(self).max_instances_spec(),
            final(self).retries_left_spec() == old(self).retries_left_spec(),
            final(self).success_count_spec() == old(self).success_count_spec(),
            final(self).succeeded_by_spec() == old(self).succeeded_by_spec(),
    {
        self.instance_pool.add(instance_id);
        self.state = TaskState::Running;
    }

    /// Matches `TaskControlBlockBase::register_task_instance` (`cache/task.rs:952-956`)
    /// and `SharedTaskControlBlock::register_task_instance` (`cache/task.rs:411-425`, where
    /// an error in `fetch_inputs` returns early before `add_task_instance` without mutating state).
    pub fn register_task_instance(&mut self, instance_id: TaskInstanceId) -> (res: Result<(), CacheError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            final(self).max_instances_spec() == old(self).max_instances_spec(),
            final(self).retries_left_spec() == old(self).retries_left_spec(),
            final(self).success_count_spec() == old(self).success_count_spec(),
            final(self).succeeded_by_spec() == old(self).succeeded_by_spec(),
            // C6: A terminal task accepts no new instance.
            old(self).state_spec().is_terminal_spec() ==> (
                res == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(old(self).state_spec())))
                && final(self).state_spec() == old(self).state_spec()
                && final(self).pool_spec() == old(self).pool_spec()
            ),
            // Pending task rejects registration with InternalError::TaskNotReady.
            old(self).state_spec() == TaskState::Pending ==> (
                res == Err::<(), CacheError>(CacheError::Internal(InternalError::TaskNotReady))
                && final(self).state_spec() == old(self).state_spec()
                && final(self).pool_spec() == old(self).pool_spec()
            ),
            // Exact rejection / acceptance behavior:
            res.is_ok() <==> (
                (old(self).state_spec() == TaskState::Ready || old(self).state_spec() == TaskState::Running)
                && old(self).pool_spec().len() < old(self).max_instances_spec()
            ),
            res.is_err() ==> (
                final(self).state_spec() == old(self).state_spec()
                && final(self).pool_spec() == old(self).pool_spec()
            ),
            res.is_ok() ==> (
                final(self).state_spec() == TaskState::Running
                && final(self).pool_spec() == old(self).pool_spec().insert(instance_id)
            ),
    {
        self.ensure_registrable()?;
        self.add_task_instance(instance_id);
        Ok(())
    }

    /// Matches `TaskControlBlockBase::succeed_task_instance` (`cache/task.rs:1002-1014`).
    pub fn succeed_task_instance(&mut self, instance_id: TaskInstanceId) -> (res: Result<(), CacheError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            final(self).max_instances_spec() == old(self).max_instances_spec(),
            final(self).retries_left_spec() == old(self).retries_left_spec(),
            // The reported instance is never live after the call.
            !final(self).pool_spec().contains(instance_id),
            final(self).pool_spec() == old(self).pool_spec().remove(instance_id),
            // C6: An unknown instance is rejected without state change.
            !old(self).pool_spec().contains(instance_id) ==> (
                res == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId))
                && final(self).state_spec() == old(self).state_spec()
                && final(self).pool_spec() == old(self).pool_spec()
                && final(self).success_count_spec() == old(self).success_count_spec()
                && final(self).succeeded_by_spec() == old(self).succeeded_by_spec()
            ),
            // C6: A surviving straggler on an already-terminal task is rejected.
            (old(self).pool_spec().contains(instance_id) && old(self).state_spec().is_terminal_spec()) ==> (
                res == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(old(self).state_spec())))
                && final(self).state_spec() == old(self).state_spec()
                && final(self).success_count_spec() == old(self).success_count_spec()
                && final(self).succeeded_by_spec() == old(self).succeeded_by_spec()
            ),
            // Corollary: `InternalError::TaskNotRunning` is provably unreachable!
            res != Err::<(), CacheError>(CacheError::Internal(InternalError::TaskNotRunning)),
            // C6: One success per task — accepted iff Running with live instance (and thus 0 prior successes).
            res.is_ok() <==> (
                old(self).pool_spec().contains(instance_id)
                && old(self).state_spec() == TaskState::Running
            ),
            res.is_ok() ==> (
                old(self).success_count_spec() == 0
                && final(self).state_spec() == TaskState::Succeeded
                && final(self).success_count_spec() == 1
                && final(self).succeeded_by_spec() == Some(instance_id)
            ),
            res.is_err() ==> (
                final(self).state_spec() == old(self).state_spec()
                && final(self).success_count_spec() == old(self).success_count_spec()
                && final(self).succeeded_by_spec() == old(self).succeeded_by_spec()
            ),
    {
        if !self.instance_pool.remove(instance_id) {
            return Err(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId));
        }
        if self.state.is_terminal() {
            return Err(CacheError::StaleState(
                StaleStateError::TaskAlreadyTerminated(self.state),
            ));
        }
        if !matches!(self.state, TaskState::Running) {
            // Unreachable under `old(self).inv()`: Pending and Ready imply an empty
            // instance pool, contradicting `remove(instance_id) == true`.
            return Err(CacheError::Internal(InternalError::TaskNotRunning));
        }
        self.state = TaskState::Succeeded;
        self.success_count = Ghost(self.success_count@ + 1);
        self.succeeded_by = Ghost(Some(instance_id));
        Ok(())
    }

    /// Matches `SharedTaskControlBlock::succeed_task_instance` output-count precheck
    /// (`cache/task.rs:469-475`): if `actual_outputs_len != expected_outputs_len`,
    /// returns `TaskOutputsLengthMismatch` before touching `instance_pool` or `state`.
    pub fn succeed_regular_precheck(
        &mut self,
        instance_id: TaskInstanceId,
        expected_outputs_len: usize,
        actual_outputs_len: usize,
    ) -> (res: Result<(), CacheError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            actual_outputs_len != expected_outputs_len ==> (
                res == Err::<(), CacheError>(CacheError::TaskOutputsLengthMismatch {
                    expected: expected_outputs_len,
                    actual: actual_outputs_len,
                })
                && final(self).state_spec() == old(self).state_spec()
                && final(self).pool_spec() == old(self).pool_spec()
                && final(self).success_count_spec() == old(self).success_count_spec()
            ),
            actual_outputs_len == expected_outputs_len ==> (
                res.is_ok() <==> (
                    old(self).pool_spec().contains(instance_id)
                    && old(self).state_spec() == TaskState::Running
                )
            ),
            res.is_ok() ==> (
                old(self).success_count_spec() == 0
                && final(self).state_spec() == TaskState::Succeeded
                && final(self).success_count_spec() == 1
                && final(self).succeeded_by_spec() == Some(instance_id)
            ),
    {
        if actual_outputs_len != expected_outputs_len {
            return Err(CacheError::TaskOutputsLengthMismatch {
                expected: expected_outputs_len,
                actual: actual_outputs_len,
            });
        }
        self.succeed_task_instance(instance_id)
    }

    /// Matches `TaskControlBlockBase::fail_task_instance` (`cache/task.rs:1039-1064`).
    pub fn fail_task_instance(
        &mut self,
        task_instance_id: TaskInstanceId,
        error_message: ErrorMsgId,
    ) -> (res: Result<TaskState, CacheError>)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            final(self).max_instances_spec() == old(self).max_instances_spec(),
            final(self).success_count_spec() == old(self).success_count_spec(),
            final(self).succeeded_by_spec() == old(self).succeeded_by_spec(),
            !final(self).pool_spec().contains(task_instance_id),
            final(self).pool_spec() == old(self).pool_spec().remove(task_instance_id),
            // C6: Unknown instance rejected.
            !old(self).pool_spec().contains(task_instance_id) ==> (
                res == Err::<TaskState, CacheError>(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId))
                && final(self).state_spec() == old(self).state_spec()
                && final(self).retries_left_spec() == old(self).retries_left_spec()
            ),
            // C6: Terminal task rejects straggler failure without changing state or retries.
            (old(self).pool_spec().contains(task_instance_id) && old(self).state_spec().is_terminal_spec()) ==> (
                res == Err::<TaskState, CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(old(self).state_spec())))
                && final(self).state_spec() == old(self).state_spec()
                && final(self).retries_left_spec() == old(self).retries_left_spec()
            ),
            // Corollary: `InternalError::TaskNotRunning` is provably unreachable!
            res != Err::<TaskState, CacheError>(CacheError::Internal(InternalError::TaskNotRunning)),
            // Valid failure transition:
            res.is_ok() <==> (
                old(self).pool_spec().contains(task_instance_id)
                && old(self).state_spec() == TaskState::Running
            ),
            res.is_ok() ==> (
                res == Ok::<TaskState, CacheError>(final(self).state_spec())
                && (old(self).retries_left_spec() > 0 ==> (
                    final(self).retries_left_spec() == old(self).retries_left_spec() - 1
                    && final(self).state_spec() == if old(self).pool_spec().remove(task_instance_id).is_empty() {
                        TaskState::Ready
                    } else {
                        TaskState::Running
                    }
                ))
                && (old(self).retries_left_spec() == 0 ==> (
                    final(self).retries_left_spec() == 0
                    && final(self).state_spec() == TaskState::Failed(error_message)
                ))
            ),
    {
        if !self.instance_pool.remove(task_instance_id) {
            return Err(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId));
        }
        if self.state.is_terminal() {
            return Err(CacheError::StaleState(
                StaleStateError::TaskAlreadyTerminated(self.state),
            ));
        }
        if !matches!(self.state, TaskState::Running) {
            return Err(CacheError::Internal(InternalError::TaskNotRunning));
        }

        if self.retry_counter.retry() != 0 {
            self.state = if self.instance_pool.is_empty() {
                TaskState::Ready
            } else {
                TaskState::Running
            };
        } else {
            self.state = TaskState::Failed(error_message);
        }
        Ok(self.state)
    }

    /// Matches `TaskControlBlockBase::force_remove_task_instance` (`cache/task.rs:1074-1086`).
    pub fn force_remove_task_instance(&mut self, instance_id: TaskInstanceId) -> (existed: bool)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            existed == old(self).pool_spec().contains(instance_id),
            final(self).pool_spec() == old(self).pool_spec().remove(instance_id),
            !final(self).pool_spec().contains(instance_id),
            final(self).max_instances_spec() == old(self).max_instances_spec(),
            final(self).retries_left_spec() == old(self).retries_left_spec(),
            final(self).success_count_spec() == old(self).success_count_spec(),
            final(self).succeeded_by_spec() == old(self).succeeded_by_spec(),
            // Running -> Ready iff the removed instance existed and was the last live instance.
            (existed && old(self).state_spec() == TaskState::Running && final(self).pool_spec().is_empty())
                ==> final(self).state_spec() == TaskState::Ready,
            !(existed && old(self).state_spec() == TaskState::Running && final(self).pool_spec().is_empty())
                ==> final(self).state_spec() == old(self).state_spec(),
    {
        let existed = self.instance_pool.remove(instance_id);
        if existed && matches!(self.state, TaskState::Running) && self.instance_pool.is_empty() {
            self.state = TaskState::Ready;
        }
        existed
    }

    /// Matches `TaskControlBlockBase::cancel_non_terminal` (`cache/task.rs:1089-1093`).
    pub fn cancel_non_terminal(&mut self)
        requires
            old(self).inv(),
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            final(self).pool_spec() == old(self).pool_spec(),
            final(self).max_instances_spec() == old(self).max_instances_spec(),
            final(self).retries_left_spec() == old(self).retries_left_spec(),
            final(self).success_count_spec() == old(self).success_count_spec(),
            final(self).succeeded_by_spec() == old(self).succeeded_by_spec(),
            old(self).state_spec().is_terminal_spec() ==> final(self).state_spec() == old(self).state_spec(),
            !old(self).state_spec().is_terminal_spec() ==> final(self).state_spec() == TaskState::Cancelled,
    {
        if !self.state.is_terminal() {
            self.state = TaskState::Cancelled;
        }
    }

    /// Models `child_tcb.base.state = TaskState::Ready` (`cache/task.rs:513`)
    /// when a regular task's last unfinished parent completes.
    pub fn mark_ready_from_pending(&mut self)
        requires
            old(self).inv(),
            old(self).state_spec() == TaskState::Pending,
        ensures
            final(self).inv(),
            valid_task_transition(old(self).state_spec(), final(self).state_spec()),
            final(self).state_spec() == TaskState::Ready,
            final(self).pool_spec() == old(self).pool_spec(),
            final(self).max_instances_spec() == old(self).max_instances_spec(),
            final(self).retries_left_spec() == old(self).retries_left_spec(),
            final(self).success_count_spec() == old(self).success_count_spec(),
            final(self).succeeded_by_spec() == old(self).succeeded_by_spec(),
    {
        self.state = TaskState::Ready;
    }

    /// Matches `SharedTaskControlBlock::is_terminal` / `SharedTerminationTaskControlBlock::is_terminal`.
    pub fn is_terminal(&self) -> (res: bool)
        requires
            self.inv(),
        ensures
            res == self.state_spec().is_terminal_spec(),
    {
        self.state.is_terminal()
    }
}

// ============================================================================
// Section 3: Verified Executable Straggler, Duplicate, Cancel & Retry Scenarios
//            (matching Section 8.8(a) and `cache/task.rs` test suite)
// ============================================================================

/// Section 8.8(a): Two live instances `i1 != i2` race; `i1` succeeds first.
/// Proves:
///   - Duplicate report from `i1` fails with `InvalidTaskInstanceId`.
///   - Straggler failure/success from `i2` fails with `TaskAlreadyTerminated(Succeeded)`.
///   - Second report from `i2` fails with `InvalidTaskInstanceId`.
///   - New registration `i3` fails with `TaskAlreadyTerminated(Succeeded)`.
///   - `state` remains `Succeeded` and `success_count == 1`.
pub fn verified_scenario_straggler_after_success(
    i1: TaskInstanceId,
    i2: TaskInstanceId,
    i3: TaskInstanceId,
    err: ErrorMsgId,
)
    requires
        i1 != i2,
{
    let mut tcb = TaskControlBlockBase::new_regular(false, 2, 1);
    let r1 = tcb.register_task_instance(i1);
    assert(r1.is_ok());
    let r2 = tcb.register_task_instance(i2);
    assert(r2.is_ok());

    // i1 succeeds.
    let s1 = tcb.succeed_task_instance(i1);
    assert(s1.is_ok());
    assert(tcb.state_spec() == TaskState::Succeeded);
    assert(tcb.success_count_spec() == 1);

    // Duplicate success from i1 is rejected as unknown instance.
    let dup1 = tcb.succeed_task_instance(i1);
    assert(dup1 == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)));

    // Straggler failure from i2 is rejected as already terminated (and removes i2).
    let straggler_fail = tcb.fail_task_instance(i2, err);
    assert(straggler_fail == Err::<TaskState, CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(TaskState::Succeeded))));

    // Subsequent straggler success from i2 is rejected as unknown instance.
    let straggler_succ2 = tcb.succeed_task_instance(i2);
    assert(straggler_succ2 == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)));

    // New registration i3 is rejected because task is terminal.
    let r3 = tcb.register_task_instance(i3);
    assert(r3 == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(TaskState::Succeeded))));

    assert(tcb.state_spec() == TaskState::Succeeded);
    assert(tcb.success_count_spec() == 1);
}

/// `cache/task.rs` test `fail_instance_then_reject_stale_and_surviving`:
/// `i1` fails with 0 retries -> `Failed`; both `i1` (stale) and `i2` (surviving)
/// cannot succeed, and no new instance `i3` can register.
pub fn verified_scenario_terminal_failure_rejects_surviving(
    i1: TaskInstanceId,
    i2: TaskInstanceId,
    i3: TaskInstanceId,
    err: ErrorMsgId,
)
    requires
        i1 != i2,
{
    let mut tcb = TaskControlBlockBase::new_termination(2, 0);
    let r1 = tcb.register_task_instance(i1);
    assert(r1.is_ok());
    let r2 = tcb.register_task_instance(i2);
    assert(r2.is_ok());

    let f1 = tcb.fail_task_instance(i1, err);
    assert(f1 == Ok::<TaskState, CacheError>(TaskState::Failed(err)));

    let s1 = tcb.succeed_task_instance(i1);
    assert(s1 == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)));

    let s2 = tcb.succeed_task_instance(i2);
    assert(s2 == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(TaskState::Failed(err)))));

    let r3 = tcb.register_task_instance(i3);
    assert(r3 == Err::<(), CacheError>(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(TaskState::Failed(err)))));

    assert(tcb.state_spec() == TaskState::Failed(err));
    assert(tcb.success_count_spec() == 0);
}

/// Retry (`Running -> Ready`), dead-EM force-remove (`Running -> Ready`),
/// and cancel (`Running -> Cancelled`) with surviving straggler rejection.
pub fn verified_scenario_retry_force_remove_and_cancel(
    i1: TaskInstanceId,
    i2: TaskInstanceId,
    i3: TaskInstanceId,
    err: ErrorMsgId,
)
    requires
        i1 != i2,
        i2 != i3,
{
    let mut tcb = TaskControlBlockBase::new_regular(true, 1, 1);
    assert(tcb.state_spec() == TaskState::Pending);

    // Registration on Pending fails with TaskNotReady.
    let reg_pending = tcb.register_task_instance(i1);
    assert(reg_pending == Err::<(), CacheError>(CacheError::Internal(InternalError::TaskNotReady)));

    // Parent completes: Pending -> Ready.
    tcb.mark_ready_from_pending();
    assert(tcb.state_spec() == TaskState::Ready);

    // Register i1: Ready -> Running.
    let r1 = tcb.register_task_instance(i1);
    assert(r1.is_ok());
    assert(tcb.state_spec() == TaskState::Running);

    // Fail i1 with 1 retry left: Running -> Ready.
    let f1 = tcb.fail_task_instance(i1, err);
    assert(f1 == Ok::<TaskState, CacheError>(TaskState::Ready));
    assert(tcb.state_spec() == TaskState::Ready);

    // Register i2: Ready -> Running.
    let r2 = tcb.register_task_instance(i2);
    assert(r2.is_ok());

    // Dead EM force-removes i2: Running -> Ready.
    let removed = tcb.force_remove_task_instance(i2);
    assert(removed);
    assert(tcb.state_spec() == TaskState::Ready);

    // Register i3: Ready -> Running, then cancel: Running -> Cancelled.
    let r3 = tcb.register_task_instance(i3);
    assert(r3.is_ok());
    tcb.cancel_non_terminal();
    assert(tcb.state_spec() == TaskState::Cancelled);

    // Force-remove on Cancelled must NOT move back to Ready!
    let removed3 = tcb.force_remove_task_instance(i3);
    assert(removed3);
    assert(tcb.state_spec() == TaskState::Cancelled);
    assert(tcb.success_count_spec() == 0);
}

// ============================================================================
// Section 4: Full Multi-Task DAG & Concurrent Interleaving Transition System
//            (Proving C6 Inductively Over Arbitrary Finite Execution Traces)
// ============================================================================

/// Abstract well-formed task DAG matching `TaskGraph::from_parts` (`cache/task.rs:286-305`)
/// and Section 8.6 (edges point strictly from lower index `u` to higher index `v`).
pub struct DagSpec {
    pub num_tasks: nat,
    pub children: Seq<Seq<nat>>,
    pub parents: Seq<Seq<nat>>,
}

pub open spec fn seq_no_duplicates(s: Seq<nat>) -> bool {
    forall|i: int, j: int| 0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s[i] != s[j]
}

impl DagSpec {
    pub open spec fn wf(self) -> bool {
        &&& self.children.len() == self.num_tasks
        &&& self.parents.len() == self.num_tasks
        // Every child list has valid, strictly larger indices with no duplicates.
        &&& forall|u: int| 0 <= u < self.num_tasks ==> (
            seq_no_duplicates(self.children[u])
            && forall|k: int| 0 <= k < self.children[u].len() ==> (
                u < self.children[u][k] && self.children[u][k] < self.num_tasks
            )
        )
        // Every parent list has valid, strictly smaller indices with no duplicates.
        &&& forall|v: int| 0 <= v < self.num_tasks ==> (
            seq_no_duplicates(self.parents[v])
            && forall|k: int| 0 <= k < self.parents[v].len() ==> (
                0 <= self.parents[v][k] && self.parents[v][k] < v
            )
        )
        // `children` and `parents` are exact transposes of the DAG edge relation.
        &&& forall|u: int, v: int| 0 <= u < self.num_tasks && 0 <= v < self.num_tasks ==> (
            self.children[u].contains(v as nat) <==> self.parents[v].contains(u as nat)
        )
    }
}

/// Abstract state of a single task control block inside `TaskGraph`.
pub struct TaskSpec {
    pub state: TaskState,
    pub live: Set<TaskInstanceId>,
    pub max_instances: nat,
    pub retries_left: nat,
    pub max_retries: nat,
    pub num_unfinished_parents: nat,
    pub success_count: nat,
}

impl TaskSpec {
    pub open spec fn c6_task_inv(self) -> bool {
        &&& self.live.finite()
        &&& self.max_instances >= 1
        &&& self.live.len() <= self.max_instances
        &&& self.retries_left <= self.max_retries
        &&& (self.state == TaskState::Pending ==> self.live.is_empty())
        &&& (self.state == TaskState::Ready ==> self.live.is_empty())
        &&& (self.state == TaskState::Running ==> !self.live.is_empty())
        &&& self.success_count <= 1
        &&& ((self.state == TaskState::Succeeded) <==> (self.success_count == 1))
    }
}

/// Identifies any task within a job's `TaskGraph`: regular task `0..num_tasks`,
/// commit task, or cleanup task (matching `spider_core::types::id::TaskId`).
pub enum GraphTaskId {
    Regular(nat),
    Commit,
    Cleanup,
}

/// Full `TaskGraph` state in cache (regular tasks + optional commit + optional cleanup),
/// plus `next_instance_id` modeling `TaskInstancePoolHandle`'s monotonic `AtomicU64` allocator.
pub struct TaskGraphSpec {
    pub tasks: Seq<TaskSpec>,
    pub commit_task: Option<TaskSpec>,
    pub cleanup_task: Option<TaskSpec>,
    pub allocated_ids: Set<TaskInstanceId>,
}

/// Exact recursive count of parents in `parents` whose state is not `Succeeded`.
pub open spec fn count_unfinished_parents(parents: Seq<nat>, tasks: Seq<TaskSpec>) -> nat
    decreases parents.len(),
{
    if parents.len() == 0 {
        0
    } else {
        let last = parents.last();
        let rest = parents.drop_last();
        let inc: nat = if last < tasks.len() && tasks[last as int].state != TaskState::Succeeded {
            1
        } else {
            0
        };
        count_unfinished_parents(rest, tasks) + inc
    }
}

pub proof fn lemma_count_init_eq_len(parents: Seq<nat>, tasks: Seq<TaskSpec>)
    requires
        forall|k: int| 0 <= k < parents.len() ==> (
            parents[k] < tasks.len() && tasks[parents[k] as int].state != TaskState::Succeeded
        ),
    ensures
        count_unfinished_parents(parents, tasks) == parents.len(),
    decreases parents.len(),
{
    if parents.len() > 0 {
        let rest = parents.drop_last();
        assert forall|k: int| 0 <= k < rest.len() implies (
            rest[k] < tasks.len() && tasks[rest[k] as int].state != TaskState::Succeeded
        ) by {
            assert(rest[k] == parents[k]);
        };
        lemma_count_init_eq_len(rest, tasks);
    }
}

pub proof fn lemma_count_preserved_if_succeeded_unchanged(
    parents: Seq<nat>,
    t1: Seq<TaskSpec>,
    t2: Seq<TaskSpec>,
)
    requires
        t1.len() == t2.len(),
        forall|i: int| 0 <= i < t1.len() ==> (
            (t1[i].state == TaskState::Succeeded) <==> (t2[i].state == TaskState::Succeeded)
        ),
    ensures
        count_unfinished_parents(parents, t1) == count_unfinished_parents(parents, t2),
    decreases parents.len(),
{
    if parents.len() > 0 {
        lemma_count_preserved_if_succeeded_unchanged(parents.drop_last(), t1, t2);
    }
}

pub proof fn lemma_count_unchanged_if_not_parent(
    parents: Seq<nat>,
    t1: Seq<TaskSpec>,
    t2: Seq<TaskSpec>,
    u: nat,
)
    requires
        t1.len() == t2.len(),
        !parents.contains(u),
        forall|i: int| 0 <= i < t1.len() && i != u ==> (
            (t1[i].state == TaskState::Succeeded) <==> (t2[i].state == TaskState::Succeeded)
        ),
    ensures
        count_unfinished_parents(parents, t1) == count_unfinished_parents(parents, t2),
    decreases parents.len(),
{
    if parents.len() > 0 {
        let last = parents.last();
        let rest = parents.drop_last();
        assert(last == parents[parents.len() - 1]);
        assert(last != u);
        assert(!rest.contains(u)) by {
            if rest.contains(u) {
                let idx = choose|k: int| 0 <= k < rest.len() && rest[k] == u;
                assert(parents[idx] == u);
            }
        };
        lemma_count_unchanged_if_not_parent(rest, t1, t2, u);
    }
}

pub proof fn lemma_count_decrements_by_one_on_parent_success(
    parents: Seq<nat>,
    t1: Seq<TaskSpec>,
    t2: Seq<TaskSpec>,
    u: nat,
)
    requires
        t1.len() == t2.len(),
        seq_no_duplicates(parents),
        parents.contains(u),
        u < t1.len(),
        t1[u as int].state != TaskState::Succeeded,
        t2[u as int].state == TaskState::Succeeded,
        forall|i: int| 0 <= i < t1.len() && i != u ==> (
            (t1[i].state == TaskState::Succeeded) <==> (t2[i].state == TaskState::Succeeded)
        ),
    ensures
        count_unfinished_parents(parents, t1) >= 1,
        count_unfinished_parents(parents, t2) == count_unfinished_parents(parents, t1) - 1,
    decreases parents.len(),
{
    let n = parents.len();
    assert(n > 0);
    let last = parents.last();
    let rest = parents.drop_last();
    assert(last == parents[n - 1]);
    assert(seq_no_duplicates(rest)) by {
        assert forall|i: int, j: int|
            0 <= i < rest.len() && 0 <= j < rest.len() && i != j
            implies rest[i] != rest[j]
        by {
            assert(rest[i] == parents[i]);
            assert(rest[j] == parents[j]);
        };
    };
    if last == u {
        assert(!rest.contains(u)) by {
            if rest.contains(u) {
                let idx = choose|k: int| 0 <= k < rest.len() && rest[k] == u;
                assert(parents[idx] == parents[n - 1]);
                assert(idx != n - 1);
            }
        };
        lemma_count_unchanged_if_not_parent(rest, t1, t2, u);
    } else {
        assert(rest.contains(u)) by {
            let idx = choose|k: int| 0 <= k < n && parents[k] == u;
            assert(idx < n - 1);
            assert(rest[idx] == u);
        };
        lemma_count_decrements_by_one_on_parent_success(rest, t1, t2, u);
    }
}

impl TaskGraphSpec {
    pub open spec fn get_task(self, tid: GraphTaskId) -> Option<TaskSpec> {
        match tid {
            GraphTaskId::Regular(i) =>
                if i < self.tasks.len() { Some(self.tasks[i as int]) } else { None },
            GraphTaskId::Commit => self.commit_task,
            GraphTaskId::Cleanup => self.cleanup_task,
        }
    }

    /// Inductive invariant of the entire `TaskGraph` (combining C6 + parent-counter coupling).
    pub open spec fn inv(self, dag: DagSpec) -> bool {
        &&& dag.wf()
        &&& self.tasks.len() == dag.num_tasks
        &&& self.allocated_ids.finite()
        // Regular tasks:
        &&& forall|i: int| 0 <= i < self.tasks.len() ==> (
            self.tasks[i].c6_task_inv()
            && self.tasks[i].live.subset_of(self.allocated_ids)
            && self.tasks[i].num_unfinished_parents == count_unfinished_parents(dag.parents[i], self.tasks)
            // Crucial C6-DAG coupling: a regular task with unfinished parents can ONLY be Pending or Cancelled!
            && (self.tasks[i].num_unfinished_parents > 0 ==> (
                self.tasks[i].state == TaskState::Pending || self.tasks[i].state == TaskState::Cancelled
            ))
        )
        // Commit task (if present):
        &&& match self.commit_task {
            Some(ct) => ct.c6_task_inv()
                && ct.live.subset_of(self.allocated_ids)
                && ct.num_unfinished_parents == 0
                && ct.state != TaskState::Pending,
            None => true,
        }
        // Cleanup task (if present):
        &&& match self.cleanup_task {
            Some(cl) => cl.c6_task_inv()
                && cl.live.subset_of(self.allocated_ids)
                && cl.num_unfinished_parents == 0
                && cl.state != TaskState::Pending,
            None => true,
        }
    }
}

/// Initial state of a `TaskGraph` created by `TaskGraph::from_parts` (`cache/task.rs:249-321`).
pub open spec fn init_task_graph(
    dag: DagSpec,
    max_instances: Seq<nat>,
    max_retries: Seq<nat>,
    commit_policy: Option<(nat, nat)>,
    cleanup_policy: Option<(nat, nat)>,
) -> TaskGraphSpec {
    TaskGraphSpec {
        tasks: Seq::new(dag.num_tasks, |i: int| TaskSpec {
            state: if dag.parents[i].len() == 0 { TaskState::Ready } else { TaskState::Pending },
            live: Set::empty(),
            max_instances: if max_instances[i] >= 1 { max_instances[i] } else { 1 },
            retries_left: max_retries[i],
            max_retries: max_retries[i],
            num_unfinished_parents: dag.parents[i].len(),
            success_count: 0,
        }),
        commit_task: match commit_policy {
            Some((mi, mr)) => Some(TaskSpec {
                state: TaskState::Ready,
                live: Set::empty(),
                max_instances: if mi >= 1 { mi } else { 1 },
                retries_left: mr,
                max_retries: mr,
                num_unfinished_parents: 0,
                success_count: 0,
            }),
            None => None,
        },
        cleanup_task: match cleanup_policy {
            Some((mi, mr)) => Some(TaskSpec {
                state: TaskState::Ready,
                live: Set::empty(),
                max_instances: if mi >= 1 { mi } else { 1 },
                retries_left: mr,
                max_retries: mr,
                num_unfinished_parents: 0,
                success_count: 0,
            }),
            None => None,
        },
        allocated_ids: Set::empty(),
    }
}

/// Proof that `init_task_graph` establishes `TaskGraphSpec::inv`.
pub proof fn lemma_init_task_graph_inv(
    dag: DagSpec,
    max_instances: Seq<nat>,
    max_retries: Seq<nat>,
    commit_policy: Option<(nat, nat)>,
    cleanup_policy: Option<(nat, nat)>,
)
    requires
        dag.wf(),
        max_instances.len() == dag.num_tasks,
        max_retries.len() == dag.num_tasks,
    ensures
        init_task_graph(dag, max_instances, max_retries, commit_policy, cleanup_policy).inv(dag),
{
    let g = init_task_graph(dag, max_instances, max_retries, commit_policy, cleanup_policy);
    assert forall|i: int| 0 <= i < g.tasks.len() implies (
        g.tasks[i].c6_task_inv()
        && g.tasks[i].live.subset_of(g.allocated_ids)
        && g.tasks[i].num_unfinished_parents == count_unfinished_parents(dag.parents[i], g.tasks)
        && (g.tasks[i].num_unfinished_parents > 0 ==> (
            g.tasks[i].state == TaskState::Pending || g.tasks[i].state == TaskState::Cancelled
        ))
    ) by {
        assert forall|k: int| 0 <= k < dag.parents[i].len() implies (
            dag.parents[i][k] < g.tasks.len()
            && g.tasks[dag.parents[i][k] as int].state != TaskState::Succeeded
        ) by {
            let p = dag.parents[i][k];
            assert(p < i && i < dag.num_tasks);
        };
        lemma_count_init_eq_len(dag.parents[i], g.tasks);
    };
}

/// Every operation that can execute on a cached `TaskGraph` (serialized by per-task mutexes
/// and the job RwLock across RPC handlers, the `TaskInstancePool` actor, and `TreeCommitter`).
pub enum GraphOp {
    /// `create_task_instance` -> `register_task_instance`
    Register { tid: GraphTaskId, instance_id: TaskInstanceId },
    /// `succeed_task_instance` (regular or termination); `outputs_len_ok` models line 469 precheck.
    Succeed { tid: GraphTaskId, instance_id: TaskInstanceId, outputs_len_ok: bool },
    /// `fail_task_instance` (regular or termination)
    Fail { tid: GraphTaskId, instance_id: TaskInstanceId, err: ErrorMsgId },
    /// `TaskInstancePool` dead-EM recovery calling `force_remove_task_instance`
    ForceRemove { tid: GraphTaskId, instance_id: TaskInstanceId },
    /// `apply_tree_state` deactivation calling `TaskGraph::cancel_non_terminal`
    /// (cancels all regular tasks and the commit task, leaving the cleanup task intact).
    CancelNonTerminalGraph,
}

/// Observable result of executing one `GraphOp`.
pub enum OpOutcome {
    Accepted,
    Rejected(CacheError),
    NoOp,
}

/// Spec transition of a single `TaskSpec` on `Register`.
pub open spec fn step_register_task(t: TaskSpec, id: TaskInstanceId) -> (TaskSpec, OpOutcome) {
    if t.state.is_terminal_spec() {
        (t, OpOutcome::Rejected(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(t.state))))
    } else if !(t.state == TaskState::Ready || t.state == TaskState::Running) {
        (t, OpOutcome::Rejected(CacheError::Internal(InternalError::TaskNotReady)))
    } else if t.live.len() >= t.max_instances {
        (t, OpOutcome::Rejected(CacheError::StaleState(StaleStateError::TaskInstanceLimitExceeded)))
    } else {
        (
            TaskSpec {
                state: TaskState::Running,
                live: t.live.insert(id),
                ..t
            },
            OpOutcome::Accepted,
        )
    }
}

/// Spec transition of a single `TaskSpec` on `Succeed` (the task's own update).
pub open spec fn step_succeed_own_task(
    t: TaskSpec,
    id: TaskInstanceId,
    outputs_len_ok: bool,
) -> (TaskSpec, OpOutcome) {
    if !outputs_len_ok {
        (t, OpOutcome::Rejected(CacheError::TaskOutputsLengthMismatch { expected: 1, actual: 0 }))
    } else if !t.live.contains(id) {
        (t, OpOutcome::Rejected(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)))
    } else if t.state.is_terminal_spec() {
        (
            TaskSpec { live: t.live.remove(id), ..t },
            OpOutcome::Rejected(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(t.state))),
        )
    } else if t.state != TaskState::Running {
        (
            TaskSpec { live: t.live.remove(id), ..t },
            OpOutcome::Rejected(CacheError::Internal(InternalError::TaskNotRunning)),
        )
    } else {
        (
            TaskSpec {
                state: TaskState::Succeeded,
                live: t.live.remove(id),
                success_count: t.success_count + 1,
                ..t
            },
            OpOutcome::Accepted,
        )
    }
}

/// Spec transition of a single `TaskSpec` on `Fail`.
pub open spec fn step_fail_task(
    t: TaskSpec,
    id: TaskInstanceId,
    err: ErrorMsgId,
) -> (TaskSpec, OpOutcome) {
    if !t.live.contains(id) {
        (t, OpOutcome::Rejected(CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)))
    } else if t.state.is_terminal_spec() {
        (
            TaskSpec { live: t.live.remove(id), ..t },
            OpOutcome::Rejected(CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(t.state))),
        )
    } else if t.state != TaskState::Running {
        (
            TaskSpec { live: t.live.remove(id), ..t },
            OpOutcome::Rejected(CacheError::Internal(InternalError::TaskNotRunning)),
        )
    } else {
        let new_live = t.live.remove(id);
        if t.retries_left > 0 {
            let next_state = if new_live.is_empty() { TaskState::Ready } else { TaskState::Running };
            (
                TaskSpec {
                    state: next_state,
                    live: new_live,
                    retries_left: (t.retries_left - 1) as nat,
                    ..t
                },
                OpOutcome::Accepted,
            )
        } else {
            (
                TaskSpec {
                    state: TaskState::Failed(err),
                    live: new_live,
                    ..t
                },
                OpOutcome::Accepted,
            )
        }
    }
}

/// Spec transition of a single `TaskSpec` on `ForceRemove`.
pub open spec fn step_force_remove_task(t: TaskSpec, id: TaskInstanceId) -> (TaskSpec, OpOutcome) {
    let existed = t.live.contains(id);
    let new_live = t.live.remove(id);
    let next_state = if existed && t.state == TaskState::Running && new_live.is_empty() {
        TaskState::Ready
    } else {
        t.state
    };
    (
        TaskSpec {
            state: next_state,
            live: new_live,
            ..t
        },
        if existed { OpOutcome::Accepted } else { OpOutcome::NoOp },
    )
}

/// Spec transition of a single `TaskSpec` on `cancel_non_terminal`.
pub open spec fn step_cancel_task(t: TaskSpec) -> TaskSpec {
    if !t.state.is_terminal_spec() {
        TaskSpec { state: TaskState::Cancelled, ..t }
    } else {
        t
    }
}

/// Spec effect on a child task `v` when parent `u` succeeds (`cache/task.rs:488-515`).
/// Note: If `child` is already terminal (`Cancelled`), `cache/task.rs:505` returns
/// `Err(TaskGraphCorrupted)` WITHOUT changing `child.state`.
pub open spec fn apply_parent_success_to_child(child: TaskSpec) -> TaskSpec {
    let new_unfinished: nat = if child.num_unfinished_parents > 0 {
        (child.num_unfinished_parents - 1) as nat
    } else {
        0
    };
    let next_state = if new_unfinished == 0 && !child.state.is_terminal_spec() {
        TaskState::Ready
    } else {
        child.state
    };
    TaskSpec {
        state: next_state,
        num_unfinished_parents: new_unfinished,
        ..child
    }
}

/// Full `TaskGraph` single-step transition function.
pub open spec fn graph_step(
    dag: DagSpec,
    g: TaskGraphSpec,
    op: GraphOp,
) -> (TaskGraphSpec, OpOutcome) {
    match op {
        GraphOp::Register { tid, instance_id } => match tid {
            GraphTaskId::Regular(idx) => {
                if idx < g.tasks.len() {
                    let (t2, out) = step_register_task(g.tasks[idx as int], instance_id);
                    let new_alloc = if out == OpOutcome::Accepted {
                        g.allocated_ids.insert(instance_id)
                    } else {
                        g.allocated_ids
                    };
                    (TaskGraphSpec { tasks: g.tasks.update(idx as int, t2), allocated_ids: new_alloc, ..g }, out)
                } else {
                    (g, OpOutcome::NoOp)
                }
            }
            GraphTaskId::Commit => match g.commit_task {
                Some(ct) => {
                    let (ct2, out) = step_register_task(ct, instance_id);
                    let new_alloc = if out == OpOutcome::Accepted {
                        g.allocated_ids.insert(instance_id)
                    } else {
                        g.allocated_ids
                    };
                    (TaskGraphSpec { commit_task: Some(ct2), allocated_ids: new_alloc, ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
            GraphTaskId::Cleanup => match g.cleanup_task {
                Some(cl) => {
                    let (cl2, out) = step_register_task(cl, instance_id);
                    let new_alloc = if out == OpOutcome::Accepted {
                        g.allocated_ids.insert(instance_id)
                    } else {
                        g.allocated_ids
                    };
                    (TaskGraphSpec { cleanup_task: Some(cl2), allocated_ids: new_alloc, ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
        },
        GraphOp::Succeed { tid, instance_id, outputs_len_ok } => match tid {
            GraphTaskId::Regular(idx) => {
                if idx < g.tasks.len() {
                    let (t2, out) = step_succeed_own_task(g.tasks[idx as int], instance_id, outputs_len_ok);
                    if out == OpOutcome::Accepted {
                        // Update task `idx` to Succeeded and decrement every child `v in dag.children[idx]`.
                        let new_tasks = Seq::new(g.tasks.len(), |v: int|
                            if v == idx as int {
                                t2
                            } else if dag.children[idx as int].contains(v as nat) {
                                apply_parent_success_to_child(g.tasks[v])
                            } else {
                                g.tasks[v]
                            }
                        );
                        (TaskGraphSpec { tasks: new_tasks, ..g }, out)
                    } else {
                        (TaskGraphSpec { tasks: g.tasks.update(idx as int, t2), ..g }, out)
                    }
                } else {
                    (g, OpOutcome::NoOp)
                }
            }
            GraphTaskId::Commit => match g.commit_task {
                Some(ct) => {
                    let (ct2, out) = step_succeed_own_task(ct, instance_id, true);
                    (TaskGraphSpec { commit_task: Some(ct2), ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
            GraphTaskId::Cleanup => match g.cleanup_task {
                Some(cl) => {
                    let (cl2, out) = step_succeed_own_task(cl, instance_id, true);
                    (TaskGraphSpec { cleanup_task: Some(cl2), ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
        },
        GraphOp::Fail { tid, instance_id, err } => match tid {
            GraphTaskId::Regular(idx) => {
                if idx < g.tasks.len() {
                    let (t2, out) = step_fail_task(g.tasks[idx as int], instance_id, err);
                    (TaskGraphSpec { tasks: g.tasks.update(idx as int, t2), ..g }, out)
                } else {
                    (g, OpOutcome::NoOp)
                }
            }
            GraphTaskId::Commit => match g.commit_task {
                Some(ct) => {
                    let (ct2, out) = step_fail_task(ct, instance_id, err);
                    (TaskGraphSpec { commit_task: Some(ct2), ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
            GraphTaskId::Cleanup => match g.cleanup_task {
                Some(cl) => {
                    let (cl2, out) = step_fail_task(cl, instance_id, err);
                    (TaskGraphSpec { cleanup_task: Some(cl2), ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
        },
        GraphOp::ForceRemove { tid, instance_id } => match tid {
            GraphTaskId::Regular(idx) => {
                if idx < g.tasks.len() {
                    let (t2, out) = step_force_remove_task(g.tasks[idx as int], instance_id);
                    (TaskGraphSpec { tasks: g.tasks.update(idx as int, t2), ..g }, out)
                } else {
                    (g, OpOutcome::NoOp)
                }
            }
            GraphTaskId::Commit => match g.commit_task {
                Some(ct) => {
                    let (ct2, out) = step_force_remove_task(ct, instance_id);
                    (TaskGraphSpec { commit_task: Some(ct2), ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
            GraphTaskId::Cleanup => match g.cleanup_task {
                Some(cl) => {
                    let (cl2, out) = step_force_remove_task(cl, instance_id);
                    (TaskGraphSpec { cleanup_task: Some(cl2), ..g }, out)
                }
                None => (g, OpOutcome::NoOp),
            },
        },
        GraphOp::CancelNonTerminalGraph => {
            // Exact match to `TaskGraph::cancel_non_terminal` (`cache/task.rs:80-87`):
            // cancels all regular tasks and the commit task, never the cleanup task.
            let new_tasks = Seq::new(g.tasks.len(), |i: int| step_cancel_task(g.tasks[i]));
            let new_commit = match g.commit_task {
                Some(ct) => Some(step_cancel_task(ct)),
                None => None,
            };
            (
                TaskGraphSpec {
                    tasks: new_tasks,
                    commit_task: new_commit,
                    ..g
                },
                OpOutcome::Accepted,
            )
        }
    }
}

/// Core single-step inductive preservation & C6 safety lemma for the entire `TaskGraph`.
pub proof fn lemma_graph_step_preserves_c6(
    dag: DagSpec,
    g: TaskGraphSpec,
    op: GraphOp,
)
    requires
        g.inv(dag),
    ensures
        ({
            let (g2, out) = graph_step(dag, g, op);
            &&& g2.inv(dag)
            // 1. Every task (regular, commit, cleanup) makes a valid C6 transition,
            //    and its `success_count` never decreases and stays <= 1.
            &&& forall|tid: GraphTaskId| match (#[trigger] g.get_task(tid), g2.get_task(tid)) {
                (Some(t1), Some(t2)) =>
                    valid_task_transition(t1.state, t2.state)
                    && t1.success_count <= t2.success_count
                    && t2.success_count <= 1
                    // Terminal tasks never gain a new live instance!
                    && (t1.state.is_terminal_spec() ==> t2.live.subset_of(t1.live)),
                (None, None) => true,
                _ => false,
            }
            // 2. Terminal tasks reject every Register attempt with TaskAlreadyTerminated.
            &&& match op {
                GraphOp::Register { tid, .. } => match g.get_task(tid) {
                    Some(t1) if t1.state.is_terminal_spec() =>
                        out == OpOutcome::Rejected(CacheError::StaleState(
                            StaleStateError::TaskAlreadyTerminated(t1.state)
                        ))
                        && g2 == g,
                    _ => true,
                },
                _ => true,
            }
            // 3. Unknown instances are rejected on Succeed (when outputs_len_ok) and Fail.
            &&& match op {
                GraphOp::Succeed { tid, instance_id, outputs_len_ok } => match g.get_task(tid) {
                    Some(t1) if (match tid { GraphTaskId::Regular(_) => outputs_len_ok, _ => true })
                        && !t1.live.contains(instance_id) =>
                        out == OpOutcome::Rejected(CacheError::StaleState(
                            StaleStateError::InvalidTaskInstanceId
                        ))
                        && g2.get_task(tid) == Some(t1),
                    _ => true,
                },
                GraphOp::Fail { tid, instance_id, .. } => match g.get_task(tid) {
                    Some(t1) if !t1.live.contains(instance_id) =>
                        out == OpOutcome::Rejected(CacheError::StaleState(
                            StaleStateError::InvalidTaskInstanceId
                        ))
                        && g2.get_task(tid) == Some(t1),
                    _ => true,
                },
                _ => true,
            }
            // 4. An accepted Succeed on task `tid` increments `success_count(tid)` from 0 to 1,
            //    and never increments any other task's `success_count`.
            &&& match op {
                GraphOp::Succeed { tid, .. } => (
                    (out == OpOutcome::Accepted ==> match (g.get_task(tid), g2.get_task(tid)) {
                        (Some(t1), Some(t2)) =>
                            t1.success_count == 0
                            && t2.success_count == 1
                            && t2.state == TaskState::Succeeded,
                        _ => false,
                    })
                    && (out != OpOutcome::Accepted ==> forall|other: GraphTaskId|
                        match (#[trigger] g.get_task(other), g2.get_task(other)) {
                            (Some(t1), Some(t2)) => t1.success_count == t2.success_count,
                            _ => true,
                        }
                    )
                ),
                _ => forall|other: GraphTaskId| match (#[trigger] g.get_task(other), g2.get_task(other)) {
                    (Some(t1), Some(t2)) => t1.success_count == t2.success_count,
                    _ => true,
                },
            }
            // 5. `TaskGraphCorrupted` (child `num_unfinished_parents == 0`) is unreachable
            //    when a regular task succeeds!
            &&& match op {
                GraphOp::Succeed { tid: GraphTaskId::Regular(idx), .. } if out == OpOutcome::Accepted =>
                    forall|k: int| 0 <= k < dag.children[idx as int].len() ==>
                        g.tasks[dag.children[idx as int][k] as int].num_unfinished_parents >= 1,
                _ => true,
            }
            // 6. `InternalError::TaskNotRunning` is unreachable on Succeed and Fail!
            &&& out != OpOutcome::Rejected(CacheError::Internal(InternalError::TaskNotRunning))
        }),
{
    let (g2, out) = graph_step(dag, g, op);
    match op {
        GraphOp::Register { tid, instance_id } => {
            match tid {
                GraphTaskId::Regular(idx) => {
                    if idx < g.tasks.len() {
                        assert forall|i: int| 0 <= i < g2.tasks.len() implies (
                            g2.tasks[i].c6_task_inv()
                            && g2.tasks[i].live.subset_of(g2.allocated_ids)
                            && g2.tasks[i].num_unfinished_parents == count_unfinished_parents(dag.parents[i], g2.tasks)
                            && (g2.tasks[i].num_unfinished_parents > 0 ==> (
                                g2.tasks[i].state == TaskState::Pending || g2.tasks[i].state == TaskState::Cancelled
                            ))
                        ) by {
                            lemma_count_preserved_if_succeeded_unchanged(dag.parents[i], g.tasks, g2.tasks);
                        };
                        if g.tasks[idx as int].state.is_terminal_spec() {
                            assert(g2.tasks =~= g.tasks);
                            assert(g2 == g);
                        }
                    }
                }
                GraphTaskId::Commit => {
                    if let Some(ct) = g.commit_task {
                        if ct.state.is_terminal_spec() {
                            assert(g2 == g);
                        }
                    }
                }
                GraphTaskId::Cleanup => {
                    if let Some(cl) = g.cleanup_task {
                        if cl.state.is_terminal_spec() {
                            assert(g2 == g);
                        }
                    }
                }
            }
        }
        GraphOp::Succeed { tid, instance_id, outputs_len_ok } => {
            match tid {
                GraphTaskId::Regular(idx) => {
                    if idx < g.tasks.len() {
                        let t1 = g.tasks[idx as int];
                        let (t2, out_own) = step_succeed_own_task(t1, instance_id, outputs_len_ok);
                        if out_own == OpOutcome::Accepted {
                            assert(t1.state == TaskState::Running);
                            assert(t1.live.contains(instance_id));
                            assert(t1.success_count == 0);
                            assert(t2.state == TaskState::Succeeded);
                            assert(t2.success_count == 1);

                            assert forall|i: int| 0 <= i < g2.tasks.len() implies (
                                g2.tasks[i].c6_task_inv()
                                && g2.tasks[i].live.subset_of(g2.allocated_ids)
                                && g2.tasks[i].num_unfinished_parents == count_unfinished_parents(dag.parents[i], g2.tasks)
                                && (g2.tasks[i].num_unfinished_parents > 0 ==> (
                                    g2.tasks[i].state == TaskState::Pending || g2.tasks[i].state == TaskState::Cancelled
                                ))
                                && valid_task_transition(g.tasks[i].state, g2.tasks[i].state)
                            ) by {
                                if i == idx as int {
                                    assert(!dag.parents[i].contains(idx)) by {
                                        if dag.parents[i].contains(idx) {
                                            let k = choose|k: int| 0 <= k < dag.parents[i].len() && dag.parents[i][k] == idx;
                                            assert(dag.parents[i][k] < i);
                                        }
                                    };
                                    lemma_count_unchanged_if_not_parent(dag.parents[i], g.tasks, g2.tasks, idx);
                                    assert(valid_task_transition(g.tasks[i].state, g2.tasks[i].state));
                                } else if dag.children[idx as int].contains(i as nat) {
                                    assert(dag.parents[i].contains(idx));
                                    lemma_count_decrements_by_one_on_parent_success(dag.parents[i], g.tasks, g2.tasks, idx);
                                    assert(g.tasks[i].num_unfinished_parents >= 1);
                                    // Because g.tasks[i].num_unfinished_parents >= 1, g.tasks[i].state is Pending or Cancelled!
                                    assert(g.tasks[i].state == TaskState::Pending || g.tasks[i].state == TaskState::Cancelled);
                                    // Therefore, if !is_terminal(), g.tasks[i].state MUST be Pending,
                                    // so setting state = Ready is strictly `Pending -> Ready`!
                                    assert(valid_task_transition(g.tasks[i].state, g2.tasks[i].state));
                                } else {
                                    assert(!dag.parents[i].contains(idx));
                                    lemma_count_unchanged_if_not_parent(dag.parents[i], g.tasks, g2.tasks, idx);
                                    assert(g2.tasks[i] == g.tasks[i]);
                                }
                            };
                            assert forall|k: int| 0 <= k < dag.children[idx as int].len() implies
                                g.tasks[dag.children[idx as int][k] as int].num_unfinished_parents >= 1
                            by {
                                let v = dag.children[idx as int][k];
                                assert(dag.children[idx as int].contains(v));
                                assert(dag.parents[v as int].contains(idx));
                                lemma_count_decrements_by_one_on_parent_success(dag.parents[v as int], g.tasks, g2.tasks, idx);
                            };
                        } else {
                            assert forall|i: int| 0 <= i < g2.tasks.len() implies (
                                g2.tasks[i].c6_task_inv()
                                && g2.tasks[i].live.subset_of(g2.allocated_ids)
                                && g2.tasks[i].num_unfinished_parents == count_unfinished_parents(dag.parents[i], g2.tasks)
                                && (g2.tasks[i].num_unfinished_parents > 0 ==> (
                                    g2.tasks[i].state == TaskState::Pending || g2.tasks[i].state == TaskState::Cancelled
                                ))
                            ) by {
                                lemma_count_preserved_if_succeeded_unchanged(dag.parents[i], g.tasks, g2.tasks);
                            };
                        }
                    }
                }
                GraphTaskId::Commit => {}
                GraphTaskId::Cleanup => {}
            }
        }
        GraphOp::Fail { tid, instance_id, err } => {
            match tid {
                GraphTaskId::Regular(idx) => {
                    if idx < g.tasks.len() {
                        assert forall|i: int| 0 <= i < g2.tasks.len() implies (
                            g2.tasks[i].c6_task_inv()
                            && g2.tasks[i].live.subset_of(g2.allocated_ids)
                            && g2.tasks[i].num_unfinished_parents == count_unfinished_parents(dag.parents[i], g2.tasks)
                            && (g2.tasks[i].num_unfinished_parents > 0 ==> (
                                g2.tasks[i].state == TaskState::Pending || g2.tasks[i].state == TaskState::Cancelled
                            ))
                        ) by {
                            lemma_count_preserved_if_succeeded_unchanged(dag.parents[i], g.tasks, g2.tasks);
                        };
                    }
                }
                GraphTaskId::Commit => {}
                GraphTaskId::Cleanup => {}
            }
        }
        GraphOp::ForceRemove { tid, instance_id } => {
            match tid {
                GraphTaskId::Regular(idx) => {
                    if idx < g.tasks.len() {
                        assert forall|i: int| 0 <= i < g2.tasks.len() implies (
                            g2.tasks[i].c6_task_inv()
                            && g2.tasks[i].live.subset_of(g2.allocated_ids)
                            && g2.tasks[i].num_unfinished_parents == count_unfinished_parents(dag.parents[i], g2.tasks)
                            && (g2.tasks[i].num_unfinished_parents > 0 ==> (
                                g2.tasks[i].state == TaskState::Pending || g2.tasks[i].state == TaskState::Cancelled
                            ))
                        ) by {
                            lemma_count_preserved_if_succeeded_unchanged(dag.parents[i], g.tasks, g2.tasks);
                        };
                    }
                }
                GraphTaskId::Commit => {}
                GraphTaskId::Cleanup => {}
            }
        }
        GraphOp::CancelNonTerminalGraph => {
            assert forall|i: int| 0 <= i < g2.tasks.len() implies (
                (#[trigger] g2.tasks[i]).c6_task_inv()
                && g2.tasks[i].live.subset_of(g2.allocated_ids)
                && g2.tasks[i].num_unfinished_parents == count_unfinished_parents(#[trigger] dag.parents[i], g2.tasks)
                && (g2.tasks[i].num_unfinished_parents > 0 ==> (
                    g2.tasks[i].state == TaskState::Pending || g2.tasks[i].state == TaskState::Cancelled
                ))
            ) by {
                lemma_count_preserved_if_succeeded_unchanged(dag.parents[i], g.tasks, g2.tasks);
            };
        }
    }
}

/// Multi-step execution of a sequence of `GraphOp`s starting from `g0`.
pub open spec fn run_trace(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
) -> TaskGraphSpec
    decreases ops.len(),
{
    if ops.len() == 0 {
        g0
    } else {
        let prev = run_trace(dag, g0, ops.drop_last());
        graph_step(dag, prev, ops.last()).0
    }
}

/// State reached at prefix length `k` (`0 <= k <= ops.len()`).
pub open spec fn trace_state(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
    k: int,
) -> TaskGraphSpec
    recommends
        0 <= k <= ops.len(),
{
    run_trace(dag, g0, ops.take(k))
}

/// Outcome of step `k` (`0 <= k < ops.len()`).
pub open spec fn trace_outcome(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
    k: int,
) -> OpOutcome
    recommends
        0 <= k < ops.len(),
{
    graph_step(dag, trace_state(dag, g0, ops, k), ops[k]).1
}

/// Helper: `trace_state(k + 1)` equals the post-state of step `k`.
pub proof fn lemma_trace_step_unfold(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
    k: int,
)
    requires
        0 <= k < ops.len(),
    ensures
        trace_state(dag, g0, ops, k + 1) == graph_step(dag, trace_state(dag, g0, ops, k), ops[k]).0,
{
    let prefix = ops.take(k + 1);
    assert(prefix.len() == k + 1);
    assert(prefix.drop_last() =~= ops.take(k));
    assert(prefix.last() == ops[k]);
}

/// Inductively prove `inv` holds at every step `0 <= k <= ops.len()`.
pub proof fn lemma_trace_inv(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
    k: int,
)
    requires
        g0.inv(dag),
        0 <= k <= ops.len(),
    ensures
        trace_state(dag, g0, ops, k).inv(dag),
    decreases k,
{
    if k == 0 {
        assert(ops.take(0) =~= Seq::<GraphOp>::empty());
    } else {
        lemma_trace_inv(dag, g0, ops, k - 1);
        lemma_trace_step_unfold(dag, g0, ops, k - 1);
        lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, k - 1), ops[k - 1]);
    }
}

/// Prove monotonicity of `success_count` and permanent absorption of terminal states
/// across any interval `i <= j <= ops.len()`.
pub proof fn lemma_trace_monotonicity_and_terminal_permanence(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
    i: int,
    j: int,
    tid: GraphTaskId,
)
    requires
        g0.inv(dag),
        0 <= i <= j <= ops.len(),
    ensures
        match (trace_state(dag, g0, ops, i).get_task(tid), trace_state(dag, g0, ops, j).get_task(tid)) {
            (Some(ti), Some(tj)) =>
                ti.success_count <= tj.success_count
                && tj.success_count <= 1
                && (ti.state.is_terminal_spec() ==> (
                    tj.state == ti.state
                    && tj.live.subset_of(ti.live)
                )),
            (None, None) => true,
            _ => false,
        },
    decreases j - i,
{
    lemma_trace_inv(dag, g0, ops, i);
    if i < j {
        lemma_trace_monotonicity_and_terminal_permanence(dag, g0, ops, i, j - 1, tid);
        lemma_trace_inv(dag, g0, ops, j - 1);
        lemma_trace_step_unfold(dag, g0, ops, j - 1);
        lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, j - 1), ops[j - 1]);
        let si = trace_state(dag, g0, ops, i);
        let sp = trace_state(dag, g0, ops, j - 1);
        let sj = trace_state(dag, g0, ops, j);
        match (si.get_task(tid), sp.get_task(tid), sj.get_task(tid)) {
            (Some(ti), Some(tp), Some(tj)) => {
                if ti.state.is_terminal_spec() {
                    lemma_terminal_is_absorbing(tp.state, tj.state);
                    assert(tj.live.subset_of(ti.live));
                }
            }
            _ => {}
        }
    }
}

/// C6 Sub-Theorem 1: Every step in any trace executes a valid C6 task state transition
/// for every task (regular, commit, cleanup).
pub proof fn theorem_c6_1_valid_transitions(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
)
    requires
        g0.inv(dag),
    ensures
        forall|k: int, tid: GraphTaskId| 0 <= k < ops.len() ==>
            match (#[trigger] trace_state(dag, g0, ops, k).get_task(tid), trace_state(dag, g0, ops, k + 1).get_task(tid)) {
                (Some(t1), Some(t2)) => valid_task_transition(t1.state, t2.state),
                (None, None) => true,
                _ => false,
            },
{
    assert forall|k: int, tid: GraphTaskId| 0 <= k < ops.len() implies
        match (#[trigger] trace_state(dag, g0, ops, k).get_task(tid), trace_state(dag, g0, ops, k + 1).get_task(tid)) {
            (Some(t1), Some(t2)) => valid_task_transition(t1.state, t2.state),
            (None, None) => true,
            _ => false,
        }
    by {
        lemma_trace_inv(dag, g0, ops, k);
        lemma_trace_step_unfold(dag, g0, ops, k);
        lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, k), ops[k]);
    };
}

/// C6 Sub-Theorem 2: Terminal states are permanently absorbing, live instance sets never grow
/// after termination, and every subsequent `Register` on a terminal task is rejected.
pub proof fn theorem_c6_2_terminal_permanence_and_no_new_instance(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
)
    requires
        g0.inv(dag),
    ensures
        forall|i: int, j: int, tid: GraphTaskId| 0 <= i <= j <= ops.len() ==>
            match (#[trigger] trace_state(dag, g0, ops, i).get_task(tid), #[trigger] trace_state(dag, g0, ops, j).get_task(tid)) {
                (Some(ti), Some(tj)) if ti.state.is_terminal_spec() =>
                    tj.state == ti.state && tj.live.subset_of(ti.live),
                _ => true,
            },
        forall|i: int, k: int| 0 <= i <= k < ops.len() ==>
            match #[trigger] ops[k] {
                GraphOp::Register { tid, .. } => match (#[trigger] trace_state(dag, g0, ops, i)).get_task(tid) {
                    Some(ti) if ti.state.is_terminal_spec() =>
                        trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                            CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(ti.state))
                        ),
                    _ => true,
                },
                _ => true,
            },
{
    assert forall|i: int, j: int, tid: GraphTaskId| 0 <= i <= j <= ops.len() implies
        match (#[trigger] trace_state(dag, g0, ops, i).get_task(tid), #[trigger] trace_state(dag, g0, ops, j).get_task(tid)) {
            (Some(ti), Some(tj)) if ti.state.is_terminal_spec() =>
                tj.state == ti.state && tj.live.subset_of(ti.live),
            _ => true,
        }
    by {
        lemma_trace_monotonicity_and_terminal_permanence(dag, g0, ops, i, j, tid);
    };

    assert forall|i: int, k: int| 0 <= i <= k < ops.len() implies
        match #[trigger] ops[k] {
            GraphOp::Register { tid, .. } => match (#[trigger] trace_state(dag, g0, ops, i)).get_task(tid) {
                Some(ti) if ti.state.is_terminal_spec() =>
                    trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                        CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(ti.state))
                    ),
                _ => true,
            },
            _ => true,
        }
    by {
        match ops[k] {
            GraphOp::Register { tid, .. } => {
                lemma_trace_monotonicity_and_terminal_permanence(dag, g0, ops, i, k, tid);
                lemma_trace_inv(dag, g0, ops, k);
                lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, k), ops[k]);
            }
            _ => {}
        }
    };
}

/// C6 Sub-Theorem 3: Unknown instances are always rejected on `Succeed` (with valid output count)
/// and `Fail` with `StaleStateError::InvalidTaskInstanceId`.
pub proof fn theorem_c6_3_unknown_instance_rejected(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
)
    requires
        g0.inv(dag),
    ensures
        forall|k: int| 0 <= k < ops.len() ==>
            match #[trigger] ops[k] {
                GraphOp::Succeed { tid, instance_id: id, outputs_len_ok: ok_len } =>
                    (match tid { GraphTaskId::Regular(_) => ok_len, _ => true }) ==>
                    match trace_state(dag, g0, ops, k).get_task(tid) {
                        Some(tk) if !tk.live.contains(id) =>
                            trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                                CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)
                            ),
                        _ => true,
                    },
                GraphOp::Fail { tid, instance_id: id, .. } =>
                    match trace_state(dag, g0, ops, k).get_task(tid) {
                        Some(tk) if !tk.live.contains(id) =>
                            trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                                CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)
                            ),
                        _ => true,
                    },
                _ => true,
            },
{
    assert forall|k: int| 0 <= k < ops.len() implies
        match #[trigger] ops[k] {
            GraphOp::Succeed { tid, instance_id: id, outputs_len_ok: ok_len } =>
                (match tid { GraphTaskId::Regular(_) => ok_len, _ => true }) ==>
                match trace_state(dag, g0, ops, k).get_task(tid) {
                    Some(tk) if !tk.live.contains(id) =>
                        trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                            CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)
                        ),
                    _ => true,
                },
            GraphOp::Fail { tid, instance_id: id, .. } =>
                match trace_state(dag, g0, ops, k).get_task(tid) {
                    Some(tk) if !tk.live.contains(id) =>
                        trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                            CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)
                        ),
                    _ => true,
                },
            _ => true,
        }
    by {
        lemma_trace_inv(dag, g0, ops, k);
        lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, k), ops[k]);
    };
}

/// C6 Sub-Theorem 4: One success per task — no two distinct steps `i < j` can both be
/// accepted `Succeed` operations on the same task `tid`.
pub proof fn theorem_c6_4_one_success_per_task(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
)
    requires
        g0.inv(dag),
    ensures
        forall|i: int, j: int| 0 <= i < j < ops.len() ==>
            match (#[trigger] ops[i], #[trigger] ops[j]) {
                (GraphOp::Succeed { tid: tid1, .. }, GraphOp::Succeed { tid: tid2, .. }) =>
                    (tid1 == tid2 && trace_outcome(dag, g0, ops, i) == OpOutcome::Accepted)
                        ==> trace_outcome(dag, g0, ops, j) != OpOutcome::Accepted,
                _ => true,
            },
{
    assert forall|i: int, j: int| 0 <= i < j < ops.len() implies
        match (#[trigger] ops[i], #[trigger] ops[j]) {
            (GraphOp::Succeed { tid: tid1, .. }, GraphOp::Succeed { tid: tid2, .. }) =>
                (tid1 == tid2 && trace_outcome(dag, g0, ops, i) == OpOutcome::Accepted)
                    ==> trace_outcome(dag, g0, ops, j) != OpOutcome::Accepted,
            _ => true,
        }
    by {
        match (ops[i], ops[j]) {
            (GraphOp::Succeed { tid: tid1, .. }, GraphOp::Succeed { tid: tid2, .. }) => {
                if tid1 == tid2 && trace_outcome(dag, g0, ops, i) == OpOutcome::Accepted {
                    lemma_trace_inv(dag, g0, ops, i);
                    lemma_trace_step_unfold(dag, g0, ops, i);
                    lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, i), ops[i]);
                    lemma_trace_monotonicity_and_terminal_permanence(dag, g0, ops, i + 1, j, tid1);
                    lemma_trace_inv(dag, g0, ops, j);
                    lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, j), ops[j]);
                }
            }
            _ => {}
        }
    };
}

/// C6 Sub-Theorem 5: `InternalError::TaskNotRunning` is unreachable across all traces.
pub proof fn theorem_c6_5_no_internal_task_not_running(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
)
    requires
        g0.inv(dag),
    ensures
        forall|k: int| 0 <= k < ops.len() ==>
            #[trigger] trace_outcome(dag, g0, ops, k) != OpOutcome::Rejected(CacheError::Internal(InternalError::TaskNotRunning)),
{
    assert forall|k: int| 0 <= k < ops.len() implies
        #[trigger] trace_outcome(dag, g0, ops, k) != OpOutcome::Rejected(CacheError::Internal(InternalError::TaskNotRunning))
    by {
        lemma_trace_inv(dag, g0, ops, k);
        lemma_graph_step_preserves_c6(dag, trace_state(dag, g0, ops, k), ops[k]);
    };
}

/// MAIN THEOREM (Invariant C6 — Full Multi-Task DAG & Trace Safety):
///
/// Combines Sub-Theorems 1–5 for any well-formed task graph initialized via `init_task_graph`
/// and ANY arbitrary finite sequence `ops` of concurrent (linearized) operations on regular,
/// commit, and cleanup tasks.
pub proof fn theorem_c6_holds_for_all_traces(
    dag: DagSpec,
    max_instances: Seq<nat>,
    max_retries: Seq<nat>,
    commit_policy: Option<(nat, nat)>,
    cleanup_policy: Option<(nat, nat)>,
    ops: Seq<GraphOp>,
)
    requires
        dag.wf(),
        max_instances.len() == dag.num_tasks,
        max_retries.len() == dag.num_tasks,
    ensures
        ({
            let g0 = init_task_graph(dag, max_instances, max_retries, commit_policy, cleanup_policy);
            &&& forall|k: int, tid: GraphTaskId| 0 <= k < ops.len() ==>
                match (#[trigger] trace_state(dag, g0, ops, k).get_task(tid), trace_state(dag, g0, ops, k + 1).get_task(tid)) {
                    (Some(t1), Some(t2)) => valid_task_transition(t1.state, t2.state),
                    (None, None) => true,
                    _ => false,
                }
            &&& forall|i: int, j: int, tid: GraphTaskId| 0 <= i <= j <= ops.len() ==>
                match (#[trigger] trace_state(dag, g0, ops, i).get_task(tid), #[trigger] trace_state(dag, g0, ops, j).get_task(tid)) {
                    (Some(ti), Some(tj)) if ti.state.is_terminal_spec() =>
                        tj.state == ti.state && tj.live.subset_of(ti.live),
                    _ => true,
                }
            &&& forall|i: int, k: int| 0 <= i <= k < ops.len() ==>
                match #[trigger] ops[k] {
                    GraphOp::Register { tid, .. } => match (#[trigger] trace_state(dag, g0, ops, i)).get_task(tid) {
                        Some(ti) if ti.state.is_terminal_spec() =>
                            trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                                CacheError::StaleState(StaleStateError::TaskAlreadyTerminated(ti.state))
                            ),
                        _ => true,
                    },
                    _ => true,
                }
            &&& forall|k: int| 0 <= k < ops.len() ==>
                match #[trigger] ops[k] {
                    GraphOp::Succeed { tid, instance_id: id, outputs_len_ok: ok_len } =>
                        (match tid { GraphTaskId::Regular(_) => ok_len, _ => true }) ==>
                        match trace_state(dag, g0, ops, k).get_task(tid) {
                            Some(tk) if !tk.live.contains(id) =>
                                trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                                    CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)
                                ),
                            _ => true,
                        },
                    GraphOp::Fail { tid, instance_id: id, .. } =>
                        match trace_state(dag, g0, ops, k).get_task(tid) {
                            Some(tk) if !tk.live.contains(id) =>
                                trace_outcome(dag, g0, ops, k) == OpOutcome::Rejected(
                                    CacheError::StaleState(StaleStateError::InvalidTaskInstanceId)
                                ),
                            _ => true,
                        },
                    _ => true,
                }
            &&& forall|i: int, j: int| 0 <= i < j < ops.len() ==>
                match (#[trigger] ops[i], #[trigger] ops[j]) {
                    (GraphOp::Succeed { tid: tid1, .. }, GraphOp::Succeed { tid: tid2, .. }) =>
                        (tid1 == tid2 && trace_outcome(dag, g0, ops, i) == OpOutcome::Accepted)
                            ==> trace_outcome(dag, g0, ops, j) != OpOutcome::Accepted,
                    _ => true,
                }
            &&& forall|k: int| 0 <= k < ops.len() ==>
                #[trigger] trace_outcome(dag, g0, ops, k) != OpOutcome::Rejected(CacheError::Internal(InternalError::TaskNotRunning))
        }),
{
    let g0 = init_task_graph(dag, max_instances, max_retries, commit_policy, cleanup_policy);
    lemma_init_task_graph_inv(dag, max_instances, max_retries, commit_policy, cleanup_policy);
    theorem_c6_1_valid_transitions(dag, g0, ops);
    theorem_c6_2_terminal_permanence_and_no_new_instance(dag, g0, ops);
    theorem_c6_3_unknown_instance_rejected(dag, g0, ops);
    theorem_c6_4_one_success_per_task(dag, g0, ops);
    theorem_c6_5_no_internal_task_not_running(dag, g0, ops);
}

/// Strengthened Corollary (Fresh Instance IDs, matching `TaskInstancePoolHandle`'s `AtomicU64`):
/// If every accepted `Register` allocates a fresh `instance_id` not in `allocated_ids`, then once
/// an instance ID is removed from a task (via Succeed, Fail, or ForceRemove), it can NEVER
/// re-appear in that task's live pool at any later step, so every late/duplicate report for that
/// instance ID is permanently rejected with `InvalidTaskInstanceId`.
pub open spec fn trace_uses_fresh_instance_ids(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
) -> bool {
    forall|k: int| 0 <= k < ops.len() ==>
        match #[trigger] ops[k] {
            GraphOp::Register { tid: _, instance_id: id } =>
                !trace_state(dag, g0, ops, k).allocated_ids.contains(id),
            _ => true,
        }
}

pub proof fn lemma_allocated_ids_monotonic(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
    i: int,
    j: int,
)
    requires
        g0.inv(dag),
        0 <= i <= j <= ops.len(),
    ensures
        trace_state(dag, g0, ops, i).allocated_ids.subset_of(trace_state(dag, g0, ops, j).allocated_ids),
    decreases j - i,
{
    if i < j {
        lemma_allocated_ids_monotonic(dag, g0, ops, i, j - 1);
        lemma_trace_step_unfold(dag, g0, ops, j - 1);
    }
}

pub proof fn lemma_step_preserves_absent_id(
    dag: DagSpec,
    g: TaskGraphSpec,
    op: GraphOp,
    tid: GraphTaskId,
    id: TaskInstanceId,
)
    requires
        g.inv(dag),
        match g.get_task(tid) {
            Some(t) => !t.live.contains(id),
            None => false,
        },
        match op {
            GraphOp::Register { tid: _, instance_id } => instance_id != id,
            _ => true,
        },
    ensures
        match graph_step(dag, g, op).0.get_task(tid) {
            Some(t2) => !t2.live.contains(id),
            None => false,
        },
{
    let (g2, _) = graph_step(dag, g, op);
    match op {
        GraphOp::Register { tid: op_tid, instance_id } => {
            assert(instance_id != id);
        }
        GraphOp::Succeed { .. } => {}
        GraphOp::Fail { .. } => {}
        GraphOp::ForceRemove { .. } => {}
        GraphOp::CancelNonTerminalGraph => {}
    }
}

pub proof fn theorem_removed_instance_never_reenters(
    dag: DagSpec,
    g0: TaskGraphSpec,
    ops: Seq<GraphOp>,
    i: int,
    j: int,
    tid: GraphTaskId,
    id: TaskInstanceId,
)
    requires
        g0.inv(dag),
        trace_uses_fresh_instance_ids(dag, g0, ops),
        0 <= i <= j <= ops.len(),
        trace_state(dag, g0, ops, i).allocated_ids.contains(id),
        match trace_state(dag, g0, ops, i).get_task(tid) {
            Some(ti) => !ti.live.contains(id),
            None => false,
        },
    ensures
        match trace_state(dag, g0, ops, j).get_task(tid) {
            Some(tj) => !tj.live.contains(id),
            None => false,
        },
    decreases j - i,
{
    if i < j {
        theorem_removed_instance_never_reenters(dag, g0, ops, i, j - 1, tid, id);
        lemma_allocated_ids_monotonic(dag, g0, ops, i, j - 1);
        lemma_trace_inv(dag, g0, ops, j - 1);
        lemma_trace_step_unfold(dag, g0, ops, j - 1);
        let sp = trace_state(dag, g0, ops, j - 1);
        assert(sp.allocated_ids.contains(id));
        match ops[j - 1] {
            GraphOp::Register { tid: _, instance_id: op_id } => {
                assert(!sp.allocated_ids.contains(op_id));
                assert(op_id != id);
            }
            _ => {}
        }
        lemma_step_preserves_absent_id(dag, sp, ops[j - 1], tid, id);
    }
}

fn main() {}

} // verus!
