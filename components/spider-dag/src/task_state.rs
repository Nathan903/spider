//! The state machine of one task: its state, its live instances and its retries.

use std::collections::HashSet;

use vstd::prelude::*;

verus! {

broadcast use vstd::std_specs::hash::group_hash_axioms;

/// Enum for all possible states of a task.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum TaskState {
    Pending,
    Ready,
    Running,
    Succeeded,
    Failed(String),
    Cancelled,
}

impl TaskState {
    /// # Returns
    ///
    /// Whether the state is a terminal state: [`TaskState::Succeeded`], [`TaskState::Failed`] or
    /// [`TaskState::Cancelled`].
    pub open spec fn is_terminal_spec(&self) -> bool {
        matches!(self, Self::Succeeded | Self::Failed(..) | Self::Cancelled)
    }

    /// # Returns
    ///
    /// Whether a task can move from `from` to `to`: `Pending -> Ready -> Running`, `Running ->
    /// Ready` when no live instance is left to retry it, `Running -> Succeeded` or `Failed`, and
    /// any non-terminal state to `Cancelled`. No transition leaves a terminal state.
    pub open spec fn is_valid_transition_spec(from: Self, to: Self) -> bool {
        match to {
            Self::Pending => false,
            Self::Ready => matches!(from, Self::Pending | Self::Running),
            Self::Running => matches!(from, Self::Ready),
            Self::Succeeded | Self::Failed(..) => matches!(from, Self::Running),
            Self::Cancelled => !from.is_terminal_spec(),
        }
    }

    /// # Returns
    ///
    /// Whether the state is a terminal state. Terminal states include:
    ///
    /// * [`TaskState::Succeeded`]
    /// * [`TaskState::Failed`]
    /// * [`TaskState::Cancelled`]
    #[must_use]
    pub const fn is_terminal(&self) -> (result: bool)
        ensures
            result == self.is_terminal_spec(),
    {
        matches!(self, Self::Succeeded | Self::Failed(..) | Self::Cancelled)
    }
}

/// Errors returned when a task's state rejects an operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TaskExecutionError {
    /// The task is in a terminal state.
    TaskAlreadyTerminated,

    /// The task is [`TaskState::Pending`], so it cannot run yet.
    TaskNotReady,

    /// The task has as many live instances as its instance limit allows.
    TaskInstanceLimitExceeded,

    /// The task instance is not live.
    InvalidTaskInstanceId,

    /// The task is not [`TaskState::Running`].
    TaskNotRunning,

    /// The task is not [`TaskState::Pending`].
    TaskNotPending,
}

/// The execution state of one task: its [`TaskState`], its live task instances and the retries it
/// has left.
///
/// Every operation keeps [`Self::invariant`] and is a step that [`Self::is_valid_step_spec`]
/// accepts, so:
///
/// * The state only moves along [`TaskState::is_valid_transition_spec`] and never leaves a terminal
///   state. [`Self::succeed_task_instance`] accepts a report only while the task is
///   [`TaskState::Running`] and leaves it [`TaskState::Succeeded`], so a task succeeds at most
///   once.
/// * The number of retries left starts at the task's retry limit and never grows, and each retry
///   that [`Self::fail_task_instance`] grants consumes one. So a task is retried at most its retry
///   limit times.
///
/// The operations are not thread-safe: the caller serializes them, e.g., behind a mutex.
pub struct TaskExecutionState {
    state: TaskState,
    instance_pool: InstancePool,
    retry_counter: RetryCounter,
}

// Verus does not support the derived `PartialEq` of `TaskState` in executable code, so the methods
// below compare states with `matches!` where the original code used `==` and `!=`.
impl TaskExecutionState {
    /// # Returns
    ///
    /// The mathematical state of the task.
    pub closed spec fn state_spec(&self) -> TaskState {
        self.state
    }

    /// # Returns
    ///
    /// The mathematical set of the task's live instance IDs.
    pub closed spec fn live_instances_spec(&self) -> Set<u64> {
        self.instance_pool.instance_ids@
    }

    /// # Returns
    ///
    /// The mathematical maximum number of the task's live instances.
    pub closed spec fn max_num_instances_spec(&self) -> usize {
        self.instance_pool.max_num_instances
    }

    /// # Returns
    ///
    /// The mathematical number of retries the task has left.
    pub closed spec fn num_retries_left_spec(&self) -> usize {
        self.retry_counter.retry_count
    }

    /// # Returns
    ///
    /// Whether the task's execution state is consistent:
    ///
    /// * The task's instance limit is at least 1, and the task has at most that many live
    ///   instances.
    /// * A [`TaskState::Running`] task has a live instance, which will report its outcome or be
    ///   removed.
    /// * A [`TaskState::Pending`] or [`TaskState::Ready`] task has no live instance.
    pub open spec fn invariant(&self) -> bool {
        &&& self.live_instances_spec().finite()
        &&& 1 <= self.max_num_instances_spec()
        &&& self.live_instances_spec().len() <= self.max_num_instances_spec()
        &&& self.state_spec() == TaskState::Running ==> !self.live_instances_spec().is_empty()
        &&& (self.state_spec() == TaskState::Pending || self.state_spec() == TaskState::Ready)
            ==> self.live_instances_spec().is_empty()
    }

    /// # Returns
    ///
    /// Whether one operation can lead from `self` to `next`: the instance limit stays, the number
    /// of retries left never grows, and the state either stays or moves along
    /// [`TaskState::is_valid_transition_spec`].
    pub open spec fn is_valid_step_spec(&self, next: &Self) -> bool {
        &&& next.max_num_instances_spec() == self.max_num_instances_spec()
        &&& next.num_retries_left_spec() <= self.num_retries_left_spec()
        &&& (next.state_spec() == self.state_spec() || TaskState::is_valid_transition_spec(
            self.state_spec(),
            next.state_spec(),
        ))
    }

    /// # Returns
    ///
    /// Whether `next` has the same state, live instances and retries left as `self`.
    pub open spec fn is_unchanged_spec(&self, next: &Self) -> bool {
        &&& next.state_spec() == self.state_spec()
        &&& next.live_instances_spec() == self.live_instances_spec()
        &&& next.num_retries_left_spec() == self.num_retries_left_spec()
    }

    /// # Returns
    ///
    /// What registering a new task instance returns:
    ///
    /// * [`TaskExecutionError::TaskAlreadyTerminated`] if the task is in a terminal state, so a
    ///   terminal task accepts no new instance.
    /// * [`TaskExecutionError::TaskNotReady`] if the task is [`TaskState::Pending`].
    /// * [`TaskExecutionError::TaskInstanceLimitExceeded`] if the task has as many live instances
    ///   as its instance limit allows.
    /// * `Ok(())` otherwise.
    pub open spec fn registration_result_spec(&self) -> Result<(), TaskExecutionError> {
        if self.state_spec().is_terminal_spec() {
            Err(TaskExecutionError::TaskAlreadyTerminated)
        } else if self.state_spec() == TaskState::Pending {
            Err(TaskExecutionError::TaskNotReady)
        } else if self.live_instances_spec().len() >= self.max_num_instances_spec() {
            Err(TaskExecutionError::TaskInstanceLimitExceeded)
        } else {
            Ok(())
        }
    }

    /// Factory function.
    ///
    /// # NOTE
    ///
    /// The `max_num_instances` must be at least 1, otherwise it will be set to 1.
    ///
    /// # Returns
    ///
    /// The execution state of a task with no live instance: [`TaskState::Ready`] if `is_ready`,
    /// otherwise [`TaskState::Pending`].
    #[must_use]
    pub fn new(is_ready: bool, max_num_instances: usize, max_num_retries: usize) -> (result: Self)
        ensures
            result.invariant(),
            result.state_spec() == if is_ready {
                TaskState::Ready
            } else {
                TaskState::Pending
            },
            result.live_instances_spec().is_empty(),
            result.max_num_instances_spec() == if max_num_instances == 0 {
                1
            } else {
                max_num_instances
            },
            result.num_retries_left_spec() == max_num_retries,
    {
        Self {
            state: if is_ready {
                TaskState::Ready
            } else {
                TaskState::Pending
            },
            instance_pool: InstancePool::create(max_num_instances),
            retry_counter: RetryCounter::new(max_num_retries),
        }
    }

    /// # Returns
    ///
    /// The state of the task.
    #[must_use]
    pub const fn state(&self) -> (result: &TaskState)
        ensures
            *result == self.state_spec(),
    {
        &self.state
    }

    /// Ensures that a new task instance can be registered.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    ///
    /// * [`TaskExecutionError::TaskAlreadyTerminated`] if the task is already in a terminal state.
    /// * [`TaskExecutionError::TaskNotReady`] if the task is not yet ready.
    /// * [`TaskExecutionError::TaskInstanceLimitExceeded`] if the number of living task instances
    ///   has reached the upper limit.
    pub fn ensure_registrable(&self) -> (result: Result<(), TaskExecutionError>)
        requires
            self.invariant(),
        ensures
            result == self.registration_result_spec(),
    {
        if self.state.is_terminal() {
            return Err(TaskExecutionError::TaskAlreadyTerminated);
        }
        if !matches!(self.state, TaskState::Ready | TaskState::Running) {
            return Err(TaskExecutionError::TaskNotReady);
        }
        if self.instance_pool.is_full() {
            return Err(TaskExecutionError::TaskInstanceLimitExceeded);
        }
        Ok(())
    }

    /// Registers a new task instance.
    ///
    /// On success, the task instance ID will be added to the live instances, and the task will be
    /// in [`TaskState::Running`] state on return.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    ///
    /// * Forwards [`Self::ensure_registrable`]'s return values on failure.
    pub fn register_task_instance(&mut self, instance_id: u64) -> (result: Result<
        (),
        TaskExecutionError,
    >)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            old(self).is_valid_step_spec(final(self)),
            result == old(self).registration_result_spec(),
            match result {
                Ok(()) => {
                    &&& final(self).state_spec() == TaskState::Running
                    &&& final(self).live_instances_spec()
                        == old(self).live_instances_spec().insert(instance_id)
                    &&& final(self).num_retries_left_spec() == old(self).num_retries_left_spec()
                },
                Err(_) => old(self).is_unchanged_spec(final(self)),
            },
    {
        self.ensure_registrable()?;
        self.instance_pool.add(instance_id);
        self.state = TaskState::Running;
        Ok(())
    }

    /// Marks a task instance as succeeded.
    ///
    /// On success, the task instance ID will be removed from the live instances, and the task will
    /// be in [`TaskState::Succeeded`] state on return.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    ///
    /// * [`TaskExecutionError::InvalidTaskInstanceId`] if the task instance is not live. This can
    ///   happen if the task instance has already been removed due to timeout.
    /// * [`TaskExecutionError::TaskAlreadyTerminated`] if the task is already in a terminal state.
    /// * [`TaskExecutionError::TaskNotRunning`] if the task is not in the running state, which
    ///   [`Self::invariant`] rules out.
    pub fn succeed_task_instance(&mut self, instance_id: u64) -> (result: Result<
        (),
        TaskExecutionError,
    >)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            old(self).is_valid_step_spec(final(self)),
            final(self).num_retries_left_spec() == old(self).num_retries_left_spec(),
            match result {
                Ok(()) => {
                    &&& old(self).live_instances_spec().contains(instance_id)
                    &&& old(self).state_spec() == TaskState::Running
                    &&& final(self).state_spec() == TaskState::Succeeded
                    &&& final(self).live_instances_spec()
                        == old(self).live_instances_spec().remove(instance_id)
                },
                Err(TaskExecutionError::InvalidTaskInstanceId) => {
                    &&& !old(self).live_instances_spec().contains(instance_id)
                    &&& old(self).is_unchanged_spec(final(self))
                },
                Err(TaskExecutionError::TaskAlreadyTerminated) => {
                    &&& old(self).live_instances_spec().contains(instance_id)
                    &&& old(self).state_spec().is_terminal_spec()
                    &&& final(self).state_spec() == old(self).state_spec()
                    &&& final(self).live_instances_spec()
                        == old(self).live_instances_spec().remove(instance_id)
                },
                Err(_) => false,
            },
    {
        if !self.instance_pool.remove(instance_id) {
            return Err(TaskExecutionError::InvalidTaskInstanceId);
        }
        if self.state.is_terminal() {
            return Err(TaskExecutionError::TaskAlreadyTerminated);
        }
        if !matches!(self.state, TaskState::Running) {
            return Err(TaskExecutionError::TaskNotRunning);
        }
        self.state = TaskState::Succeeded;
        Ok(())
    }

    /// Marks a task instance as failed.
    ///
    /// On success, the task instance ID will be removed from the live instances, and the task will
    /// be in one of the following states on return:
    ///
    /// * [`TaskState::Ready`] if the task is still eligible for retry, and there is no other living
    ///   task instance.
    /// * [`TaskState::Running`] if the task is still eligible for retry, and there are still other
    ///   living task instances.
    /// * [`TaskState::Failed`] with `error_message` if the task is no longer eligible for retry.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    ///
    /// * [`TaskExecutionError::InvalidTaskInstanceId`] if the task instance is not live. This can
    ///   happen if the task instance has already been removed due to timeout.
    /// * [`TaskExecutionError::TaskAlreadyTerminated`] if the task is already in a terminal state.
    /// * [`TaskExecutionError::TaskNotRunning`] if the task is not in the running state, which
    ///   [`Self::invariant`] rules out.
    pub fn fail_task_instance(&mut self, instance_id: u64, error_message: String) -> (result:
        Result<(), TaskExecutionError>)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            old(self).is_valid_step_spec(final(self)),
            match result {
                Ok(()) => {
                    &&& old(self).live_instances_spec().contains(instance_id)
                    &&& old(self).state_spec() == TaskState::Running
                    &&& final(self).live_instances_spec()
                        == old(self).live_instances_spec().remove(instance_id)
                    &&& if old(self).num_retries_left_spec() > 0 {
                        &&& final(self).num_retries_left_spec() + 1
                            == old(self).num_retries_left_spec()
                        &&& final(self).live_instances_spec().is_empty()
                            ==> final(self).state_spec() == TaskState::Ready
                        &&& !final(self).live_instances_spec().is_empty()
                            ==> final(self).state_spec() == TaskState::Running
                    } else {
                        &&& final(self).num_retries_left_spec() == 0
                        &&& final(self).state_spec() == TaskState::Failed(error_message)
                    }
                },
                Err(TaskExecutionError::InvalidTaskInstanceId) => {
                    &&& !old(self).live_instances_spec().contains(instance_id)
                    &&& old(self).is_unchanged_spec(final(self))
                },
                Err(TaskExecutionError::TaskAlreadyTerminated) => {
                    &&& old(self).live_instances_spec().contains(instance_id)
                    &&& old(self).state_spec().is_terminal_spec()
                    &&& final(self).state_spec() == old(self).state_spec()
                    &&& final(self).live_instances_spec()
                        == old(self).live_instances_spec().remove(instance_id)
                    &&& final(self).num_retries_left_spec() == old(self).num_retries_left_spec()
                },
                Err(_) => false,
            },
    {
        if !self.instance_pool.remove(instance_id) {
            return Err(TaskExecutionError::InvalidTaskInstanceId);
        }
        if self.state.is_terminal() {
            return Err(TaskExecutionError::TaskAlreadyTerminated);
        }
        if !matches!(self.state, TaskState::Running) {
            return Err(TaskExecutionError::TaskNotRunning);
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
        Ok(())
    }

    /// Forcefully removes a task instance from the live instances.
    ///
    /// A [`TaskState::Running`] task whose last live instance is removed goes back to
    /// [`TaskState::Ready`].
    ///
    /// # Returns
    ///
    /// Whether the task instance was found and removed.
    pub fn force_remove_task_instance(&mut self, instance_id: u64) -> (existed: bool)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            old(self).is_valid_step_spec(final(self)),
            existed == old(self).live_instances_spec().contains(instance_id),
            final(self).live_instances_spec() == old(self).live_instances_spec().remove(
                instance_id,
            ),
            final(self).state_spec() == if existed && old(self).state_spec() == TaskState::Running
                && final(self).live_instances_spec().is_empty() {
                TaskState::Ready
            } else {
                old(self).state_spec()
            },
            final(self).num_retries_left_spec() == old(self).num_retries_left_spec(),
    {
        let existed = self.instance_pool.remove(instance_id);
        if existed && matches!(self.state, TaskState::Running) && self.instance_pool.is_empty() {
            // NOTE: We should not reset the task state to [`TaskState::Ready`] if:
            // * The task instance is not found in the instance pool, meaning that it may have
            //   already been removed.
            // * The task is not in the running state, meaning that it may already terminate.
            // * The instance pool is not empty, meaning that there are still other living task
            //   instances.
            self.state = TaskState::Ready;
        }
        existed
    }

    /// Cancels the task if it is in a non-terminal state.
    pub fn cancel_non_terminal(&mut self)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            old(self).is_valid_step_spec(final(self)),
            final(self).state_spec() == if old(self).state_spec().is_terminal_spec() {
                old(self).state_spec()
            } else {
                TaskState::Cancelled
            },
            final(self).live_instances_spec() == old(self).live_instances_spec(),
            final(self).num_retries_left_spec() == old(self).num_retries_left_spec(),
    {
        if !self.state.is_terminal() {
            self.state = TaskState::Cancelled;
        }
    }

    /// Moves a [`TaskState::Pending`] task, whose parents have all succeeded, to
    /// [`TaskState::Ready`].
    ///
    /// # Errors
    ///
    /// Returns an error if:
    ///
    /// * [`TaskExecutionError::TaskAlreadyTerminated`] if the task is already in a terminal state.
    /// * [`TaskExecutionError::TaskNotPending`] if the task is [`TaskState::Ready`] or
    ///   [`TaskState::Running`].
    pub fn mark_ready(&mut self) -> (result: Result<(), TaskExecutionError>)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            old(self).is_valid_step_spec(final(self)),
            match result {
                Ok(()) => {
                    &&& old(self).state_spec() == TaskState::Pending
                    &&& final(self).state_spec() == TaskState::Ready
                    &&& final(self).live_instances_spec() == old(self).live_instances_spec()
                    &&& final(self).num_retries_left_spec() == old(self).num_retries_left_spec()
                },
                Err(TaskExecutionError::TaskAlreadyTerminated) => {
                    &&& old(self).state_spec().is_terminal_spec()
                    &&& old(self).is_unchanged_spec(final(self))
                },
                Err(TaskExecutionError::TaskNotPending) => {
                    &&& (old(self).state_spec() == TaskState::Ready || old(self).state_spec()
                        == TaskState::Running)
                    &&& old(self).is_unchanged_spec(final(self))
                },
                Err(_) => false,
            },
    {
        if self.state.is_terminal() {
            return Err(TaskExecutionError::TaskAlreadyTerminated);
        }
        if !matches!(self.state, TaskState::Pending) {
            return Err(TaskExecutionError::TaskNotPending);
        }
        self.state = TaskState::Ready;
        Ok(())
    }
}

/// A pool of task instances that are currently running the same task.
struct InstancePool {
    instance_ids: HashSet<u64>,
    max_num_instances: usize,
}

impl InstancePool {
    /// # Returns
    ///
    /// Whether the pool holds at least one and at most `max_num_instances` instances.
    spec fn invariant(&self) -> bool {
        &&& self.instance_ids@.finite()
        &&& 1 <= self.max_num_instances
        &&& self.instance_ids@.len() <= self.max_num_instances
    }

    /// Factory function.
    ///
    /// # NOTE
    ///
    /// The `max_num_instances` must be at least 1, otherwise it will be set to 1.
    ///
    /// # Returns
    ///
    /// A newly created instance of [`InstancePool`].
    fn create(max_num_instances: usize) -> (result: Self)
        ensures
            result.invariant(),
            result.instance_ids@.is_empty(),
            result.max_num_instances == if max_num_instances == 0 {
                1
            } else {
                max_num_instances
            },
    {
        /*
         * Verus does not support [`std::cmp::max`].
         *
         * Origin Rust:
         * Self {
         *     instance_ids: HashSet::new(),
         *     max_num_instances: max(max_num_instances, 1),
         * }
         */
        Self {
            instance_ids: HashSet::new(),
            max_num_instances: max_num_instances.max(1),
        }
    }

    /// # Returns
    ///
    /// Whether the number of living task instances has reached the upper limit.
    fn is_full(&self) -> (result: bool)
        requires
            self.invariant(),
        ensures
            result == (self.instance_ids@.len() >= self.max_num_instances),
    {
        self.instance_ids.len() >= self.max_num_instances
    }

    /// Adds a task instance to the pool.
    fn add(&mut self, instance_id: u64)
        requires
            old(self).invariant(),
            old(self).instance_ids@.len() < old(self).max_num_instances,
        ensures
            final(self).invariant(),
            final(self).instance_ids@ == old(self).instance_ids@.insert(instance_id),
            final(self).max_num_instances == old(self).max_num_instances,
    {
        self.instance_ids.insert(instance_id);
    }

    /// Removes a task instance from the pool.
    ///
    /// # Returns
    ///
    /// Whether the instance has been found and removed from the pool.
    fn remove(&mut self, instance_id: u64) -> (result: bool)
        requires
            old(self).invariant(),
        ensures
            final(self).invariant(),
            result == old(self).instance_ids@.contains(instance_id),
            final(self).instance_ids@ == old(self).instance_ids@.remove(instance_id),
            !result ==> final(self).instance_ids@ == old(self).instance_ids@,
            final(self).max_num_instances == old(self).max_num_instances,
    {
        let result = self.instance_ids.remove(&instance_id);
        proof {
            if !result {
                assert(self.instance_ids@ =~= old(self).instance_ids@);
            }
        }
        result
    }

    /// # Returns
    ///
    /// Whether the pool is empty (i.e., has no living task instance).
    fn is_empty(&self) -> (result: bool)
        ensures
            result == self.instance_ids@.is_empty(),
    {
        self.instance_ids.is_empty()
    }
}

/// A counter for tracking the number of retries left for a task.
struct RetryCounter {
    retry_count: usize,
}

impl RetryCounter {
    /// Factory function.
    ///
    /// # Returns
    ///
    /// A newly created instance of [`RetryCounter`].
    const fn new(max_num_retries_allowed: usize) -> (result: Self)
        ensures
            result.retry_count == max_num_retries_allowed,
    {
        Self {
            retry_count: max_num_retries_allowed,
        }
    }

    /// # Returns
    ///
    /// The number of retries left before the retry count is exhausted. If 0 is returned, it means
    /// that the retry count is exhausted and no more retries are allowed.
    const fn retry(&mut self) -> (num_retries_left: usize)
        ensures
            num_retries_left == old(self).retry_count,
            final(self).retry_count == if old(self).retry_count == 0 {
                0
            } else {
                (old(self).retry_count - 1) as usize
            },
    {
        if self.retry_count == 0 {
            // In practice, this is possible if the total number of task instances creates are
            // greater than the number of retries allowed.
            return 0;
        }
        let num_retries_left = self.retry_count;
        self.retry_count -= 1;
        num_retries_left
    }
}

} // verus!
