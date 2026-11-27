// Checked projections of the three production method bodies. The driver passes the
// original Rust tokens to these macros. A change outside the supported shapes
// fails macro matching. Error payloads and operations on outputs are immaterial to
// counters. Every fallible call or await may end the trace at that point.

macro_rules! accept {
    (
        if !self.instance_pool.remove(instance_id) {
            return Err(StaleStateError::InvalidTaskInstanceId.into());
        }
        if self.state.is_terminal() {
            return Err(StaleStateError::TaskAlreadyTerminated(self.state.clone()).into());
        }
        if self.state != TaskState::Running {
            return Err(InternalError::TaskNotRunning.into());
        }
        self.state = TaskState::Succeeded;
        Ok(())
    ) => {
        verus! {
            // Running is disjoint from Succeeded. Other rejection conditions
            // may reject any attempted start and leave all counters unchanged.
            pub(super) open spec fn attempt(
                task: super::Task, reporter: super::Reporter, already_succeeded: bool, eligible: bool,
            ) -> super::Effect {
                if !already_succeeded && eligible { super::Effect::Flip(task, reporter) }
                else { super::Effect::Idle }
            }
        }
    };
}

macro_rules! notify {
    (
        let mut tcb = self.inner.lock().await;
        if task_outputs.len() != tcb.outputs.len() {
            return Err(CacheError::TaskOutputsLengthMismatch {
                expected: tcb.outputs.len(), actual: task_outputs.len(),
            });
        }
        tcb.base.succeed_task_instance(instance_id)?;
        let partial_mutation_guard = new_partial_mutation_guard();
        tcb.write_outputs(task_outputs).await?;
        tcb.prepared_children = prepared_children;
        hooks.hit(HookPoint::TaskSuccessBeforeSuccessorLock, context).await?;
        let result: Result<_, InternalError> = {
            let mut ready_child_indices = Vec::new();
            for child in &tcb.children {
                let mut child_tcb = child.inner.lock().await;
                if child_tcb.num_unfinished_parents == 0 {
                    return Err(InternalError::TaskGraphCorrupted($empty:literal.to_owned(),).into());
                }
                child_tcb.num_unfinished_parents -= $delta:literal;
                if child_tcb.num_unfinished_parents != 0 { continue; }
                if child_tcb.base.state.is_terminal() {
                    return Err(InternalError::TaskGraphCorrupted($terminal:literal.to_owned(),).into());
                }
                child_tcb.base.state = TaskState::Ready;
                ready_child_indices.push(child_tcb.index);
            }
            drop(tcb);
            Ok(ready_child_indices)
        };
        Ok((result?, partial_mutation_guard))
    ) => {
        verus! {
            // One iteration debits the child at the current position. Only the
            // exhausted loop can return to the caller for its job debit.
            pub(super) open spec fn next_update(
                task: super::Task, children: Seq<super::Task>, cursor: int,
            ) -> super::Effect {
                if 0 <= cursor < children.len() { super::Effect::Child(task, children[cursor]) }
                else if cursor == children.len() { super::Effect::Job(task) }
                else { super::Effect::Idle }
            }

            // Check the cursor interpretation against Rust's borrowed Vec iterator,
            // for any TCB representation and any mapping from TCBs to task IDs.
            fn check_child_iteration<C>(
                children: &Vec<C>, Ghost(id): Ghost<spec_fn(C) -> super::Task>,
                Ghost(task): Ghost<super::Task>,
            ) -> (end: Ghost<int>)
                ensures
                    end@ == children.len(),
                    next_update(task, children@.map_values(id), end@) == super::Effect::Job(task),
            {
                let ghost mut cursor = 0int;
                let slice = children.as_slice();
                for child in it: slice.iter()
                    invariant cursor == it.pos, 0 <= it.pos <= children.len(), it.elements == children@,
                {
                    proof {
                        assert(next_update(task, children@.map_values(id), cursor)
                            == super::Effect::Child(task, id(*child)));
                        cursor = cursor + 1;
                    }
                }
                Ghost(cursor)
            }

            pub(crate) open spec fn parent_after(old: int) -> int { old - $delta }
            // Check the machine-word operation at the point protected by the child's mutex.
            pub(crate) fn apply_parent(old: usize) -> (new: usize)
                requires old > 0,
                ensures new == parent_after(old as int),
            {
                let mut remaining = old;
                remaining -= $delta;
                remaining
            }
        }
    };
}

macro_rules! charge {
    (
        let jcb = &self.inner;
        let job = jcb.job_execution_state.read_running().await?;
        let tcb = job.task_graph.get_task_control_block(task_index)
            .ok_or(InternalError::TaskIndexOutOfBound)?;
        let (ready_task_indices, partial_mutation_guard) = tcb.succeed_task_instance(
            task_instance_id, task_outputs, prepared_children,
            || jcb.partial_mutation_guard(TaskId::Index(task_index), task_instance_id),
            &jcb.hooks, || jcb.hook_context(Some(task_instance_id)),
        ).await?;
        jcb.hit_hook(HookPoint::TaskSuccessAfterTcbFlip, Some(task_instance_id)).await?;
        let num_incomplete_tasks =
            job.num_incomplete_tasks.fetch_sub($delta:literal, Ordering::AcqRel) - $offset:literal;
        if !ready_task_indices.is_empty() {
            if num_incomplete_tasks == 0 {
                return Err(InternalError::TaskGraphCorrupted($corrupt:literal.to_owned(),).into());
            }
            job.inbound_queue_sender.send_task_ready(jcb.owner_id, jcb.id, ready_task_indices).await?;
            partial_mutation_guard.disarm();
            return Ok(job.state);
        }
        if num_incomplete_tasks != 0 {
            partial_mutation_guard.disarm();
            return Ok(job.state);
        }
        let outputs = job.task_graph.read_output_payloads().await?;
        let children = job.task_graph.take_prepared_children().await;
        drop(job);
        jcb.hit_hook(HookPoint::TaskSuccessBeforeOutputsCommit, Some(task_instance_id),).await?;
        self.submit_event_and_wait_for_reply(
            TreeEventKind::RegularTasksDone { outputs, children }, Some(partial_mutation_guard),
        ).await
    ) => {
        verus! {
            pub(crate) open spec fn job_after(old: int) -> int { old - $delta }
            pub(crate) open spec fn observed(old: int) -> int { old - $offset }

            // Verus's permissioned atomic supplies the RMW value contract. The
            // projection uses only modification order and the returned old value.
            pub(crate) fn apply_job(
                counter: &vstd::atomic::PAtomicUsize,
                Tracked(perm): Tracked<&mut vstd::atomic::PermissionUsize>,
            ) -> (reported: usize)
                requires old(perm).is_for(*counter), old(perm).value() > 0,
                ensures
                    final(perm).value() == job_after(old(perm).value() as int),
                    reported == observed(old(perm).value() as int),
            {
                let old_count = counter.fetch_sub(Tracked(&mut *perm), $delta);
                old_count - $offset
            }
        }
    };
}
