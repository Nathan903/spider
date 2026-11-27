# Formal Verification Report: Spider Job Cache Contract Invariant C6 (Verus)

- **Repository:** `https://github.com/y-scope/spider`
- **Verified Commit:** `80882d338e6eda1a4cb886b556891a5f5e3e6ba9`
- **Specification Source:** [ECE1724 formal verification project — Spider development doc (tab `t.qiy3b41rtoe9`)](https://docs.google.com/document/d/1NeIAyhX5sn-jmGpyGGsAAd81QHnPGlxafB5P65jFjM0/edit?tab=t.qiy3b41rtoe9), copied locally to `../ECE1724_formal_verification_project.md`
- **Target Invariant:** Section 7.2, **Invariant C6** (*Task state machine, and one success per task*) & Section 8.5 (*TCB states and checks*)
- **Verifier:** Verus `0.2026.05.03.8b81855` (release, `linux_x86_64`, Rust `1.95.0-x86_64-unknown-linux-gnu`)
- **Verification Outcome:** **`50 verified, 0 errors`** (exit code `0`, `0` `assume`, `0` `admit`, `0` `external_body`, `0` `unsafe`)

---

## 1. Invariant C6 Specification

From Section 7.2 (*Invariants C1–C15*) of the Spider development document:

> **C6 — Task state machine, and one success per task.**  
> `Pending → Ready → Running → Succeeded`, `Failed` or `Cancelled`, with `Running → Ready` on a retry. A terminal task accepts no new instance, and an unknown instance is rejected.  
> - **Holds:** always  
> - **Enforced by:** The task checks under the task's lock: unknown instance, terminal task (§8.5)  
> - **Checked by:** Straggler and duplicate-report tests

From Section 8.5 (*TCB states and checks*):
- Regular tasks initialize to `Pending` if `num_parents > 0`, else `Ready`. Commit and cleanup termination tasks always initialize to `Ready`.
- `Running → Ready` occurs on a retry failure when no other live instance remains, **or** when `TaskInstancePool` force-removes the last live instance of a dead execution manager (`force_remove_task_instance`).
- `cancel_non_terminal` transitions any non-terminal state (`Pending`, `Ready`, `Running`) directly to `Cancelled` while leaving live instance IDs in `instance_pool` (for regular tasks and commit tasks; never the cleanup task).
- Terminal states (`Succeeded`, `Failed(_)`, `Cancelled`) are final.

---

## 2. Files Produced

| Path | Description |
| :--- | :--- |
| `ECE1724_formal_verification_project.md` | Full UTF-8 copy of tab `t.qiy3b41rtoe9` (*Spider development doc*, 2,239 lines / 210,850 chars) |
| `verification/c6_task_state_machine.rs` | Complete Verus formalization and proof of C6 (2,427 lines; executable TCB verification + full DAG/trace safety proof) |
| `verification/run_verus.sh` | Reproducible WSL verification script invoking `verus --triggers-mode silent --time --time-expanded` |
| `verification/C6_VERIFICATION_REPORT.md` | This consolidated verification report and metrics log |

---

## 3. Mapping Between Spider Source Code and Verus Proof

| Spider Source Component | Verified Counterpart in `verification/c6_task_state_machine.rs` |
| :--- | :--- |
| `components/spider-core/src/task/mod.rs` (`TaskState`, `is_terminal`) | `TaskState`, `TaskState::is_terminal_spec`, `TaskState::is_terminal` (lines 67–89) |
| `components/spider-core/src/types/id.rs` (`TaskInstanceId = u64`, `TaskId`) | `TaskInstanceId = u64`, `GraphTaskId::{Regular, Commit, Cleanup}` |
| `components/spider-storage/src/cache/error.rs` (`CacheError`, `StaleStateError`, `InternalError`) | `CacheError`, `StaleStateError`, `InternalError` (lines 93–114) |
| `components/spider-storage/src/cache/task.rs:835-888` (`InstancePool`) | Executable `InstancePool` backed by `std::collections::HashSet<TaskInstanceId>` (`create`, `is_full`, `add`, `remove`, `is_empty`) |
| `components/spider-storage/src/cache/task.rs:891-927` (`RetryCounter`) | Executable `RetryCounter` (`new`, `retry`) |
| `components/spider-storage/src/cache/task.rs:933-1094` (`TaskControlBlockBase`) | Executable `TaskControlBlockBase` (`new_regular`, `new_termination`, `ensure_registrable`, `add_task_instance`, `register_task_instance`, `succeed_task_instance`, `fail_task_instance`, `force_remove_task_instance`, `cancel_non_terminal`, `mark_ready_from_pending`, `is_terminal`) |
| `components/spider-storage/src/cache/task.rs:469-515` (`SharedTaskControlBlock::succeed_task_instance`) | `succeed_regular_precheck` (output-length check before mutation) + `GraphOp::Succeed` child `num_unfinished_parents` decrement and `Pending → Ready` transition |
| `components/spider-storage/src/cache/task.rs:80-87` (`TaskGraph::cancel_non_terminal`) | `GraphOp::CancelNonTerminalGraph` (cancels all regular tasks and commit task, leaves cleanup task untouched) |
| `components/spider-storage/src/task_instance_pool.rs` (dead-EM recovery & monotonic `AtomicU64` IDs) | `GraphOp::ForceRemove` + `trace_uses_fresh_instance_ids` and `theorem_removed_instance_never_reenters` |

---

## 4. Formal Properties & Theorems Proved

### 4.1 State-Machine Transition Relation (`valid_task_transition`)
Allowed edges:
- Stuttering: `s → s`
- `Pending → Ready`
- `Ready → Running`
- `Running → Ready` (retry with no other live instance, or dead-EM `force_remove_task_instance` of last live instance)
- `Running → Succeeded`
- `Running → Failed(_)`
- `Pending | Ready | Running → Cancelled`

Proved meta-lemmas:
- `lemma_terminal_is_absorbing`: any valid transition from a terminal state stays in the exact same state.
- `lemma_forbidden_transitions`: explicitly verifies all 23 forbidden non-stuttering edges (including `Pending → Running/Succeeded/Failed`, `Ready → Pending/Succeeded/Failed`, `Running → Pending`, and every exit from `Succeeded`, `Failed(_)`, or `Cancelled`).

### 4.2 Executable TCB Inductive Invariant (`TaskControlBlockBase::inv`)
Every executable method on `TaskControlBlockBase` preserves:
1. `instance_pool.wf()`: `max_num_instances >= 1` and `instance_pool@.len() <= max_num_instances`.
2. `retry_counter.wf()`: `retry_count <= max_num_retries_allowed`.
3. **Pool–state coupling:**
   - `state == Pending ==> instance_pool@.is_empty()`
   - `state == Ready ==> instance_pool@.is_empty()`
   - `state == Running ==> !instance_pool@.is_empty()`
   - (Terminal states may retain surviving straggler IDs until reported or force-removed.)
4. **One success per task (ghost history):**
   - `success_count <= 1`
   - `state == Succeeded <==> success_count == 1`
   - `state == Succeeded <==> succeeded_by.is_some()`

Key verified consequences on the executable methods:
- **Terminal permanence & no new instance:** `register_task_instance` on any terminal task always returns `Err(StaleState(TaskAlreadyTerminated(state)))` without mutating `state` or `instance_pool`.
- **Unknown instance rejection:** `succeed_task_instance` and `fail_task_instance` for any `id` not in `instance_pool` always return `Err(StaleState(InvalidTaskInstanceId))` without mutating `state`, `instance_pool`, `retry_counter`, or `success_count`.
- **Unreachability of `InternalError::TaskNotRunning`:** proved impossible on any reachable TCB (because `Pending` and `Ready` imply an empty pool, so `remove(id)` returns `false` first).
- **Output-length mismatch safety:** `succeed_regular_precheck` returns `Err(TaskOutputsLengthMismatch)` before touching `instance_pool` or `state`.

### 4.3 Verified Executable Race & Straggler Scenarios
- `verified_scenario_straggler_after_success` (§8.8(a)): two live instances `i1 != i2`; `i1` succeeds; duplicate `succeed(i1)` → `InvalidTaskInstanceId`; straggler `fail(i2)` → `TaskAlreadyTerminated(Succeeded)` (removing `i2`); second report `succeed(i2)` → `InvalidTaskInstanceId`; `register(i3)` → `TaskAlreadyTerminated(Succeeded)`; `success_count == 1`.
- `verified_scenario_terminal_failure_rejects_surviving` (`cache/task.rs` test): `i1` fails with `0` retries → `Failed`; `succeed(i1)` → `InvalidTaskInstanceId`; `succeed(i2)` → `TaskAlreadyTerminated(Failed)`; `register(i3)` → `TaskAlreadyTerminated(Failed)`; `success_count == 0`.
- `verified_scenario_retry_force_remove_and_cancel`: `Pending` rejects registration (`TaskNotReady`), transitions `Pending → Ready → Running → Ready` (retry) `→ Running → Ready` (dead-EM force-remove) `→ Running → Cancelled`; subsequent `force_remove` on `Cancelled` leaves state `Cancelled`.

### 4.4 Full Multi-Task DAG & Arbitrary Trace Safety (`theorem_c6_holds_for_all_traces`)
Models any topologically ordered task DAG `DagSpec` (`u < v` for every edge `(u, v)`, matching `TaskGraph::from_parts` and §8.6) with regular tasks, optional commit task, and optional cleanup task, under any finite trace `ops: Seq<GraphOp>` representing arbitrary linearized concurrent interleavings of RPC handlers, `TaskInstancePool` GC, and `TreeCommitter` applies:

- `lemma_init_task_graph_inv`: initial `TaskGraph` satisfies `TaskGraphSpec::inv(dag)`.
- `lemma_graph_step_preserves_c6`: every single `GraphOp` preserves `inv(dag)`, including the parent-counter coupling invariant (`num_unfinished_parents[v] == count_unfinished_parents(dag.parents[v], tasks)` and `num_unfinished_parents[v] > 0 ==> state ∈ {Pending, Cancelled}`), which proves:
  - `child_tcb.base.state = TaskState::Ready` (`cache/task.rs:513`) is **always** strictly the legal C6 edge `Pending → Ready`.
  - `InternalError::TaskGraphCorrupted` on `child_tcb.num_unfinished_parents == 0` (`cache/task.rs:490`) is **unreachable**.
- `theorem_c6_1_valid_transitions`: every step satisfies `valid_task_transition` on every task.
- `theorem_c6_2_terminal_permanence_and_no_new_instance`: once terminal at step `i`, for all `j >= i` the state never changes, `live` never grows (`tj.live.subset_of(ti.live)`), and every `Register` is rejected with `TaskAlreadyTerminated`.
- `theorem_c6_3_unknown_instance_rejected`: every `Succeed` (with valid output length) or `Fail` for an unknown instance is rejected with `InvalidTaskInstanceId`.
- `theorem_c6_4_one_success_per_task`: no two distinct steps `i < j` can both be accepted `Succeed` operations on the same task `tid`.
- `theorem_c6_5_no_internal_task_not_running`: `InternalError::TaskNotRunning` never occurs in any trace.
- `theorem_c6_holds_for_all_traces`: unified top-level theorem combining all five guarantees.
- `theorem_removed_instance_never_reenters`: strengthened corollary under `trace_uses_fresh_instance_ids` proving any removed instance ID can never re-enter `live`, permanently rejecting late/duplicate reports with `InvalidTaskInstanceId`.

---

## 5. Codebase Audit Findings

1. **Unused public `SharedTaskControlBlock::reset(&self)` breaks C6/C8 if ever called (`components/spider-storage/src/cache/task.rs:555-569`):**
   - `SharedTaskControlBlock::reset` is currently `pub async fn` and unconditionally resets `state` back to `Ready`/`Pending` and clears `instance_pool`, `retry_counter`, `outputs`, and `prepared_children` without checking `is_terminal()`.
   - A workspace-wide search confirmed it has **zero callers** today (so production behavior satisfies C6), but removing it or gating it with `#[cfg(test)]` is recommended to prevent accidental C6/C8 violations.
2. **Additional legal edges in §8.5 / implementation beyond the terse §7.2 table summary:**
   - `Running → Ready` occurs both on retry (`fail_task_instance`) and on dead-EM `force_remove_task_instance` when the last live instance is removed (`cache/task.rs:1074-1086`).
   - `cancel_non_terminal` transitions `Pending → Cancelled` and `Ready → Cancelled` in addition to `Running → Cancelled` (`cache/task.rs:1089-1093`).
   - All of these edges are explicitly modeled and proved safe in `valid_task_transition`.
3. **Uniqueness of `TaskInstanceId`:**
   - C6 holds at the `TaskControlBlockBase` and `TaskGraph` levels **even without** assuming unique `TaskInstanceId`s (`HashSet::insert` is idempotent and preserves `len <= max_num_instances`). Adding uniqueness (via `TaskInstancePoolHandle`'s monotonic `AtomicU64`) yields the stronger non-re-entry property (`theorem_removed_instance_never_reenters`).

---

## 6. How to Reproduce Verification

From Windows PowerShell (with WSL Ubuntu and Verus installed at `$HOME/tools/verus/source/target-verus/release`):

```powershell
wsl -d Ubuntu -- bash /mnt/c/Users/lehar/OneDrive/Documents/ECE1724/spider/verification/run_verus.sh
```

Expected output:

```text
verification results:: 50 verified, 0 errors
```

---

## 7. Verification & Token Usage Statistics

### 7.1 Verus Verification Metrics (Final Clean Run)

| Metric | Value |
| :--- | :--- |
| Verus version | `0.2026.05.03.8b81855` (release, `linux_x86_64`) |
| Rust toolchain | `1.95.0-x86_64-unknown-linux-gnu` |
| Proof file size | 2,427 lines |
| Verified items / errors | **50 verified, 0 errors** (exit code `0`) |
| Unchecked escapes (`assume` / `admit` / `external_body` / `unsafe`) | **0 / 0 / 0 / 0** |
| Total wall time (`verus --time`) | **9,157 ms** |
| Total verification time (`verification-time`) | **8,226 ms** (`vir-time`: 422 ms, `verify-crate-time`: 7,803 ms) |
| SMT solving time (`smt-time`) | **7,331 ms** (`smt-init`: 4 ms, `smt-run`: 7,327 ms; `air-time`: 246 ms) |
| Rust compile time (`rust-time`) | **846 ms** (`init-and-types`: 273 ms, `trait-conflicts`: 49 ms, `compile-time`: 522 ms) |
| Total Z3 `rlimit` | **20,486,884** (`smt-init`: 15,589 + `smt-run`: 20,471,295) |
| Verification iterations (draft → clean pass) | **8 Verus runs** (fixed `Ghost<T>` field & `Result` turbofish annotations, Verus 2026 `final(self)` mut-ref postconditions, `matches!` for `TaskState`, explicit quantifier triggers, modularized trace sub-theorems & `lemma_step_preserves_absent_id` to eliminate Z3 rlimit blowup) |

### 7.2 Agent Session & Token Usage Metrics

Measured directly from the conversation transcript log (`transcript.jsonl`):

| Metric | Through Proof Completion | Including Summary Turn (Before This Report Write) |
| :--- | ---: | ---: |
| Model | Gemini 4 Neon (High) | Gemini 4 Neon (High) |
| Planner turns | 60 | 64 |
| Total tool calls | 121 | 124 |
| Input tokens (non-cached) | 403,126 | 413,938 |
| Output tokens | 108,748 | 113,102 |
| Cache read tokens | 11,151,356 | 12,397,000 |
| Total uncached tokens (input + output) | **511,874** | **527,040** |
| Total tokens incl. cache reads | **11,663,230** | **12,924,040** |
| Wall-clock span (UTC) | `04:36:48Z → 05:09:08Z` (32m 20s; ~20m active after plugin install & clone approval) | `04:36:48Z → 05:15:30Z` |

**Tool call breakdown (124 total calls prior to writing this report):**
- `run_command`: 53
- `read_file`: 22
- `edit_file`: 19
- `update_focus`: 12
- `update_steps`: 6
- `write_file`: 5
- `manage_task`: 4
- `list_plugin_accounts`: 2
- `search_marketplace`: 1
