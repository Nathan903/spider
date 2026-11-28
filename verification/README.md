# Regular-task success counters

Run the proof from the repository root. The driver uses Python 3's standard library and the
Verus distribution on your path. Use `--verus /path/to/verus` to select a binary.

```sh
python3 verification/verify_job_counters.py
```

Verus `0.2026.05.03.8b81855` reports `14 verified, 0 errors` with `--no-cheating`.
The driver takes the three `succeed_task_instance` bodies for the task state transition,
the regular task and the job from the storage sources. Rust macro matching checks their
whole statement structure and passes the actual decrement operands and the reporter's
subtraction into Verus. Changing an unsupported control path stops verification. The
executable proof obligations check the child iterator, the mutex-protected `usize`
subtraction and the value returned from an atomic read-modify-write. [Projection](handler_projection.rs)

## Verified claims

For one initialized regular-task graph, `in_flight_counters` proves the following for
every finite interleaving, including rejected reports, competing reporters and interruptions.

| Stored counter | Tasks it counts while reports are in flight |
| --- | --- |
| Job | Regular tasks still awaiting success, plus successful tasks whose reporter still owes the job decrement |
| Task's parents | Predecessors still awaiting success, plus successful predecessors whose reporter still owes this child a decrement |

`counters_and_unique_reporter` proves both equalities from the original invariant once all
owed updates finish. Every prefix has at most one zero observer. For a nonempty graph,
exactly one report observes zero when all regular tasks have succeeded and their updates
have finished. Its identity is recorded at the atomic decrement that returned one.
A dropped report can leave an update owed even after its future disappears. An initially
empty graph has zero observers. [Theorems](job_counters.rs)

## Scope of the handler proof

The source-to-model projection is a reviewed translation. It treats the task and child
mutexes as exclusive, takes the order of modifications to a single atomic and uses the
old value returned by `fetch_sub`. The permissioned Verus atomic checks that value contract.
The proof makes no use of ordering between different memory locations. Await points and
irrelevant work may pause or interrupt a reporter. The trace permits additional interleavings
when a concrete lock would block one. The theorem is a safety property and supplies no
scheduling or recovery progress guarantee.

The initial state requires one regular TCB per task, duplicate-free reciprocal child and
parent lists, the job counter initialized from the regular-task count, and parent counters
initialized from the lengths of the parent lists. The projection covers the regular success
handlers. Graph construction, task reset, the Tokio implementation and database persistence
are outside the checked code. The proof covers the lifetime of a fixed set of TCBs in which
success is permanent. [Graph builder](../components/spider-core/src/task/task_graph.rs) ·
[Task setup and success](../components/spider-storage/src/cache/task.rs) ·
[Job setup and success](../components/spider-storage/src/cache/job.rs)

A crash can occur **after** the last reporter observes zero and **before** the completion
event is persisted. Recovery of a still-running job builds fresh TCBs and a fresh job
counter. The one-task witness in the proof shows how each such counter can have its own
zero observer for the same job. An interrupted partial mutation triggers the storage
service's shutdown guard. [Guard](../components/spider-storage/src/partial_mutation.rs) ·
[Handler fault and pause tests](../components/spider-storage/src/state/service/hooked_tests.rs)
