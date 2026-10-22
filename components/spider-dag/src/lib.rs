//! Runtime-free DAG construction and task-readiness primitives.

/// An edge in a task graph.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Edge {
    parent: usize,
    child: usize,
}

impl Edge {
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
    /// Creates an empty DAG.
    ///
    /// # Returns
    ///
    /// An empty DAG.
    #[must_use]
    pub const fn new() -> Self {
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
    pub fn insert_task(&mut self, parent_indices: &[usize]) -> Result<usize, DagError> {
        let child = self.num_tasks;
        let Some(next_num_tasks) = self.num_tasks.checked_add(1) else {
            return Err(DagError::TaskCountOverflow);
        };

        for (position, parent) in parent_indices.iter().copied().enumerate() {
            if parent >= child {
                return Err(DagError::ParentOutOfRange { parent, child });
            }
            if parent_indices[..position].contains(&parent) {
                return Err(DagError::DuplicateParent { parent });
            }
        }

        self.num_tasks = next_num_tasks;
        self.edges.extend(
            parent_indices
                .iter()
                .copied()
                .map(|parent| Edge { parent, child }),
        );
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
        self.edges.iter().all(|edge| {
            let parent_precedes_child = edge.parent < edge.child;
            let child_exists = edge.child < self.num_tasks;
            parent_precedes_child && child_exists
        })
    }
}

/// The result of recording one parent task's successful completion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ParentCompletion {
    AlreadyReady,
    BecameReady,
    StillPending,
}

/// Tracks the unique unfinished parents of one task.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TaskReadiness {
    num_parents: usize,
    num_unfinished_parents: usize,
}

impl TaskReadiness {
    /// Creates readiness state for a task.
    ///
    /// # Returns
    ///
    /// Readiness state with every parent unfinished.
    #[must_use]
    pub const fn new(num_parents: usize) -> Self {
        Self {
            num_parents,
            num_unfinished_parents: num_parents,
        }
    }

    /// Records one unique parent task's successful completion.
    ///
    /// # Returns
    ///
    /// * [`ParentCompletion::AlreadyReady`] if no unfinished parent remains.
    /// * [`ParentCompletion::BecameReady`] if this was the final unfinished parent.
    /// * [`ParentCompletion::StillPending`] if another unfinished parent remains.
    pub const fn parent_completed(&mut self) -> ParentCompletion {
        if self.num_unfinished_parents == 0 {
            return ParentCompletion::AlreadyReady;
        }

        self.num_unfinished_parents -= 1;
        if self.num_unfinished_parents == 0 {
            ParentCompletion::BecameReady
        } else {
            ParentCompletion::StillPending
        }
    }

    /// Restores the initial readiness state.
    pub const fn reset(&mut self) {
        self.num_unfinished_parents = self.num_parents;
    }

    /// # Returns
    ///
    /// Whether all parent tasks have completed successfully.
    #[must_use]
    pub const fn is_ready(&self) -> bool {
        self.num_unfinished_parents == 0
    }

    /// # Returns
    ///
    /// The number of unique parent tasks.
    #[must_use]
    pub const fn num_parents(&self) -> usize {
        self.num_parents
    }

    /// # Returns
    ///
    /// The number of unique parent tasks that have not completed successfully.
    #[must_use]
    pub const fn num_unfinished_parents(&self) -> usize {
        self.num_unfinished_parents
    }
}

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

    #[test]
    fn becomes_ready_after_final_parent() {
        let mut readiness = TaskReadiness::new(3);
        assert!(!readiness.is_ready());
        assert_eq!(readiness.parent_completed(), ParentCompletion::StillPending);
        assert_eq!(readiness.parent_completed(), ParentCompletion::StillPending);
        assert_eq!(readiness.parent_completed(), ParentCompletion::BecameReady);
        assert!(readiness.is_ready());
        assert_eq!(readiness.parent_completed(), ParentCompletion::AlreadyReady);
    }

    #[test]
    fn reset_restores_initial_readiness() {
        let mut input_task = TaskReadiness::new(0);
        assert!(input_task.is_ready());
        assert_eq!(
            input_task.parent_completed(),
            ParentCompletion::AlreadyReady
        );
        input_task.reset();
        assert!(input_task.is_ready());

        let mut dependent_task = TaskReadiness::new(2);
        assert_eq!(
            dependent_task.parent_completed(),
            ParentCompletion::StillPending
        );
        dependent_task.reset();
        assert_eq!(dependent_task.num_unfinished_parents(), 2);
        assert!(!dependent_task.is_ready());
    }
}
