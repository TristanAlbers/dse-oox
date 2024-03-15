use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::{
    cfg::CFGStatement, statistics::Statistics, Options, SymbolTable
};

use super::{
    execution_tree::{ExecutionTree, ExecutionTreeBasedHeuristic}, IdCounter, ProgramCounter
};
use slog::Logger;

pub(super) struct ConcreteExecution {
    pub coverage_tuples: HashMap<(u64, u64), u64>
}

impl ConcreteExecution{
    pub(super) fn new() -> ConcreteExecution{
        ConcreteExecution{
            coverage_tuples: HashMap::new()
        }
    }

    pub(super) fn add_coverage_tuple(&mut self, tuple: (u64, u64)) {
        if let Some(value) = self.coverage_tuples.get(&tuple){
            self.coverage_tuples.insert(tuple, value + 1);
        } else {
            self.coverage_tuples.insert(tuple, 0);
        }
    }
}

impl ExecutionTreeBasedHeuristic for ConcreteExecution{
    fn choice(
        &mut self,
        root: Rc<RefCell<ExecutionTree>>,
        _program: &HashMap<u64, CFGStatement>,
        _flows: &HashMap<u64, Vec<u64>>,
        _st: &SymbolTable,
        _entry_method: &crate::cfg::MethodIdentifier,
        _coverage: &mut HashMap<ProgramCounter, usize>,
        _root_logger: Logger,
        _path_counter: Rc<RefCell<IdCounter<u64>>>,
        _statistics: &mut Statistics,
        _options: &Options,
    ) -> Rc<RefCell<ExecutionTree>> {
        let chosen = ExecutionTree::leafs(root.clone())[0].clone();

        let parent_statement = chosen.borrow().parent().upgrade().unwrap_or_default().borrow().statement();
        let child_statement = chosen.borrow().statement();
        self.add_coverage_tuple((parent_statement, child_statement));

        chosen
    }
}

