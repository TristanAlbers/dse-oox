use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use crate::{
    cfg::CFGStatement, statistics::Statistics, Options, SymbolTable
};

use super::{
    execution_tree::{ExecutionTree, ExecutionTreeBasedHeuristic}, IdCounter, ProgramCounter
};
use slog::Logger;
use serde::{Deserialize, Serialize};

// #[derive(Serialize, Deserialize, Debug)]
pub(super) struct ConcreteExecution {
    pub coverage_tuples: Rc<RefCell<HashMap<(u64, u64), u64>>>
}

impl ConcreteExecution{
    pub(super) fn new(coverage_tuples: Rc<RefCell<HashMap<(u64, u64), u64>>>) -> ConcreteExecution{
        Self {
            coverage_tuples
        }
    }

    pub(super) fn add_coverage_tuple(&mut self, tuple: (u64, u64)) {
        let mut map = RefCell::borrow_mut(self.coverage_tuples.deref());
        if let Some(value) = map.clone().get(&tuple){
            map.insert(tuple, value + 1);
        } else {
            map.insert(tuple, 0);
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

