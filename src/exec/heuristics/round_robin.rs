use std::{cell::RefCell, collections::HashMap, rc::Rc};

use slog::Logger;

use crate::{
    cfg::CFGStatement,
    exec::{IdCounter, State, SymResult},
    statistics::Statistics,
    symbol_table::SymbolTable,
    Options,
};

use super::{
    execution_tree::{sym_exec_execution_tree, ExecutionTree, ExecutionTreeBasedHeuristic},
    min_dist_to_uncovered::MinDist2Uncovered,
    random_path::RandomPath,
    ProgramCounter,
};

struct RoundRobin {
    heuristics: Vec<Box<dyn ExecutionTreeBasedHeuristic>>,
    next_up_heuristic: usize,
}

impl RoundRobin {
    fn new(heuristics: Vec<Box<dyn ExecutionTreeBasedHeuristic>>) -> RoundRobin {
        RoundRobin {
            heuristics,
            next_up_heuristic: 0,
        }
    }
    fn md2u_with_random_path() -> RoundRobin {
        RoundRobin::new(vec![
            Box::new(MinDist2Uncovered::new()),
            Box::new(RandomPath::new()),
        ])
    }
}

impl ExecutionTreeBasedHeuristic for RoundRobin {
    fn choice(
        &mut self,
        root: Rc<RefCell<ExecutionTree>>,
        program: &HashMap<u64, crate::cfg::CFGStatement>,
        flows: &HashMap<u64, Vec<u64>>,
        st: &SymbolTable,
        entry_method: &crate::cfg::MethodIdentifier,
        coverage: &mut HashMap<ProgramCounter, usize>,
        root_logger: Logger,
        path_counter: Rc<RefCell<IdCounter<u64>>>,
        statistics: &mut Statistics,
        options: &Options,
    ) -> Rc<RefCell<ExecutionTree>> {
        let heuristic = self.heuristics[self.next_up_heuristic].as_mut();
        let states_node = heuristic.choice(root, program, flows, st, entry_method, coverage, root_logger, path_counter, statistics, options);

        self.next_up_heuristic = (self.next_up_heuristic + 1) % self.heuristics.len();

        states_node
    }
}

pub(crate) fn sym_exec(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    entry_method: crate::cfg::MethodIdentifier,
    options: &Options,
) -> SymResult {
    let mut heuristic = RoundRobin::md2u_with_random_path();
    sym_exec_execution_tree(
        state,
        program,
        flows,
        st,
        root_logger,
        path_counter,
        statistics,
        entry_method,
        &mut heuristic,
        options,
    )
}
