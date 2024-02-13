//! Measure reachability starting from a static program method entry
//!

use std::collections::{HashMap, HashSet};

use crate::{
    cfg::{CFGStatement, MethodIdentifier},
    exec::find_entry_for_static_invocation,
    symbol_table::SymbolTable,
};

type ProgramCounter = u64;

/// Computes the set of program points reachable from method.
/// Does not check whether paths are unreachable logically.
pub fn reachability(
    method: MethodIdentifier,
    program: &HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
) -> HashSet<u64> {
    let mut visited_methods = HashSet::from([method.clone()]);
    let mut reachability = HashSet::new();
    let pc = find_entry_for_static_invocation(
        &method.decl_name,
        &method.method_name,
        method.arg_list.into_iter(),
        program,
        st,
    );

    reachability.insert(pc);

    let mut unchecked_methods = methods_called(pc, program, flow);

    while let Some(method) = unchecked_methods.pop() {
        if visited_methods.contains(&method) {
            continue;
        } else {
            let pc = find_entry_for_static_invocation(
                &method.decl_name,
                &method.method_name,
                method.arg_list.clone().into_iter(),
                program,
                st,
            );
            unchecked_methods.extend(methods_called(pc, program, flow));
            visited_methods.insert(method);
        }
    }

    for method in visited_methods {
        let pc = find_entry_for_static_invocation(
            &method.decl_name,
            &method.method_name,
            method.arg_list.into_iter(),
            program,
            st,
        );
        reachability.extend(reachable_pc(pc, flow));
    }

    reachability
}

fn methods_called(
    entry: u64,
    program: &HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
) -> Vec<MethodIdentifier> {
    let mut methods_called = Vec::new();

    let mut stack = vec![entry];
    let mut visited = HashSet::new();

    while let Some(pc) = stack.pop() {
        if visited.contains(&pc) {
            continue;
        } else {
            visited.insert(pc);
        }

        let statement = &program[&pc];
        if let Some(invocation) = statement.is_method_invocation() {
            methods_called.extend(invocation.methods_called());
        }

        stack.extend(flow.get(&pc).unwrap_or(&Vec::new()));
    }

    methods_called
}

fn reachable_pc(entry: u64, flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>) -> HashSet<u64> {
    let mut stack = vec![entry];
    let mut visited = HashSet::new();

    while let Some(pc) = stack.pop() {
        if visited.contains(&pc) {
            continue;
        } else {
            visited.insert(pc);
        }

        stack.extend(flow.get(&pc).unwrap_or(&Vec::new()));
    }

    visited
}

pub fn transitions_set(
    method: MethodIdentifier,
    program: &HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &SymbolTable,
) -> Vec<(u64, u64)> {
    let reachability = reachability(method, program, flow, st);
    let mut transitions: Vec<(u64, u64)> = Vec::new();
    flow.into_iter()
        .filter(|(k, _)| {reachability.contains(k)})
        .for_each(|(k, l)| {l.into_iter().for_each(|v| transitions.push((*k, *v)))} );
    transitions
}
