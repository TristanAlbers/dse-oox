
use std::cell::RefCell;
use std::collections::HashMap;
use std::ops::Deref;
use std::rc::Rc;
use std::{marker::PhantomData, path::PathBuf};

use libafl::corpus::Corpus;
use libafl::events::EventRestarter;
use libafl::executors::InProcessExecutor;
use libafl::generators::RandPrintablesGenerator;
use libafl::mutators::{havoc_mutations, StdScheduledMutator};
use libafl::observers::RefCellValueObserver;
use libafl::stages::StdMutationalStage;
use libafl::state::{HasCorpus, HasSolutions};
use libafl::Fuzzer;
use libafl::{
    corpus::{InMemoryCorpus, OnDiskCorpus}, 
    events::SimpleEventManager, 
    feedbacks::{CrashFeedback, Feedback}, 
    inputs::BytesInput, 
    monitors::SimpleMonitor, 
    observers::{ObserversTuple,  ValueObserver}, 
    prelude::{Error, ExitKind}, 
    schedulers::QueueScheduler, 
    state::{ State, StdState}, 
    StdFuzzer
};
use libafl_bolts::tuples::tuple_list;
use libafl_bolts::{rands::StdRand, Named};

use crate::exec::heuristics::concrete_execution::ConcreteExecution;


/*
--------------------------------------------------------------------------------
EXECUTOR CREATION
--------------------------------------------------------------------------------
*/

pub type OOXExecutor<'a, H, OT, S> = InProcessExecutor<'a, H, OT, S>;



/*
pub struct OOXExecutor<'a, H, OT, S> {
    observers: OT,
    phantom: PhantomData<S>,
    harness_fn: H,
}

impl<'a, H, OT, S> OOXExecutor<'a, H, OT, S> 
where
    H: FnMut(&S::Input) -> ExitKind + ?Sized,
    OT: ObserversTuple<S>,
    S: HasExecutions + HasSolutions + HasCorpus + State,
{
    pub fn new<EM, OF, Z>(
        harness_fn: &'a mut H,
        observers: OT,
        fuzzer: &mut Z,
        state: &mut S,
        event_mgr: &mut EM,
    ) -> Result<Self, Error>
    where
        Self: Executor<EM, Z, State = S> + HasObservers,
        EM: EventFirer<State = S> + EventRestarter,
        OF: Feedback<S>,
        S: State,
        Z: HasObjective<Objective = OF, State = S>,
    {
        Self::with_timeout_generic(
            tuple_list!(),
            harness_fn,
            observers,
            fuzzer,
            state,
            event_mgr,
            Duration::from_millis(5000),
        )
    }
}

impl<'a, H, OT, EM, Z, S> Executor<EM, Z> for OOXExecutor<'a, H, OT, S>
where
    OT: ObserversTuple<S>,
    S: State + HasExecutions,
    EM: UsesState<State = S>,
    Z: UsesState<State = S>,
{
    fn run_target(
        &mut self,
        fuzzer: &mut Z,
        state: &mut Self::State,
        mgr: &mut EM,
        input: &Self::Input,
    ) -> Result<ExitKind, Error> {
        todo!()
    }
}

impl<'a, H, OT, S> UsesState for OOXExecutor<'a, H, OT, S>
where
    S: State,
{
    type State = S;
}

impl<'a, H, OT, S> UsesObservers for OOXExecutor<'a, H, OT, S>
where
    OT: ObserversTuple<S>,
    S: State,
{
    type Observers = OT;
}

impl<'a, H, OT, S> HasObservers for OOXExecutor<'a, H, OT, S>
where
    S: State,
    OT: ObserversTuple<S>,
{
    fn observers(&self) -> &OT {
        &self.observers
    }

    fn observers_mut(&mut self) -> &mut OT {
        &mut self.observers
    }
}*/

/*
--------------------------------------------------------------------------------
OBSERVER CREATION
--------------------------------------------------------------------------------
*/

// Should maybe be changed to a refcell, but we will see later.
fn oox_observer<'a>(coverage_map: &'a RefCell<HashMap<(u64, u64), u64>>) -> RefCellValueObserver<'a, HashMap<(u64, u64), u64>> {
    let name = "Coverage Observer";
    // let mut coverage_map = ConcreteExecution::new();
    let value = libafl_bolts::ownedref::OwnedRef::Ref(coverage_map);

    let coverage_observer = RefCellValueObserver::new(name, value);
    coverage_observer
}

/*
--------------------------------------------------------------------------------
FEEDBACK CREATION
--------------------------------------------------------------------------------
*/

#[derive(Debug)]
pub struct OOXFeedback<S> {
    old_map: HashMap<(u64, u64), u64>,
    name: String,
    phantom: PhantomData<S>,
}

impl<S> OOXFeedback<S>{
    pub fn from_observer(_observer: &RefCellValueObserver<'_ , HashMap<(u64, u64), u64>>) -> Self{
        Self {
            name: "Coverage Feedbacker".to_owned(),
            phantom: PhantomData,
            old_map: HashMap::new()
        }
    }
}

impl<S> Named for OOXFeedback<S> {
    fn name(&self) -> &str {
        &self.name
    }
}

impl<S> Feedback<S> for OOXFeedback<S>
where
    S: State,
{
    fn is_interesting<EM, OT>(
        &mut self,
        state: &mut S,
        _manager: &mut EM,
        _input: &<S>::Input,
        observers: &OT,
        _exit_kind: &ExitKind,
    ) -> Result<bool, Error>
    where
        EM: libafl::prelude::EventFirer<State = S>,
        OT: ObserversTuple<S>,
    {
        let interesting;
        let observer = observers
        .match_name::<RefCellValueObserver<'_, HashMap<(u64, u64), u64>>>("Coverage Observer")
        .expect("No 'Coverage Observer' observer found");

        let b = observer.get_ref();
        if self.old_map == *b {
            interesting = false;
        } else {
            interesting = true;
        }
        self.old_map = b.clone();

        // state.try_into(); // Personal form of state which can hold interesting inputs or whatever.

        Ok(interesting)
    }

    fn init_state(&mut self, _state: &mut S) -> Result<(), Error> {
        // self.old_map = HashMap::new();
        Ok(())
    }

    fn append_metadata<EM, OT>(
        &mut self,
        _state: &mut S,
        _manager: &mut EM,
        _observers: &OT,
        _testcase: &mut libafl::prelude::Testcase<<S>::Input>,
    ) -> Result<(), Error>
    where
        OT: ObserversTuple<S>,
        EM: libafl::prelude::EventFirer<State = S>,
    {
        Ok(())
    }

    fn discard_metadata(&mut self, _state: &mut S, _input: &<S>::Input) -> Result<(), Error> {
        Ok(())
    }
}

/*
--------------------------------------------------------------------------------
FUZZER LOOP CREATION
--------------------------------------------------------------------------------
*/

pub fn oox_fuzzer(mut harness: impl FnMut(&BytesInput) -> ExitKind, shared_coverage_map: Rc<RefCell<HashMap<(u64, u64), u64>>>) -> bool {
    // Harness
    // let mut harness:  = |input: &BytesInput| {
    //     ExitKind::Ok
    // };

    // Shared value which should be observed
    // let mut shared_coverage_map = shared_coverage_map;

    // Actual observer of shared value
    let observer = oox_observer(shared_coverage_map.as_ref());

    // Feedback
    let mut feedback: OOXFeedback<_> = OOXFeedback::from_observer(&observer);

    // Objective
    let mut objective = CrashFeedback::new();

    // State creation with observer, feedback, input, rng and objective
    let mut state = StdState::new(
        StdRand::with_seed(123),
        InMemoryCorpus::<BytesInput>::new(),
        OnDiskCorpus::new(PathBuf::from("./crashes")).unwrap(),
        &mut feedback,
        &mut objective
    ).unwrap();

    // Simple Monitor
    let mon = SimpleMonitor::new(|s| println!("{s}"));

    // The event manager handle the various events generated during the fuzzing loop
    // such as the notification of the addition of a new item to the corpus
    let mut mgr = SimpleEventManager::new(mon);

    // A queue policy to get testcasess from the corpus
    let scheduler = QueueScheduler::new();

    // A fuzzer with feedbacks and a corpus scheduler
    let mut fuzzer = StdFuzzer::new(scheduler, feedback, objective);

    // Create the executor for an in-process function with just one observer
    let mut executor = OOXExecutor::new(
        &mut harness, 
        tuple_list!(observer), 
        &mut fuzzer, 
        &mut state, 
        &mut mgr,
    )
    .expect("Failed to create the executor");

    // Generator of printable bytearrays of max size 32
    let mut generator = RandPrintablesGenerator::new(32);

    // Generate 8 initial inputs
    state
        .generate_initial_inputs(&mut fuzzer, &mut executor, &mut generator, &mut mgr, 8)
        .expect("Failed to generate the initial corpus");

    // Setup a mutational stage with a basic bytes mutator
    let mutator = StdScheduledMutator::new(havoc_mutations());
    let mut stages = tuple_list!(StdMutationalStage::new(mutator));

    // fuzzer
    //     .fuzz_loop(&mut stages, &mut executor, &mut state, &mut mgr)
    //     .expect("Error in the fuzzing loop");

    
    // mgr.on_restart(&mut state);
    let res = fuzzer.fuzz_one(&mut stages, &mut executor, &mut state, &mut mgr);
    
    state.solutions().count() > 0
}


