//! A derivation far longer than a small thread's stack could hold one frame
//! per event, carried through every walk of this crate inside that thread.

use std::thread;

use gandr_theory_cell_complexes::CellAlphabet as _;
use gandr_theory_cell_complexes::CellStore;
use gandr_theory_cell_complexes_tools::Toy;
use gandr_theory_cell_complexes_tools::ToyAlphabet;
use gandr_theory_cell_complexes_tools::toy_cell;
use gandr_theory_coherent_resolutions::CellApp;
use gandr_theory_deep_inference::CausalDepth;
use gandr_theory_deep_inference::EventCount;
use gandr_theory_deep_inference::WebVertex;
use gandr_theory_deep_inference::WebVertexCount;
use gandr_theory_deep_inference::causal_web;
use gandr_theory_deep_inference::event_order;
use gandr_theory_deep_inference::normalize_certified;
use gandr_theory_deep_inference::project_flow;

/// The events in the chain, an even number so the chain returns to its peak.
/// Every event fires at the root, so every one depends on every earlier one
/// and the causal order is one chain this long.
const CHAIN: usize = 2_048;

/// The stack the walks run on. Every call frame holds at least a return
/// address and a frame pointer, sixteen bytes, so one frame per event would
/// need twice this stack before any frame holds a local.
const STACK: usize = 16 * 1_024;

#[test]
fn a_deep_derivation_is_ordered_normalized_and_dropped_on_a_small_stack()
{
    // Two cells toggling the root between `Succ(Zero)` and `Add(Zero, Zero)`:
    // the term stays three nodes deep while the derivation grows, so the walks
    // over events are what the stack is asked to hold.
    let mut store = CellStore::new();
    let grow = store.insert(toy_cell(
        Toy::succ(Toy::zero()),
        Toy::add(Toy::zero(), Toy::zero()),
    ));
    let shrink = store.insert(toy_cell(
        Toy::add(Toy::zero(), Toy::zero()),
        Toy::succ(Toy::zero()),
    ));
    let peak = Toy::succ(Toy::zero());
    let path: Vec<CellApp<ToyAlphabet>> = [grow, shrink]
        .into_iter()
        .cycle()
        .take(CHAIN)
        .map(|cell| CellApp {
            cell,
            at: ToyAlphabet::root_position(),
        })
        .collect();
    let walks = thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let order = event_order(&store, &peak, &path).expect("the chain fires step by step");
            assert_eq!(
                EventCount::from(CHAIN),
                order.event_count(),
                "one event per step"
            );
            let witness =
                normalize_certified(&store, &peak, &peak, &path).expect("the chain replays");
            assert_eq!(
                CausalDepth::from(CHAIN),
                witness.replay_plan().critical_path(),
                "every step depends on the one before, so the plan is one level per step"
            );
            let flow = project_flow(&store, &peak, &path).expect("the chain projects to a flow");
            assert_eq!(
                CHAIN,
                flow.labels.len(),
                "the flow labels one vertex per event"
            );
            let web = causal_web(&order);
            assert_eq!(
                WebVertexCount::from(CHAIN),
                web.vertex_count(),
                "the web has one vertex per event"
            );
            let last = WebVertex::from(CHAIN.saturating_sub(1_usize));
            assert!(
                bool::from(web.precedes.contains(WebVertex::from(0_usize), last)),
                "and the first event precedes the last, through the whole chain"
            );
            drop(web);
            drop(flow);
            drop(witness);
            drop(order);
            drop(path);
            drop(peak);
            drop(store);
        })
        .expect("the small-stack thread starts");
    walks
        .join()
        .expect("every walk and every drop completes on the small stack");
}
