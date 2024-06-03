use lonelybot::{
    engine::{Encode, MoveVec, Solitaire},
    pruning::FullPruner,
    shuffler::default_shuffle,
    traverse::{traverse, Callback, ControlFlow, TpTable},
};

#[derive(Debug, PartialEq, Eq)]
pub enum CycleResult {
    CycleFound,
    NoCycle,
}

struct CycleCallback {
    history: TpTable,
    result: CycleResult,
}

impl Callback for CycleCallback {
    type Pruner = FullPruner;
    fn on_win(&mut self, _: &Solitaire) -> ControlFlow {
        ControlFlow::Ok
    }

    fn on_move_gen(&mut self, _: &MoveVec, e: Encode) -> ControlFlow {
        if !self.history.insert(e) {
            ControlFlow::Halt
        } else {
            ControlFlow::Ok
        }
    }

    fn on_backtrack(&mut self, _: &Solitaire, encode: Encode) -> ControlFlow {
        self.history.remove(&encode);
        ControlFlow::Ok
    }
}

#[test]
#[ignore]
fn test_no_cycle() {
    let mut tp = TpTable::default();
    for seed in 0..1 {
        let deck = default_shuffle(seed);

        tp.clear();

        let mut callback = CycleCallback {
            history: TpTable::default(),
            result: CycleResult::NoCycle,
        };

        let mut g = Solitaire::new(&deck, 3);
        traverse(&mut g, &Default::default(), &mut tp, &mut callback);
        assert_eq!(callback.result, CycleResult::NoCycle);
    }
}
