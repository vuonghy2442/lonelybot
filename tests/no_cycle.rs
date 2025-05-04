use std::num::NonZeroU8;

use lonelybot::{
    moves::MoveMask,
    pruning::FullPruner,
    shuffler::ks_shuffle,
    state::{Encode, Solitaire},
    traverse::{traverse, Callback, Control, TpTable},
};

#[derive(Default)]
struct CycleCallback {
    history: TpTable,
}

impl Callback for CycleCallback {
    type Pruner = FullPruner;
    fn on_win(&mut self, _: &Solitaire) -> Control {
        Control::Ok
    }

    fn on_move_gen(&mut self, _: &MoveMask, e: Encode) -> Control {
        if !self.history.insert(e) {
            Control::Halt
        } else {
            Control::Ok
        }
    }

    fn on_backtrack(&mut self, _: &Solitaire, encode: Encode) -> Control {
        self.history.remove(&encode);
        Control::Ok
    }
}

#[test]
#[ignore]
fn test_no_cycle() {
    let mut tp = TpTable::default();
    for seed in 0..2 {
        let deck = ks_shuffle(seed);

        tp.clear();

        let mut callback = CycleCallback::default();

        let mut g = Solitaire::new(&deck, NonZeroU8::new(3).unwrap());
        let res = traverse(&mut g, Default::default(), &mut tp, &mut callback);
        assert_eq!(res, Control::Ok);
    }
}
