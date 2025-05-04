use hashbrown::HashSet;

use crate::{
    moves::{Move, MoveMask},
    pruning::Pruner,
    state::{Encode, Solitaire},
    utils::MixHasherBuilder,
};

pub trait TranspositionTable {
    fn clear(&mut self);
    fn insert(&mut self, value: Encode) -> bool;
}

#[derive(PartialEq, Eq, Debug)]
pub enum Control {
    Halt,
    Skip,
    Ok,
}

pub trait Callback {
    type Pruner: Pruner;

    fn on_win(&mut self, game: &Solitaire) -> Control;

    fn on_visit(&mut self, _game: &Solitaire, _encode: Encode) -> Control {
        Control::Ok
    }

    fn on_backtrack(&mut self, _game: &Solitaire, _encode: Encode) -> Control {
        Control::Ok
    }

    fn on_move_gen(&mut self, _move_list: &MoveMask, _encode: Encode) -> Control {
        Control::Ok
    }

    fn on_do_move(
        &mut self,
        _game: &Solitaire,
        _m: Move,
        _encode: Encode,
        _pruner: &Self::Pruner,
    ) -> Control {
        Control::Ok
    }

    fn on_undo_move(&mut self, _m: Move, _encode: Encode, _res: &Control) {}
}

pub type TpTable = HashSet<Encode, MixHasherBuilder>;
impl TranspositionTable for TpTable {
    fn clear(&mut self) {
        self.clear();
    }
    fn insert(&mut self, value: Encode) -> bool {
        self.insert(value)
    }
}

// it guarantee to return the state of g back into normal state
pub fn traverse<T: TranspositionTable, C: Callback>(
    game: &mut Solitaire,
    prune_info: C::Pruner,
    tp: &mut T,
    callback: &mut C,
) -> Control {
    if game.is_win() {
        return callback.on_win(game);
    }

    let encode = game.encode();

    match callback.on_visit(game, encode) {
        Control::Halt => return Control::Halt,
        Control::Skip => return Control::Skip,
        Control::Ok => {}
    }

    if !tp.insert(encode) {
        return Control::Ok;
    }

    let move_list = game
        .gen_moves::<true>()
        .filter(&prune_info.prune_moves(game));

    match callback.on_move_gen(&move_list, encode) {
        Control::Halt => return Control::Halt,
        Control::Skip => return Control::Skip,
        Control::Ok => {}
    }

    let res = move_list.iter_moves(|m| {
        match callback.on_do_move(game, m, encode, &prune_info) {
            Control::Halt => return core::ops::ControlFlow::Break(()),
            Control::Skip => return core::ops::ControlFlow::Continue(()),
            Control::Ok => {}
        }

        let (rev_m, (undo, extra)) = game.do_move(m);
        let new_prune_info = prune_info.update(m, rev_m, extra);

        let res = traverse(game, new_prune_info, tp, callback);

        game.undo_move(m, undo);
        callback.on_undo_move(m, encode, &res);

        if res == Control::Halt {
            core::ops::ControlFlow::Break(())
        } else {
            core::ops::ControlFlow::Continue(())
        }
    });

    if res.is_break() {
        return Control::Halt;
    }

    callback.on_backtrack(game, encode)
}
