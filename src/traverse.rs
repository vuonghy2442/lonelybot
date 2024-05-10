use hashbrown::HashSet;

use crate::{
    engine::{Encode, Move, MoveVec, Solitaire},
    utils::MixHasherBuilder,
};

pub trait TranspositionTable {
    fn clear(&mut self);
    fn insert(&mut self, value: Encode) -> bool;
}

#[derive(PartialEq, Eq)]
pub enum ControlFlow {
    Halt,
    Skip,
    Ok,
}

pub trait Callback {
    fn on_win(&mut self, game: &Solitaire, rev_move: &Option<Move>) -> ControlFlow;

    fn on_visit(&mut self, _game: &Solitaire, _encode: Encode) -> ControlFlow {
        ControlFlow::Ok
    }

    fn on_backtrack(&mut self, _game: &Solitaire, _encode: Encode) -> ControlFlow {
        ControlFlow::Ok
    }

    fn on_move_gen(&mut self, _move_list: &MoveVec, _encode: Encode) -> ControlFlow {
        ControlFlow::Ok
    }

    fn on_do_move(
        &mut self,
        _game: &Solitaire,
        _m: &Move,
        _encode: Encode,
        _rev_move: &Option<Move>,
    ) -> ControlFlow {
        ControlFlow::Ok
    }

    fn on_undo_move(&mut self, _m: &Move, _encode: Encode, _res: &ControlFlow) {}
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
    rev_move: Option<Move>,
    tp: &mut T,
    callback: &mut C,
) -> ControlFlow {
    if game.is_win() {
        return callback.on_win(game, &rev_move);
    }

    let encode = game.encode();

    match callback.on_visit(game, encode) {
        ControlFlow::Halt => return ControlFlow::Halt,
        ControlFlow::Skip => return ControlFlow::Skip,
        ControlFlow::Ok => {}
    };

    if !tp.insert(encode) {
        return ControlFlow::Ok;
    }

    let move_list = game.list_moves::<true>();
    match callback.on_move_gen(&move_list, encode) {
        ControlFlow::Halt => return ControlFlow::Halt,
        ControlFlow::Skip => return ControlFlow::Skip,
        ControlFlow::Ok => {}
    }

    for m in move_list {
        if Some(m) == rev_move {
            continue;
        }
        let rev_move = game.get_rev_move(&m);

        match callback.on_do_move(game, &m, encode, &rev_move) {
            ControlFlow::Halt => return ControlFlow::Halt,
            ControlFlow::Skip => continue,
            ControlFlow::Ok => {}
        }

        let undo = game.do_move(&m);

        let res = traverse(game, rev_move, tp, callback);

        game.undo_move(&m, &undo);
        callback.on_undo_move(&m, encode, &res);

        if res == ControlFlow::Halt {
            return ControlFlow::Halt;
        }
    }

    callback.on_backtrack(game, encode)
}
