use hashbrown::HashSet;

use crate::{
    engine::{Encode, Move, MoveVec, Solitaire},
    utils,
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

    fn on_visit(&mut self, game: &Solitaire, encode: Encode) -> ControlFlow;
    fn on_move_gen(&mut self, move_list: &MoveVec, encode: Encode);

    fn on_do_move(&mut self, game: &Solitaire, m: &Move, encode: Encode, rev_move: &Option<Move>);
    fn on_undo_move(&mut self, m: &Move, encode: Encode);

    fn on_start(&mut self);
    fn on_finish(&mut self, res: &ControlFlow);
}

// it guarantee to return the state of g back into normal state
fn traversing<T: TranspositionTable, C: Callback>(
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

    if !tp.insert(utils::mix(encode)) {
        return ControlFlow::Ok;
    }

    let move_list = game.list_moves::<true>();
    callback.on_move_gen(&move_list, encode);

    for m in move_list {
        if Some(m) == rev_move {
            continue;
        }
        let rev_move = game.get_rev_move(&m);

        callback.on_do_move(game, &m, encode, &rev_move);
        let undo = game.do_move(&m);

        let res = traversing(game, rev_move, tp, callback);

        game.undo_move(&m, &undo);
        callback.on_undo_move(&m, encode);

        if res == ControlFlow::Halt {
            return ControlFlow::Halt;
        }
    }
    ControlFlow::Ok
}

pub type TpTable = HashSet<Encode, nohash_hasher::BuildNoHashHasher<Encode>>;
impl TranspositionTable for TpTable {
    fn clear(&mut self) {
        self.clear();
    }
    fn insert(&mut self, value: Encode) -> bool {
        self.insert(value)
    }
}

pub fn traverse<T: TranspositionTable, C: Callback>(
    game: &mut Solitaire,
    tp: &mut T,
    callback: &mut C,
    rev_move: Option<Move>,
) -> ControlFlow {
    callback.on_start();
    let res = traversing(game, rev_move, tp, callback);
    callback.on_finish(&res);
    res
}
