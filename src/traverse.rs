use hashbrown::HashSet;

use crate::{
    engine::{Encode, Move, MoveVec, Solitaire},
    mixer,
};

pub trait TranspositionTable {
    fn clear(&mut self);
    fn insert(&mut self, value: Encode) -> bool;
}

#[derive(PartialEq, Eq)]
pub enum TraverseResult {
    Halted,
    Skip,
    Ok,
}

pub trait TraverseCallback {
    fn on_win(&mut self, g: &Solitaire, rev_move: &Option<Move>) -> TraverseResult;

    fn on_visit(&mut self, g: &Solitaire, encode: Encode) -> TraverseResult;
    fn on_move_gen(&mut self, m: &MoveVec, encode: Encode);

    fn on_do_move(&mut self, g: &Solitaire, m: &Move, encode: Encode, rev_move: &Option<Move>);
    fn on_undo_move(&mut self, m: &Move, encode: Encode);

    fn on_start(&mut self);
    fn on_finish(&mut self, res: &TraverseResult);
}

// it guarantee to return the state of g back into normal state
fn traverse(
    g: &mut Solitaire,
    rev_move: Option<Move>,
    tp: &mut impl TranspositionTable,

    callback: &mut impl TraverseCallback,
) -> TraverseResult {
    if g.is_win() {
        return callback.on_win(g, &rev_move);
    }

    let encode = g.encode();

    match callback.on_visit(g, encode) {
        TraverseResult::Halted => return TraverseResult::Halted,
        TraverseResult::Skip => return TraverseResult::Skip,
        TraverseResult::Ok => {}
    };

    if !tp.insert(mixer::mix(encode)) {
        return TraverseResult::Ok;
    }

    let move_list = g.list_moves::<true>();
    callback.on_move_gen(&move_list, encode);

    for m in move_list {
        if Some(m) == rev_move {
            continue;
        }
        let rev_move = g.get_rev_move(&m);

        callback.on_do_move(g, &m, encode, &rev_move);
        let undo = g.do_move(&m);

        let res = traverse(g, rev_move, tp, callback);

        g.undo_move(&m, &undo);
        callback.on_undo_move(&m, encode);

        if res == TraverseResult::Halted {
            return TraverseResult::Halted;
        }
    }
    TraverseResult::Ok
}

pub type TpTable = HashSet<Encode, nohash_hasher::BuildNoHashHasher<Encode>>;
impl crate::traverse::TranspositionTable for TpTable {
    fn clear(&mut self) {
        self.clear();
    }
    fn insert(&mut self, value: Encode) -> bool {
        self.insert(value)
    }
}

pub fn traverse_game(
    g: &mut Solitaire,
    tp: &mut impl TranspositionTable,
    callback: &mut impl TraverseCallback,
    rev_move: Option<Move>,
) -> TraverseResult {
    callback.on_start();
    let res = traverse(g, rev_move, tp, callback);
    callback.on_finish(&res);
    res
}
