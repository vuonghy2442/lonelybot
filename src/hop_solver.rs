use core::ops::{Add, AddAssign};

use rand::Rng;

use crate::{
    card::Card,
    moves::Move,
    pruning::{FullPruner, Pruner},
    solver::SearchResult,
    state::{Encode, Solitaire},
    tracking::TerminateSignal,
    traverse::{traverse, Callback, Control, TpTable},
};

struct HOPSolverCallback<'a, T: TerminateSignal> {
    sign: &'a T,
    result: SearchResult,
    limit: usize,
    n_visit: usize,
}

impl<T: TerminateSignal> Callback for HOPSolverCallback<'_, T> {
    type Pruner = FullPruner;

    fn on_win(&mut self, _: &Solitaire) -> Control {
        self.result = SearchResult::Solved;
        Control::Halt
    }

    fn on_visit(&mut self, g: &Solitaire, _: Encode) -> Control {
        if g.is_sure_win() {
            self.result = SearchResult::Solved;
            return Control::Halt;
        }

        if self.sign.is_terminated() {
            self.result = SearchResult::Terminated;
            return Control::Halt;
        }

        self.n_visit += 1;
        if self.n_visit > self.limit {
            self.result = SearchResult::Terminated;
            Control::Halt
        } else {
            Control::Ok
        }
    }
}

fn solve_limited<T: TerminateSignal>(
    g: &mut Solitaire,
    prune_info: &FullPruner,
    limit: usize,
    sign: &T,
    tp: &mut TpTable,
) -> SearchResult {
    let mut callback = HOPSolverCallback {
        sign,
        result: SearchResult::Unsolvable,
        limit,
        n_visit: 0,
    };
    tp.clear();
    traverse(g, prune_info, tp, &mut callback);
    callback.result
}

#[derive(Default, Clone, Copy, PartialEq, Eq, Debug)]
pub struct HopResult {
    pub wins: usize,
    pub skips: usize,
    pub played: usize,
    /// The value was computed by evaluating every hidden-card arrangement,
    /// so there is no sampling noise left: re-running the evaluation cannot
    /// change it.
    pub exhaustive: bool,
}

const SURE_WIN: HopResult = HopResult {
    wins: 1,
    skips: 0,
    played: 1,
    exhaustive: true,
};

/// A candidate wins in every arrangement iff its result is exhaustive with
/// no losses and no undecided arrangements.
#[must_use]
pub fn is_sure_win(r: &HopResult) -> bool {
    r.exhaustive && r.played > 0 && r.wins == r.played
}

/// A candidate loses in every arrangement iff its result is exhaustive with
/// no wins and no undecided arrangements.
#[must_use]
pub fn is_sure_lose(r: &HopResult) -> bool {
    r.exhaustive && r.played > 0 && r.wins == 0 && r.skips == 0
}

impl HopResult {
    /// Win-rate estimate with undecided playouts counted as half a win: a
    /// truncated search is evidence neither way, but a proven loss is firm,
    /// so undecided results should neither punish nor fully reward a move.
    #[must_use]
    pub fn rate(&self) -> f64 {
        if self.played == 0 {
            0.5
        } else {
            #[allow(clippy::cast_precision_loss)]
            {
                (2.0 * self.wins as f64 + self.skips as f64) / (2.0 * self.played as f64)
            }
        }
    }
}

impl Add for HopResult {
    type Output = Self;

    fn add(self, rhs: Self) -> Self {
        Self {
            wins: self.wins + rhs.wins,
            skips: self.skips + rhs.skips,
            played: self.played + rhs.played,
            // a default-initialized result is the additive identity, so the
            // empty part must not drag exactness out of a real part: an
            // arm accumulates `default + exact` on its first evaluation
            exhaustive: self.exhaustive || rhs.exhaustive,
        }
    }
}

impl AddAssign for HopResult {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

/// Maximum number of buried cards for which every arrangement is enumerated
/// and solved exactly instead of sampling random determinizations.
/// 5! = 120 arrangements at most.
const MAX_EXACT_BURIED: usize = 5;

/// Advance `cards` to the next lexicographic permutation (by internal card
/// value). Cards are unique, so this visits every permutation exactly once.
fn next_permutation(cards: &mut [Card]) -> bool {
    let n = cards.len();
    if n < 2 {
        return false;
    }

    let val = |c: &Card| c.mask_index();

    let mut i = n - 2;
    loop {
        if val(&cards[i]) < val(&cards[i + 1]) {
            let mut k = n - 1;
            while val(&cards[i]) >= val(&cards[k]) {
                k -= 1;
            }
            cards.swap(i, k);
            cards[i + 1..].reverse();
            return true;
        }
        if i == 0 {
            return false;
        }
        i -= 1;
    }
}

/// Evaluate the candidate move `m` from state `g`.
///
/// When few cards remain buried, every possible arrangement of the hidden
/// cards is enumerated and solved exactly (each with a share of the total
/// visit budget), which makes the returned value exact. Otherwise `n_times`
/// random determinizations are played out, each truncated at `limit` visits.
///
/// # Panics
///
/// Maybe out of memory. Otherwise should not panic
#[allow(clippy::too_many_arguments)]
pub fn hop_solve_game<R: Rng, T: TerminateSignal>(
    g: &Solitaire,
    m: Move,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    budget: usize,
    sign: &T,
    prune_info: &FullPruner,
) -> HopResult {
    // determinization only permutes strictly buried cards, which no
    // generated move depends on, so the candidate must stay legal under
    // every determinization; assert it so a regression fails loudly instead
    // of silently corrupting evaluation samples
    assert!(g.is_valid_move(m), "move {m} is illegal in this state");

    let buried = g.get_hidden().buried_cards();

    if buried.len() <= MAX_EXACT_BURIED {
        // exact branch: the hidden information is small enough to
        // enumerate exhaustively, so the value needs no sampling at all.
        let n_perms = (1..=buried.len()).product::<usize>().max(1);
        let per_limit = (budget.max(limit) / n_perms).max(limit);

        let mut tp = TpTable::default();
        let mut cards = buried;
        // start from the lexicographically smallest arrangement so that the
        // permutation walk below covers every arrangement exactly once
        cards.sort_unstable_by_key(|c| c.mask_index());
        let mut total = HopResult::default();

        loop {
            // the move is evaluated *after* it is made: an arrangement where
            // the position after `m` is solvable counts as a win
            let mut gg = g.clone();
            gg.apply_buried(&cards);
            let (rev_m, (_, extra)) = gg.do_move(m);
            let new_prune_info = FullPruner::update(prune_info, m, rev_m, extra);

            total.played += 1;
            match solve_limited(&mut gg, &new_prune_info, per_limit, sign, &mut tp) {
                SearchResult::Solved => total.wins += 1,
                SearchResult::Terminated => total.skips += 1,
                _ => {}
            }

            if sign.is_terminated() {
                // partial enumeration: no longer exact
                return total;
            }

            if !next_permutation(&mut cards) {
                total.exhaustive = true;
                return total;
            }
        }
    }

    let mut total_wins = 0;
    let mut total_skips = 0;
    let mut total_played = 0;

    let mut tp = TpTable::default();

    for _ in 0..n_times {
        let mut gg = g.clone();
        gg.hidden_shuffle(rng);
        let (rev_m, (_, extra)) = gg.do_move(m);
        let new_prune_info = FullPruner::update(prune_info, m, rev_m, extra);

        let result = solve_limited(&mut gg, &new_prune_info, limit, sign, &mut tp);
        if sign.is_terminated() {
            break;
        }
        total_played += 1;
        match result {
            SearchResult::Solved => total_wins += 1,
            SearchResult::Terminated => total_skips += 1,
            _ => {}
        }
    }
    HopResult {
        wins: total_wins,
        skips: total_skips,
        played: total_played,
        exhaustive: false,
    }
}

extern crate alloc;
use alloc::vec::Vec;

struct RevStatesCallback<'a, R: Rng, T: TerminateSignal> {
    his: Vec<Move>,
    rng: &'a mut R,
    n_times: usize,
    limit: usize,
    sign: &'a T,
    res: Vec<(Vec<Move>, HopResult)>,
}

impl<R: Rng, T: TerminateSignal> Callback for RevStatesCallback<'_, R, T> {
    type Pruner = FullPruner;

    fn on_win(&mut self, _: &Solitaire) -> Control {
        self.res.push((self.his.clone(), SURE_WIN));
        Control::Halt
    }

    fn on_do_move(
        &mut self,
        g: &Solitaire,
        m: Move,
        _: Encode,
        prune_info: &FullPruner,
    ) -> Control {
        self.his.push(m);
        // a candidate is an irreversible move: doing it commits the game, so
        // the search stops there and the evaluation happens separately
        let rev = g.reverse_move(m);
        if rev.is_none() {
            self.res.push((
                self.his.clone(),
                hop_solve_game(
                    g,
                    m,
                    self.rng,
                    self.n_times,
                    self.limit,
                    self.n_times * self.limit,
                    self.sign,
                    prune_info,
                ),
            ));
            Control::Skip
        } else {
            Control::Ok
        }
    }

    fn on_undo_move(&mut self, _: Move, _: Encode, _: &Control) {
        self.his.pop();
    }
}

pub fn list_moves<R: Rng, T: TerminateSignal>(
    g: &mut Solitaire,
    rng: &mut R,
    n_times: usize,
    limit: usize,
    sign: &T,
) -> Vec<(Vec<Move>, HopResult)> {
    let mut callback = RevStatesCallback {
        his: Vec::default(),
        rng,
        n_times,
        limit,
        sign,
        res: Vec::default(),
    };

    let mut tp = TpTable::default();
    traverse(g, &FullPruner::default(), &mut tp, &mut callback);
    callback.res
}
