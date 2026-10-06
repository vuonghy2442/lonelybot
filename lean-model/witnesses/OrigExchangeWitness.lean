import Orig.Fate

/-!
# The exchange witness — the physical twin of w15merge (F1)

The wave-15 exchange claim, in its premiseless form: a position and its
twin-thread exchange (cargo `z` on twin seat `t`, cargo `z'` on twin
seat `t'` — the two thread slices traded, everything else untouched)
have the same verdict.  The old corpus refuted this at a crafted
NON-WF engine state (`Temp/opencode/w15merge.lean`, per
FARM.md:343-360: the win REQUIRES the merge — a run landing on the
other thread's cargo top — while the exchanged state is frozen-dead);
the repair `+hwf` made the row.  `FUTURES-ORIG.md` F1/§7 predicts the
physical side: the crafted shape is unstateable at `WF`, so its
re-derivation here is the boundary record — the same refutation at the
same craft level, as a hand-built wild record pair.

## The craft (WILD STATES — clearly marked, deliberately non-WF)

`xA`/`xB` are direct hand-built `State` records (`State.initial` of a
deal cannot present multi-card face-up threads, and the merge anatomy
forces the braided slice below).  Two deviations from `WF`, both
inherited from the old witness's craft, both never consulted by
`State.step`:

* phantom cards: hearts, diamonds and clubs sit COMPLETE on the
  foundations (`A..K` — heights past every visible card) and spades
  one short (`A..Q`), so the only ascendable card in the world is
  `♠K`, and every red/club tableau card is a stray at a
  foundation-passed rank — a phantom duplicate of a founded card
  (conservation is never claimed; `WF` is never stated);
* the braided helix slice: `xA`'s t-thread is the face-up run
  `[♥5, ♥7, ♠6]` — run head `c₀ = ♥5` over twin seat `♥7` and its
  cargo `♠6`.  A fully legal-edge helix thread is IMPOSSIBLE: the
  landing needs `canSitOn c₀ z'` (`c₀.rank.toIdx + 1 =
  z'.rank.toIdx`) while a legal thread would need `z.rank.toIdx + 1 =
  t.rank.toIdx` and `t.rank.toIdx + 1 = c₀.rank.toIdx`, so with `z'`
  the suit-twin of `z` the three compare to `t.rank.toIdx + 2 ≤
  t.rank.toIdx - 1`.  The merge head therefore sits two ranks off its
  interior edge — `runOK` is a `WF` conjunct only, never a step guard;
  at `WF` the slice does not exist (FUTURES-ORIG §1 dividend (c), the
  braided-walk unstateability).

## The verdicts (all decided below; the census `#eval` battery is at
the file's end)

* `xA` WINS through the merge: `[tabToTab ♥5 (inr ♣6),
  tabToFound ♠K]` — the first move lands the run `[♥5, ♥7, ♠6]`
  ON the bare TWIN-CARGO TOP `♣6` of the OTHER thread
  `[♦7, ♣6]` (both threads merged into one pile, `xA_merge`), the
  vacated pile's automatic reveal flips `♠K` face-up, and the second
  move completes the spade foundation — `isWin`.
* `xB` — `xA` with the two thread slices exchanged, hidden cards
  staying at their piles (the board-only lift of the old
  `exchangeTwinCargo`) — LOSES.  Its whole reachable space is the
  three records `xB` (exactly two first moves), `xB₁` (the mirror
  merge: the run lands on `♣6` again, but the vacated pile's hidden
  card is the POISON `♥2`, not `♠K`), and `xB₂` (the tail-vanish;
  frozen): `♠K` never surfaces, the spade foundation stays at 12,
  `isWin = false` at all three (`xOrbit_closed`, `xOrbit_notWin`).
* hence `xA_xB_notSameFate : ¬ sameFate xA xB`, and the premiseless
  exchange universal `wk_exchange_premiseless_false` — the fence.

## The WF-side expectation (route-map alignment)

Per FUTURES-ORIG §1.8/F1 and the w15circ collapse kit, at `WF` the
merge-shaped cast dies (the found-discipline blocks the phantom
strays, `runOK` blocks the braided slice); the physical exchange rows
are expected to be premise-light (`hwf` and the twinLicense shape).
This file is the boundary record of the premiseless claim; nothing
downstream may cite an unfenced exchange equivalence.

Axioms: witnesses are permitted `[propext, Classical.choice,
Quot.sound]` like the old corpus; this file's rows are all finitary
(decide-level), and the `#print axioms` battery at the end pins the
fence row axiom-clean.

DEDUP NOTE: the search-fact helpers at the bottom (`decSt` — a
private `DecidableEq State` instance — and its probes) are
self-contained re-derivations at this worktree's base `d6b53fb`,
which predates `Orig.Integrity` (842045d); nothing is imported from
it, and the overlap is listed in the report.
-/

namespace OrigExchange

/-! ## Cards and foundations -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The crafted foundations: hearts, diamonds and clubs complete
(`A..K` — heights past every visible card), spades one short
(`A..Q`).  The only ascendable card in the world is `♠K`. -/
private def xFound (s : Suit) : List Card :=
  match s with
  | .heart | .diamond | .club => Rank.all.map (Card.mk s)
  | .spade => (Rank.all.take 12).map (Card.mk s)

/-- The winning foundations: all four suits complete. -/
private def xFoundWin (s : Suit) : List Card :=
  Rank.all.map (Card.mk s)

/-- An occupied, silent guard pile: one hidden card, no face-up. -/
private def gPile (x : Card) : Pile := ⟨[x], []⟩

private def mkState (p : Anchor → Pile) : State :=
  { found := xFound, piles := p, stock := [], waste := [], drawStep := 1 }

private def mkWinState (p : Anchor → Pile) : State :=
  { found := xFoundWin, piles := p, stock := [], waste := [], drawStep := 1 }

/-! ## THE STATES (hand-built wild records) -/

/-- `xA`'s piles: the helix thread `[♥5, ♥7, ♠6]` (braided run head
`♥5`, twin seat `♥7`, cargo `♠6`) over `♠K` hidden at pile 2; the bare
twin thread `[♦7, ♣6]` over the poison `♥2` hidden at pile 4; five
silent guards. -/
private def xPilesA : Anchor → Pile
  | .p0 => gPile (H .nine)
  | .p1 => gPile (D .four)
  | .p2 => ⟨[S .king], [H .five, H .seven, S .six]⟩
  | .p3 => gPile (D .five)
  | .p4 => ⟨[H .two], [D .seven, C .six]⟩
  | .p5 => gPile (D .nine)
  | .p6 => gPile (D .ten)

/-- `xB`'s piles: the two thread slices exchanged, hidden cards at
their piles.  Pile 2 now hosts the bare t'-thread over `♠K`; pile 4
hosts the helix over `♥2`. -/
private def xPilesB : Anchor → Pile
  | .p0 => gPile (H .nine)
  | .p1 => gPile (D .four)
  | .p2 => ⟨[S .king], [D .seven, C .six]⟩
  | .p3 => gPile (D .five)
  | .p4 => ⟨[H .two], [H .five, H .seven, S .six]⟩
  | .p5 => gPile (D .nine)
  | .p6 => gPile (D .ten)

/-- The winning side of the pair. -/
def xA : State := mkState xPilesA

/-- The exchanged side of the pair. -/
def xB : State := mkState xPilesB

/-- The state after the merge at `xA`: both threads in one pile, the
`♠K` reveal done at the vacated pile. -/
def xA₁ : State := mkState fun a =>
  match a with
  | .p2 => ⟨[], [S .king]⟩
  | .p4 => ⟨[H .two], [D .seven, C .six, H .five, H .seven, S .six]⟩
  | .p0 => gPile (H .nine)
  | .p1 => gPile (D .four)
  | .p3 => gPile (D .five)
  | .p5 => gPile (D .nine)
  | .p6 => gPile (D .ten)

/-- The win state of the play (all four foundations complete). -/
def xW : State := mkWinState fun a =>
  match a with
  | .p2 => ⟨[], []⟩
  | .p4 => ⟨[H .two], [D .seven, C .six, H .five, H .seven, S .six]⟩
  | .p0 => gPile (H .nine)
  | .p1 => gPile (D .four)
  | .p3 => gPile (D .five)
  | .p5 => gPile (D .nine)
  | .p6 => gPile (D .ten)

/-- The mirror merge state at `xB`: the run lands on `♣6` again, the
vacated pile's flip is the poison `♥2`. -/
def xB₁ : State := mkState fun a =>
  match a with
  | .p2 => ⟨[S .king], [D .seven, C .six, H .five, H .seven, S .six]⟩
  | .p4 => ⟨[], [H .two]⟩
  | .p0 => gPile (H .nine)
  | .p1 => gPile (D .four)
  | .p3 => gPile (D .five)
  | .p5 => gPile (D .nine)
  | .p6 => gPile (D .ten)

/-- The tail-vanish state at `xB`: the run departs onto `♠6` and
vanishes; the flip is again the poison `♥2`. -/
def xB₂ : State := mkState fun a =>
  match a with
  | .p2 => ⟨[S .king], [D .seven, C .six]⟩
  | .p4 => ⟨[], [H .two]⟩
  | .p0 => gPile (H .nine)
  | .p1 => gPile (D .four)
  | .p3 => gPile (D .five)
  | .p5 => gPile (D .nine)
  | .p6 => gPile (D .ten)

/-- The merge: the braided run `[♥5, ♥7, ♠6]` lands on the bare
twin-cargo top `♣6`. -/
private def mergeMove : Move := .tabToTab (H .five) (.inr (C .six))

/-- The tail-landing: the same run onto the cargo top `♠6`. -/
private def vanishMove : Move := .tabToTab (H .five) (.inr (S .six))

/-- The explicit short winning play through the merge. -/
private def winPlay : List Move := [mergeMove, .tabToFound (S .king)]

/-! ## The A-side verdicts (decide-anchored) -/
/-! ## Step-shape aliases and search helpers (private; DEDUP-marked:
re-derivations local to this file's base, see the header note) -/

private def decSt (s t : State) : Decidable (s = t) :=
  decidable_of_decidable_of_iff (p :=
    (s.found .spade = t.found .spade ∧ s.found .heart = t.found .heart ∧
     s.found .diamond = t.found .diamond ∧ s.found .club = t.found .club ∧
     s.piles .p0 = t.piles .p0 ∧ s.piles .p1 = t.piles .p1 ∧
     s.piles .p2 = t.piles .p2 ∧ s.piles .p3 = t.piles .p3 ∧
     s.piles .p4 = t.piles .p4 ∧ s.piles .p5 = t.piles .p5 ∧
     s.piles .p6 = t.piles .p6 ∧
     s.stock = t.stock ∧ s.waste = t.waste ∧ s.drawStep = t.drawStep))
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        apply State.ext
        · funext σ; cases σ <;> assumption
        · funext a; cases a <;> assumption
        · assumption
        · assumption
        · assumption
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

local instance : DecidableEq State := fun s t => decSt s t

private theorem pileOfTop_some {st : State} {z : Card} {a : Anchor}
    (h : st.pileOfTop z = some a) : st.topOf a = some z := by
  have h' : firstWhere (fun a' => decide (st.topOf a' = some z)) Anchor.all = some a := h
  exact of_decide_eq_true
    (firstWhere_sound (fun a' => decide (st.topOf a' = some z)) h')

private theorem pileHolding_some {st : State} {c : Card} {a : Anchor}
    (h : st.pileHolding c = some a) : c ∈ (st.piles a).faceUp := by
  have h' : firstWhere (fun a' => decide (c ∈ (st.piles a').faceUp)) Anchor.all = some a := h
  exact of_decide_eq_true
    (firstWhere_sound (fun a' => decide (c ∈ (st.piles a').faceUp)) h')

private theorem canPlace_inl_eq (st : State) (c : Card) (a : Anchor) :
    st.canPlace c (.inl a) = ((st.piles a).isEmpty && decide (c.rank = .king)) := rfl

private theorem canPlace_inr_eq (st : State) (c z : Card) :
    st.canPlace c (.inr z) = (match st.pileOfTop z with
      | some _ => canSitOn c z | none => false) := rfl

private theorem step_draw_eq (st : State) : st.step .draw = st.stepDraw := rfl

private theorem step_w2f_eq (st : State) (c : Card) :
    st.step (.wasteToFound c) =
      (if st.wasteIs c && st.nextUp c then
        match st.waste with
        | _ :: ws => some { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws }
        | [] => none
      else none) := rfl

private theorem step_w2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.wasteToTab c b) =
      (if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none) := rfl

private theorem step_t2f_eq (st : State) (c : Card) :
    st.step (.tabToFound c) =
      (if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a =>
            some { st.setFound c.suit (st.found c.suit ++ [c]) with
                     piles := fun a' =>
                       if a' = a then
                         Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                       else st.piles a' }
      else none) := rfl

private theorem step_f2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.foundToTab c b) =
      (match st.foundTop c.suit with
      | some c' =>
          if decide (c' = c) && st.canPlace c b then
            some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
          else none
      | none => none) := rfl

private theorem step_t2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.tabToTab c b) =
      (match st.pileHolding c with
      | none => none
      | some a =>
          if st.canPlace c b then
            match fromCard c (st.piles a).faceUp with
            | [] => none
            | run =>
                some ((st.setPile a (Pile.afterRunRemoved (st.piles a)
                  (below c (st.piles a).faceUp))).putRun run b)
          else none) := rfl

/-- The win NEEDS the merge first: at `xA` itself the `♠K` pin is
still hidden — the pile-to-foundation arm is dead there.  [axioms:
none.] -/
theorem xA_pin_buried : xA.step (.tabToFound (S .king)) = none := by decide

/-- The merge at `xA`: the run `[♥5, ♥7, ♠6]` lands ON the bare
twin-cargo top `♣6` of the `[♦7, ♣6]` thread — both threads merged in
one pile — and the vacated pile's flip reveals `♠K`.  The last
conjunct records the pre-merge cargo top.  [axioms: none — decide.] -/
theorem xA_merge : xA.step mergeMove = some xA₁ ∧
    (xA₁.piles Anchor.p4).faceUp = [D .seven, C .six, H .five, H .seven, S .six] ∧
    (xA₁.piles Anchor.p2).faceUp = [S .king] ∧
    (xA.piles Anchor.p4).faceUp = [D .seven, C .six] := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- `xA`'s play runs to the win.  [axioms: none — decide.] -/
theorem xA_win_data : xA.run winPlay = some xW ∧ xW.isWin = true := by
  refine ⟨by decide, by decide⟩

/-- **VERDICT: `xA` is winnable — through the merge.**  The play is
`[merge, tabToFound ♠K]`: the merge is ON the path — its vacated-pile
flip is the reveal that arms the win.  [axioms: none.] -/
theorem xA_win : WinFrom xA :=
  ⟨winPlay, xW, xA_win_data.1, xA_win_data.2⟩

/-! ## The B-side: the three-state enumeration -/

/-- The B-step records, verified concretely.  [axioms: none — each by
`decide` through the local `DecidableEq State` re-derivation below.] -/
theorem xB_copy_step :
    xB.step (Move.tabToTab (H .five) (Sum.inr (C .six))) = some xB₁ := by decide
theorem xB_vanish_step :
    xB.step (Move.tabToTab (H .five) (Sum.inr (S .six))) = some xB₂ := by decide
theorem xB₁_vanish_step :
    xB₁.step (Move.tabToTab (H .five) (Sum.inr (S .six))) = some xB₂ := by decide

/-- The poison data: through the whole orbit the `♠K` pin stays
hidden at pile 2, and the exchange moved the vacated pile's flip to
`♥2` — never `♠K`.  [axioms: none.] -/
theorem xB_poison : (xB.piles Anchor.p2).hidden = [S .king] ∧
    (xB₁.piles Anchor.p2).hidden = [S .king] ∧
    (xB₂.piles Anchor.p2).hidden = [S .king] ∧
    (xB₁.piles Anchor.p4).faceUp = [H .two] ∧
    (xB₁.piles Anchor.p4).hidden = [] ∧
    (xB₂.piles Anchor.p4).faceUp = [H .two] := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- `xB`'s reachable space, bounded by hand: the three records below
and nothing else. -/
def xOrbit (s : State) : Prop := s = xB ∨ s = xB₁ ∨ s = xB₂

/-! ### The dead move kinds -/

/-- The draw is dead everywhere here: stock and waste are empty in
the whole orbit. -/
private theorem draw_dead (st : State) (hs : st.stock = []) (hw : st.waste = []) :
    st.step .draw = none := by
  have hre : st.recycle = st := by simp [State.recycle, hs, hw]
  show State.dealStock st.recycle = none
  rw [hre]
  simp [State.dealStock, hs]

/-- The waste moves are dead: the waste is empty in the whole orbit. -/
private theorem waste_found_dead (st : State) (hw : st.waste = []) (c : Card) :
    st.step (.wasteToFound c) = none := by
  rw [step_w2f_eq, show st.wasteIs c = false from State.wasteIs_nil hw]
  simp

private theorem waste_tab_dead (st : State) (hw : st.waste = []) (c : Card) (b : Base) :
    st.step (.wasteToTab c b) = none := by
  rw [step_w2t_eq, show st.wasteIs c = false from State.wasteIs_nil hw]
  simp

/-- The only rank at index 12 is the king. -/
private theorem rank_toIdx_twelve {r : Rank} (h : r.toIdx = 12) : r = .king := by
  cases r <;> simp_all [Rank.toIdx]

/-- The only ascendable card of the craft is `♠K`: the three full
suits sit at 13, spades at 12. -/
private theorem nextUp_char (st : State)
    (hh : (st.found .heart).length = 13) (hd : (st.found .diamond).length = 13)
    (hc : (st.found .club).length = 13) (hsp : (st.found .spade).length = 12)
    (c : Card) (h : st.nextUp c = true) : c = S .king := by
  rcases c with ⟨s, r⟩
  rw [State.nextUp] at h
  have h4 : r.toIdx = st.foundHeight s := of_decide_eq_true h
  cases s with
  | spade =>
      have h5 : r.toIdx = 12 := h4.trans hsp
      cases rank_toIdx_twelve h5
      rfl
  | heart =>
      have := Rank.toIdx_lt r
      have h6 : st.foundHeight Suit.heart = 13 := hh
      omega
  | diamond =>
      have := Rank.toIdx_lt r
      have h6 : st.foundHeight Suit.diamond = 13 := hd
      omega
  | club =>
      have := Rank.toIdx_lt r
      have h6 : st.foundHeight Suit.club = 13 := hc
      omega

/-- A king can never be placed anywhere in the orbit: the anchors are
occupied, and no card sits thirteen. -/
private theorem canPlace_king_false (st : State)
    (hocc : ∀ a : Anchor, ¬ (st.piles a).isEmpty) (c : Card) (hck : c.rank = .king)
    (b : Base) : st.canPlace c b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_eq]
      have hio : (st.piles a).isEmpty = false := by
        cases hio : (st.piles a).isEmpty with
        | true => exact (hocc a hio).elim
        | false => rfl
      rw [hio]; simp
  | inr z =>
      rw [canPlace_inr_eq]
      cases hp : st.pileOfTop z with
      | none => rfl
      | some k =>
          show canSitOn c z = false
          cases hfit : canSitOn c z with
          | true =>
              obtain ⟨h1, -⟩ := (canSitOn_eq c z).mp hfit
              have hz := Rank.toIdx_lt z.rank
              rw [hck] at h1
              simp_all [Rank.toIdx]
          | false => rfl

/-- The spade queen cannot descend either: no top of the orbit is a
king. -/
private theorem canPlace_queen_false (st : State)
    (hocc : ∀ a : Anchor, ¬ (st.piles a).isEmpty)
    (htop : ∀ z : Card, st.pileOfTop z ≠ none → z.rank ≠ .king)
    (b : Base) : st.canPlace (S .queen) b = false := by
  cases b with
  | inl a =>
      rw [canPlace_inl_eq]
      have hio : (st.piles a).isEmpty = false := by
        cases hio : (st.piles a).isEmpty with
        | true => exact (hocc a hio).elim
        | false => rfl
      rw [hio]; simp
  | inr z =>
      rw [canPlace_inr_eq]
      cases hp : st.pileOfTop z with
      | none => rfl
      | some k =>
          show canSitOn (S .queen) z = false
          cases hfit : canSitOn (S .queen) z with
          | true =>
              obtain ⟨h1, -⟩ := (canSitOn_eq _ z).mp hfit
              have hq11 : (S .queen).rank.toIdx = 11 := rfl
              have hz2 : z.rank.toIdx = 12 := by simp_all
              have hpn : st.pileOfTop z ≠ none := by rw [hp]; simp
              exact absurd (rank_toIdx_twelve hz2) (htop z hpn)
          | false => rfl

/-- The foundation-return arm is dead everywhere in the orbit: the
three full-suit kings and the spade queen can never be placed. -/
private theorem foundToTab_dead (st : State)
    (hftH : st.foundTop Suit.heart = some (H .king))
    (hftD : st.foundTop Suit.diamond = some (D .king))
    (hftC : st.foundTop Suit.club = some (C .king))
    (hftS : st.foundTop Suit.spade = some (S .queen))
    (hocc : ∀ a : Anchor, ¬ (st.piles a).isEmpty)
    (htop : ∀ z : Card, st.pileOfTop z ≠ none → z.rank ≠ .king)
    (c : Card) (b : Base) : st.step (.foundToTab c b) = none := by
  rw [step_f2t_eq]
  cases hcs : c.suit with
  | heart =>
      rw [hftH]
      show (if decide ((H .king) = c) && st.canPlace c b then some _ else none) = none
      by_cases hck : c = H .king
      · subst hck
        rw [canPlace_king_false st hocc _ rfl b]; rfl
      · have h2 : decide ((H .king) = c) = false := by
          cases hdec : decide ((H .king) = c) with
          | true => exact absurd (of_decide_eq_true hdec) (fun hh => hck hh.symm)
          | false => rfl
        rw [h2, Bool.false_and]; rfl
  | diamond =>
      rw [hftD]
      show (if decide ((D .king) = c) && st.canPlace c b then some _ else none) = none
      by_cases hck : c = D .king
      · subst hck
        rw [canPlace_king_false st hocc _ rfl b]; rfl
      · have h2 : decide ((D .king) = c) = false := by
          cases hdec : decide ((D .king) = c) with
          | true => exact absurd (of_decide_eq_true hdec) (fun hh => hck hh.symm)
          | false => rfl
        rw [h2, Bool.false_and]; rfl
  | club =>
      rw [hftC]
      show (if decide ((C .king) = c) && st.canPlace c b then some _ else none) = none
      by_cases hck : c = C .king
      · subst hck
        rw [canPlace_king_false st hocc _ rfl b]; rfl
      · have h2 : decide ((C .king) = c) = false := by
          cases hdec : decide ((C .king) = c) with
          | true => exact absurd (of_decide_eq_true hdec) (fun hh => hck hh.symm)
          | false => rfl
        rw [h2, Bool.false_and]; rfl
  | spade =>
      rw [hftS]
      show (if decide ((S .queen) = c) && st.canPlace c b then some _ else none) = none
      by_cases hck : c = S .queen
      · subst hck
        rw [canPlace_queen_false st hocc htop b]; rfl
      · have h2 : decide ((S .queen) = c) = false := by
          cases hdec : decide ((S .queen) = c) with
          | true => exact absurd (of_decide_eq_true hdec) (fun hh => hck hh.symm)
          | false => rfl
        rw [h2, Bool.false_and]; rfl

/-! ### The per-state shape facts -/

/-- Every anchor of every orbit state is occupied (guards hold hidden
cards; the threads hold their slices). -/
private theorem xOrbit_occupied (a : Anchor) :
    ¬ (xB.piles a).isEmpty ∧ ¬ (xB₁.piles a).isEmpty ∧ ¬ (xB₂.piles a).isEmpty := by
  cases a <;> exact ⟨by decide, by decide, by decide⟩

private theorem xB_occ (a : Anchor) : ¬ (xB.piles a).isEmpty := (xOrbit_occupied a).1
private theorem xB1_occ (a : Anchor) : ¬ (xB₁.piles a).isEmpty := (xOrbit_occupied a).2.1
private theorem xB2_occ (a : Anchor) : ¬ (xB₂.piles a).isEmpty := (xOrbit_occupied a).2.2

/-- No top of any orbit state is a king, and the tops are the two
cargos and the poison. -/
private theorem xB_topChar (z : Card) (h : xB.pileOfTop z ≠ none) :
    z = C .six ∨ z = S .six := by
  obtain ⟨a, ha⟩ : ∃ a, xB.topOf a = some z := by
    cases hp : xB.pileOfTop z with
    | none => exact absurd hp h
    | some a => exact ⟨a, pileOfTop_some hp⟩
  cases a with
  | p0 => rw [show xB.topOf Anchor.p0 = none from rfl] at ha; simp at ha
  | p1 => rw [show xB.topOf Anchor.p1 = none from rfl] at ha; simp at ha
  | p2 =>
      rw [show xB.topOf Anchor.p2 = some (C .six) from rfl] at ha
      exact Or.inl (Option.some.inj ha).symm
  | p3 => rw [show xB.topOf Anchor.p3 = none from rfl] at ha; simp at ha
  | p4 =>
      rw [show xB.topOf Anchor.p4 = some (S .six) from rfl] at ha
      exact Or.inr (Option.some.inj ha).symm
  | p5 => rw [show xB.topOf Anchor.p5 = none from rfl] at ha; simp at ha
  | p6 => rw [show xB.topOf Anchor.p6 = none from rfl] at ha; simp at ha

private theorem xB1_topChar (z : Card) (h : xB₁.pileOfTop z ≠ none) :
    z = S .six ∨ z = H .two := by
  obtain ⟨a, ha⟩ : ∃ a, xB₁.topOf a = some z := by
    cases hp : xB₁.pileOfTop z with
    | none => exact absurd hp h
    | some a => exact ⟨a, pileOfTop_some hp⟩
  cases a with
  | p0 => rw [show xB₁.topOf Anchor.p0 = none from rfl] at ha; simp at ha
  | p1 => rw [show xB₁.topOf Anchor.p1 = none from rfl] at ha; simp at ha
  | p2 =>
      rw [show xB₁.topOf Anchor.p2 = some (S .six) from rfl] at ha
      exact Or.inl (Option.some.inj ha).symm
  | p3 => rw [show xB₁.topOf Anchor.p3 = none from rfl] at ha; simp at ha
  | p4 =>
      rw [show xB₁.topOf Anchor.p4 = some (H .two) from rfl] at ha
      exact Or.inr (Option.some.inj ha).symm
  | p5 => rw [show xB₁.topOf Anchor.p5 = none from rfl] at ha; simp at ha
  | p6 => rw [show xB₁.topOf Anchor.p6 = none from rfl] at ha; simp at ha

private theorem xB2_topChar (z : Card) (h : xB₂.pileOfTop z ≠ none) :
    z = C .six ∨ z = H .two := by
  obtain ⟨a, ha⟩ : ∃ a, xB₂.topOf a = some z := by
    cases hp : xB₂.pileOfTop z with
    | none => exact absurd hp h
    | some a => exact ⟨a, pileOfTop_some hp⟩
  cases a with
  | p0 => rw [show xB₂.topOf Anchor.p0 = none from rfl] at ha; simp at ha
  | p1 => rw [show xB₂.topOf Anchor.p1 = none from rfl] at ha; simp at ha
  | p2 =>
      rw [show xB₂.topOf Anchor.p2 = some (C .six) from rfl] at ha
      exact Or.inl (Option.some.inj ha).symm
  | p3 => rw [show xB₂.topOf Anchor.p3 = none from rfl] at ha; simp at ha
  | p4 =>
      rw [show xB₂.topOf Anchor.p4 = some (H .two) from rfl] at ha
      exact Or.inr (Option.some.inj ha).symm
  | p5 => rw [show xB₂.topOf Anchor.p5 = none from rfl] at ha; simp at ha
  | p6 => rw [show xB₂.topOf Anchor.p6 = none from rfl] at ha; simp at ha

private theorem xB_noKingTop (z : Card) (h : xB.pileOfTop z ≠ none) :
    z.rank ≠ .king := by
  rcases xB_topChar z h with rfl | rfl <;> decide

private theorem xB1_noKingTop (z : Card) (h : xB₁.pileOfTop z ≠ none) :
    z.rank ≠ .king := by
  rcases xB1_topChar z h with rfl | rfl <;> decide

private theorem xB2_noKingTop (z : Card) (h : xB₂.pileOfTop z ≠ none) :
    z.rank ≠ .king := by
  rcases xB2_topChar z h with rfl | rfl <;> decide

/-- The face-up census of each orbit state. -/
private theorem xB_faceUp_disj {c : Card} {a : Anchor}
    (h : c ∈ (xB.piles a).faceUp) :
    c = D .seven ∨ c = C .six ∨ c = H .five ∨ c = H .seven ∨ c = S .six := by
  cases a with
  | p0 => simp only [show (xB.piles Anchor.p0).faceUp = [] from rfl] at h; cases h
  | p1 => simp only [show (xB.piles Anchor.p1).faceUp = [] from rfl] at h; cases h
  | p2 =>
      simp only [show (xB.piles Anchor.p2).faceUp = [D .seven, C .six] from rfl] at h
      cases h with
      | head => simp
      | tail b h2 =>
          cases h2 with
          | head => simp
          | tail c3 h3 => cases h3
  | p3 => simp only [show (xB.piles Anchor.p3).faceUp = [] from rfl] at h; cases h
  | p4 =>
      simp only [show (xB.piles Anchor.p4).faceUp =
        [H .five, H .seven, S .six] from rfl] at h
      cases h with
      | head => simp
      | tail b h2 =>
          cases h2 with
          | head => simp
          | tail c3 h3 =>
              cases h3 with
              | head => simp
              | tail c4 h4 => cases h4
  | p5 => simp only [show (xB.piles Anchor.p5).faceUp = [] from rfl] at h; cases h
  | p6 => simp only [show (xB.piles Anchor.p6).faceUp = [] from rfl] at h; cases h

private theorem xB1_faceUp_disj {c : Card} {a : Anchor}
    (h : c ∈ (xB₁.piles a).faceUp) :
    c = D .seven ∨ c = C .six ∨ c = H .five ∨ c = H .seven ∨ c = S .six ∨
    c = H .two := by
  cases a with
  | p0 => simp only [show (xB₁.piles Anchor.p0).faceUp = [] from rfl] at h; cases h
  | p1 => simp only [show (xB₁.piles Anchor.p1).faceUp = [] from rfl] at h; cases h
  | p2 =>
      simp only [show (xB₁.piles Anchor.p2).faceUp =
        [D .seven, C .six, H .five, H .seven, S .six] from rfl] at h
      cases h with
      | head => simp
      | tail b h2 =>
          cases h2 with
          | head => simp
          | tail c3 h3 =>
              cases h3 with
              | head => simp
              | tail c4 h4 =>
                  cases h4 with
                  | head => simp
                  | tail c5 h5 =>
                      cases h5 with
                      | head => simp
                      | tail c6 h6 => cases h6
  | p3 => simp only [show (xB₁.piles Anchor.p3).faceUp = [] from rfl] at h; cases h
  | p4 =>
      simp only [show (xB₁.piles Anchor.p4).faceUp = [H .two] from rfl] at h
      cases h with
      | head => simp
      | tail c3 h3 => cases h3
  | p5 => simp only [show (xB₁.piles Anchor.p5).faceUp = [] from rfl] at h; cases h
  | p6 => simp only [show (xB₁.piles Anchor.p6).faceUp = [] from rfl] at h; cases h

private theorem xB2_faceUp_disj {c : Card} {a : Anchor}
    (h : c ∈ (xB₂.piles a).faceUp) :
    c = D .seven ∨ c = C .six ∨ c = H .two := by
  cases a with
  | p0 => simp only [show (xB₂.piles Anchor.p0).faceUp = [] from rfl] at h; cases h
  | p1 => simp only [show (xB₂.piles Anchor.p1).faceUp = [] from rfl] at h; cases h
  | p2 =>
      simp only [show (xB₂.piles Anchor.p2).faceUp = [D .seven, C .six] from rfl] at h
      cases h with
      | head => simp
      | tail b h2 =>
          cases h2 with
          | head => simp
          | tail c3 h3 => cases h3
  | p3 => simp only [show (xB₂.piles Anchor.p3).faceUp = [] from rfl] at h; cases h
  | p4 =>
      simp only [show (xB₂.piles Anchor.p4).faceUp = [H .two] from rfl] at h
      cases h with
      | head => simp
      | tail c3 h3 => cases h3
  | p5 => simp only [show (xB₂.piles Anchor.p5).faceUp = [] from rfl] at h; cases h
  | p6 => simp only [show (xB₂.piles Anchor.p6).faceUp = [] from rfl] at h; cases h

/-! ### The fit matrices -/

/-- The fit matrix at `xB`: among its face-up cards and tops, only the
two helix landings fit. -/
private theorem xB_fit_live (c z : Card)
    (hc : c = D .seven ∨ c = C .six ∨ c = H .five ∨ c = H .seven ∨ c = S .six)
    (hz : z = C .six ∨ z = S .six) (hfit : canSitOn c z = true) :
    (c = H .five ∧ z = C .six) ∨ (c = H .five ∧ z = S .six) := by
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl <;>
    first
    | exact absurd hfit (by decide)
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩

/-- The fit matrix at `xB₁`: only the tail-vanish fits. -/
private theorem xB1_fit_live (c z : Card)
    (hc : c = D .seven ∨ c = C .six ∨ c = H .five ∨ c = H .seven ∨
      c = S .six ∨ c = H .two)
    (hz : z = S .six ∨ z = H .two) (hfit : canSitOn c z = true) :
    c = H .five ∧ z = S .six := by
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hz with rfl | rfl <;>
    first
    | exact absurd hfit (by decide)
    | exact ⟨rfl, rfl⟩

/-- The fit matrix at `xB₂`: nothing fits. -/
private theorem xB2_fit_dead (c z : Card)
    (hc : c = D .seven ∨ c = C .six ∨ c = H .two)
    (hz : z = C .six ∨ z = H .two) (hfit : canSitOn c z = true) : False := by
  rcases hc with rfl | rfl | rfl <;> rcases hz with rfl | rfl <;>
    exact absurd hfit (by decide)

/-! ### The live-move characterizations -/

/-- `xB` has exactly the two first moves: the mirror merge and the
tail-vanish. -/
private theorem xB_liveOnly (c : Card) (b : Base) (t : State)
    (h : xB.step (.tabToTab c b) = some t) :
    (c = H .five ∧ b = .inr (C .six) ∧ t = xB₁) ∨
    (c = H .five ∧ b = .inr (S .six) ∧ t = xB₂) := by
  have hstep := h
  rw [step_t2t_eq] at h
  cases hh : xB.pileHolding c with
  | none => rw [hh] at h; simp at h
  | some a =>
      rw [hh] at h
      cases hcp : xB.canPlace c b with
      | false => rw [hcp] at h; simp at h
      | true =>
          rw [hcp] at h
          have hmem : c ∈ (xB.piles a).faceUp := pileHolding_some hh
          cases b with
          | inl a0 =>
          rw [canPlace_inl_eq] at hcp
          have hio : (xB.piles a0).isEmpty = false := by
            cases hio : (xB.piles a0).isEmpty with
            | true => exact (xB_occ a0 hio).elim
            | false => rfl
          rw [hio] at hcp; simp at hcp
          | inr z =>
              rw [canPlace_inr_eq] at hcp
              cases hpt : xB.pileOfTop z with
              | none => rw [hpt] at hcp; simp at hcp
              | some k =>
                  rw [hpt] at hcp
                  have hfit : canSitOn c z = true := hcp
                  rcases xB_fit_live c z (xB_faceUp_disj hmem)
                      (xB_topChar z (by rw [hpt]; simp)) hfit with
                    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                  · rw [xB_copy_step] at hstep
                    exact Or.inl ⟨rfl, rfl, (Option.some.inj hstep).symm⟩
                  · rw [xB_vanish_step] at hstep
                    exact Or.inr ⟨rfl, rfl, (Option.some.inj hstep).symm⟩

/-- `xB₁` has exactly the one move: the tail-vanish. -/
private theorem xB1_liveOnly (c : Card) (b : Base) (t : State)
    (h : xB₁.step (.tabToTab c b) = some t) :
    c = H .five ∧ b = .inr (S .six) ∧ t = xB₂ := by
  have hstep := h
  rw [step_t2t_eq] at h
  cases hh : xB₁.pileHolding c with
  | none => rw [hh] at h; simp at h
  | some a =>
      rw [hh] at h
      cases hcp : xB₁.canPlace c b with
      | false => rw [hcp] at h; simp at h
      | true =>
          rw [hcp] at h
          have hmem : c ∈ (xB₁.piles a).faceUp := pileHolding_some hh
          cases b with
          | inl a0 =>
          rw [canPlace_inl_eq] at hcp
          have hio : (xB₁.piles a0).isEmpty = false := by
            cases hio : (xB₁.piles a0).isEmpty with
            | true => exact (xB1_occ a0 hio).elim
            | false => rfl
          rw [hio] at hcp; simp at hcp
          | inr z =>
              rw [canPlace_inr_eq] at hcp
              cases hpt : xB₁.pileOfTop z with
              | none => rw [hpt] at hcp; simp at hcp
              | some k =>
                  rw [hpt] at hcp
                  have hfit : canSitOn c z = true := hcp
                  rcases xB1_fit_live c z (xB1_faceUp_disj hmem)
                      (xB1_topChar z (by rw [hpt]; simp)) hfit with ⟨rfl, rfl⟩
                  rw [xB₁_vanish_step] at hstep
                  exact ⟨rfl, rfl, (Option.some.inj hstep).symm⟩

/-- `xB₂` is fully frozen. -/
private theorem xB2_frozen (m : Move) : xB₂.step m = none := by
  cases m with
  | draw => exact draw_dead xB₂ rfl rfl
  | wasteToFound c => exact waste_found_dead xB₂ rfl c
  | wasteToTab c b => exact waste_tab_dead xB₂ rfl c b
  | tabToFound c =>
      rw [step_t2f_eq]
      cases hn : xB₂.nextUp c with
      | false => rfl
      | true =>
          have hck : c = S .king :=
            nextUp_char xB₂ rfl rfl rfl rfl c hn
          subst hck
          have hpt : xB₂.pileOfTop (S .king) = none := by decide
          rw [hpt]
          rfl
  | foundToTab c b =>
      exact foundToTab_dead xB₂ rfl rfl rfl rfl xB2_occ xB2_noKingTop c b
  | tabToTab c b =>
      cases h' : xB₂.step (.tabToTab c b) with
      | none => rfl
      | some t =>
          exfalso
          have hstep : xB₂.step (.tabToTab c b) = some t := h'
          rw [step_t2t_eq] at hstep
          cases hh : xB₂.pileHolding c with
          | none => rw [hh] at hstep; simp at hstep
          | some a =>
              rw [hh] at hstep
              cases hcp : xB₂.canPlace c b with
              | false => rw [hcp] at hstep; simp at hstep
              | true =>
                  rw [hcp] at hstep
                  have hmem : c ∈ (xB₂.piles a).faceUp := pileHolding_some hh
                  cases b with
                  | inl a0 =>
                      rw [canPlace_inl_eq] at hcp
                      have hio : (xB₂.piles a0).isEmpty = false := by
                        cases hio : (xB₂.piles a0).isEmpty with
                        | true => exact (xB2_occ a0 hio).elim
                        | false => rfl
                      rw [hio] at hcp; simp at hcp
                  | inr z =>
                      rw [canPlace_inr_eq] at hcp
                      cases hpt : xB₂.pileOfTop z with
                      | none => rw [hpt] at hcp; simp at hcp
                      | some k =>
                          rw [hpt] at hcp
                          exact xB2_fit_dead c z (xB2_faceUp_disj hmem)
                            (xB2_topChar z (by rw [hpt]; simp)) hcp

/-! ### The closure and the verdicts -/

/-- **The three-state enumeration, closed**: every move out of any
orbit state lands back in the orbit (all other kinds dead, the live
moves exactly the recorded step-lemmas).  [axioms: none — per-kind
case analysis on the crafted shapes.] -/
theorem xOrbit_closed (s : State) (hmem : xOrbit s) (m : Move) (t : State)
    (hstep : s.step m = some t) : xOrbit t := by
  rcases hmem with rfl | rfl | rfl
  · cases m with
    | draw => rw [draw_dead xB rfl rfl] at hstep; simp at hstep
    | wasteToFound c => rw [waste_found_dead xB rfl c] at hstep; simp at hstep
    | wasteToTab c b => rw [waste_tab_dead xB rfl c b] at hstep; simp at hstep
    | tabToFound c =>
        rw [step_t2f_eq] at hstep
        cases hn : xB.nextUp c with
        | false => rw [hn] at hstep; simp at hstep
        | true =>
            have hck : c = S .king := nextUp_char xB rfl rfl rfl rfl c hn
            subst hck
            have hpt : xB.pileOfTop (S .king) = none := by decide
            rw [hn, hpt] at hstep; simp at hstep
    | foundToTab c b =>
        rw [foundToTab_dead xB rfl rfl rfl rfl xB_occ xB_noKingTop c b] at hstep
        simp at hstep
    | tabToTab c b =>
        rcases xB_liveOnly c b t hstep with ⟨rfl, rfl, ht⟩ | ⟨rfl, rfl, ht⟩
        · exact Or.inr (Or.inl ht)
        · exact Or.inr (Or.inr ht)
  · cases m with
    | draw => rw [draw_dead xB₁ rfl rfl] at hstep; simp at hstep
    | wasteToFound c => rw [waste_found_dead xB₁ rfl c] at hstep; simp at hstep
    | wasteToTab c b => rw [waste_tab_dead xB₁ rfl c b] at hstep; simp at hstep
    | tabToFound c =>
        rw [step_t2f_eq] at hstep
        cases hn : xB₁.nextUp c with
        | false => rw [hn] at hstep; simp at hstep
        | true =>
            have hck : c = S .king := nextUp_char xB₁ rfl rfl rfl rfl c hn
            subst hck
            have hpt : xB₁.pileOfTop (S .king) = none := by decide
            rw [hn, hpt] at hstep; simp at hstep
    | foundToTab c b =>
        rw [foundToTab_dead xB₁ rfl rfl rfl rfl xB1_occ xB1_noKingTop c b] at hstep
        simp at hstep
    | tabToTab c b =>
        obtain ⟨rfl, rfl, ht⟩ := xB1_liveOnly c b t hstep
        exact Or.inr (Or.inr ht)
  · rw [xB2_frozen m] at hstep; simp at hstep

/-- Every orbit state is a non-win: the spade foundation is never
touched inside the orbit, and it is the only one short of 13. -/
theorem xOrbit_notWin (s : State) (hmem : xOrbit s) : s.isWin = false := by
  rcases hmem with rfl | rfl | rfl <;> decide

/-- The orbit rides every play out of any of its states. -/
private theorem xOrbit_run : ∀ (s : State) (hmem : xOrbit s) (play : List Move)
    (w : State), s.run play = some w → xOrbit w := by
  intro s hmem play
  induction play generalizing s with
  | nil =>
      intro w hrun
      have := Option.some.inj hrun
      subst this
      exact hmem
  | cons m rest ih =>
      intro w hrun
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      exact ih s₁ (xOrbit_closed s hmem m s₁ hstep) w hrest

/-- **VERDICT: `xB` is unwinnable** — its reachable space is the
three frozen-or-poisoned records, and the spade foundation never
reaches 13.  [axioms: none.] -/
theorem xB_noWin : ¬ WinFrom xB := by
  rintro ⟨play, w, hrun, hwin⟩
  have hv : xOrbit w := xOrbit_run xB (Or.inl rfl) play w hrun
  rw [xOrbit_notWin w hv] at hwin
  exact absurd hwin (by simp)

/-! ## The fences -/

/-- **THE FENCE: the exchange pair is verdict-distinct** — `xA` wins
through the merge, `xB` — its twin-thread exchange — loses everywhere.
[axioms: none.] -/
theorem xA_xB_notSameFate : ¬ sameFate xA xB := by
  intro hiff
  exact absurd (hiff.mp xA_win) xB_noWin

/-- The helix-thread shape of the pair: one pile hosts a run
`[c₀, t, z]` (braided head over a twin seat and its cargo), another
the bare other thread `[t', z']`, with `t, t'` and `z, z'` the twin
pairs and both cargos legally seated. -/
def HelixThreads (s : State) (a₁ a₂ : Anchor) : Prop :=
  a₁ ≠ a₂ ∧ ∃ t t' z z' c₀ : Card,
    (s.piles a₁).faceUp = [c₀, t, z] ∧ (s.piles a₂).faceUp = [t', z'] ∧
    t.suit.twin = t'.suit ∧ t.rank = t'.rank ∧
    z.suit.twin = z'.suit ∧ z.rank = z'.rank ∧ z ≠ z' ∧
    canSitOn z t = true ∧ canSitOn z' t' = true

/-- The twin-thread exchange relation: `s'` is `s` with the two
helix-thread slices traded (hidden cards at their piles, everything
else untouched) — the board-only lift of the old `exchangeTwinCargo`. -/
def ExchHelix (s s' : State) : Prop :=
  ∃ a₁ a₂ : Anchor, HelixThreads s a₁ a₂ ∧
    s'.stock = s.stock ∧ s'.waste = s.waste ∧ s'.drawStep = s.drawStep ∧
    (∀ σ : Suit, s'.found σ = s.found σ) ∧
    (∀ a : Anchor, a ≠ a₁ ∧ a ≠ a₂ → s'.piles a = s.piles a) ∧
    (s'.piles a₁).hidden = (s.piles a₁).hidden ∧
    (s'.piles a₂).hidden = (s.piles a₂).hidden ∧
    (s'.piles a₁).faceUp = (s.piles a₂).faceUp ∧
    (s'.piles a₂).faceUp = (s.piles a₁).faceUp

/-- The witness pair stands in the exchange relation, with the helix
twin premises witnessed: seats `♥7, ♦7`, cargos `♠6, ♣6`, braided
head `♥5`. -/
theorem xA_xB_ExchHelix : ExchHelix xA xB :=
  ⟨Anchor.p2, Anchor.p4,
    ⟨by decide,
      H .seven, D .seven, S .six, C .six, H .five,
      by rfl, by rfl, by rfl, by rfl, by decide, by decide, by decide⟩,
    by rfl, by rfl, by rfl,
    by intro σ; cases σ <;> rfl,
    by
      intro a ha
      cases a
      · rfl
      · rfl
      · exact absurd rfl ha.1
      · rfl
      · exact absurd rfl ha.2
      · rfl
      · rfl,
    by rfl, by rfl, by rfl, by rfl⟩

/-- **The premiseless exchange universal is REFUTED (the wave-15
claim, physical spelling)**: there are helix-thread twins — seats and
cargos twinned, both cargos legally seated, the slices exchanged —
whose verdicts split.  [axioms: none.] -/
theorem wk_exchange_premiseless_false :
    ¬ (∀ s s' : State, ExchHelix s s' → sameFate s s') := by
  intro h
  exact xA_xB_notSameFate (h xA xB xA_xB_ExchHelix)

/-! ## The census battery (deterministic `#eval` probes) -/

private def rankStr (r : Rank) : String :=
  match r with
  | .ace => "A" | .two => "2" | .three => "3" | .four => "4" | .five => "5"
  | .six => "6" | .seven => "7" | .eight => "8" | .nine => "9" | .ten => "10"
  | .jack => "J" | .queen => "Q" | .king => "K"

private def cardStr (c : Card) : String :=
  (match c.suit with
    | .spade => "♠"
    | .heart => "♥"
    | .diamond => "♦"
    | .club => "♣") ++ rankStr c.rank

private def cardsStr (l : List Card) : String :=
  "[" ++ String.intercalate ", " (l.map cardStr) ++ "]"

private def moveCase (st : State) (m : Move) : List (Move × State) :=
  match st.step m with
  | some t => [(m, t)]
  | none => []

/-- The full move enumeration at a state (all six kinds over all
cards and bases) — the census instrument. -/
private def allMoves (st : State) : List (Move × State) :=
  moveCase st .draw
  ++ (Card.universe.flatMap fun c =>
        moveCase st (.wasteToFound c) ++ moveCase st (.tabToFound c))
  ++ ((Card.universe.flatMap fun c => Anchor.all.map fun a => (c, Sum.inl a))
      ++ (Card.universe.flatMap fun c => Card.universe.map fun z => (c, Sum.inr z))
      ).flatMap fun cb =>
      match cb with
      | (c, b) =>
          moveCase st (.wasteToTab c b) ++ moveCase st (.foundToTab c b)
            ++ moveCase st (.tabToTab c b)

/-- info: some true -/
#guard_msgs in
#eval (xA.run winPlay).map (·.isWin)

/-- info: [false, false, false, true] -/
#guard_msgs in
#eval [xB.isWin, xB₁.isWin, xB₂.isWin, xW.isWin]

/-- info: some "[♦7, ♣6, ♥5, ♥7, ♠6]" -/
#guard_msgs in
#eval (xA.run [mergeMove]).map fun s => cardsStr (s.piles Anchor.p4).faceUp

/-- info: some "[♠K]" -/
#guard_msgs in
#eval (xA.run [mergeMove]).map fun s => cardsStr (s.piles Anchor.p2).faceUp

/-- info: 2 -/
#guard_msgs in
#eval (allMoves xA).length

/-- info: 2 -/
#guard_msgs in
#eval (allMoves xB).length

/-- info: 0 -/
#guard_msgs in
#eval (allMoves xB₂).length

/- Axiom pins for the battery. -/
#print axioms OrigExchange.xA_win
#print axioms OrigExchange.xB_noWin
#print axioms OrigExchange.xA_xB_notSameFate
#print axioms OrigExchange.wk_exchange_premiseless_false
#print axioms OrigExchange.xA_xB_ExchHelix
#print axioms OrigExchange.xOrbit_closed
#print axioms OrigExchange.xOrbit_notWin

end OrigExchange



