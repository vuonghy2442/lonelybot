import Orig.Shuttle
import Orig.Phase
import Orig.Irreversible
import Orig.Classify
import Orig.Reach

/-!
# The original game — the to-foundation dominances

The physical port of method.md §5.1 (forced safe stacking) and §5.3
(draw-1 deck dominance).  The old engine's chapter is
`Klondike/Dominance.lean`; the correspondence is six moves on six:

| old (Klondike) | here (Orig) | remark |
|---|---|---|
| `draw` | `draw` | the physical deal recycles; no cursor |
| `deckStack` | `wasteToFound` | c pinned by `wasteIs` |
| `deckPile` | `wasteToTab` | |
| `pileStack` | `tabToFound` | the §5.1 subject |
| `stackPile` | `foundToTab` | the worry-back |
| `pilePile` | `tabToTab` | first-class runs here |

Two physical dividends change the shape of the statements:

* **no locked-guard** — the reveal is part of the moving move
  (`Pile.afterRunRemoved`), so the old dead-pile witness (a stacked
  card stranding its hidden boundary) is unstateable here;
* **the deal-adjacent residue is geometric** — the R/N split of the
  old §5.1 (returnable base vs the rest) reads here as: the raised
  card's below-run still sits (`tabToFound_undo_under`), the pile
  empties and the card is a king (`tabToFound_undo_bare`), or the
  *bare floor corner* — the below-run is empty and either the reveal
  seated a fresh card or the card is no king.  The first two are
  LANDED (Orig.Irreversible); the third is the file's one §5.1
  residue, the old [GAP] channel-A/B reshape in physical dress.

§5.3 follows the old chapter's layer split — (A) the
stock-as-reserve rotation, (B) the compliant replay, (C) the
rung-discipline normal form — each named below.  The assembly
plumbing is proven; the residues carry their routes.
-/

/-- Keller's safe-automove rung condition, physical form (the old
`safeToStack`, translated through `foundHeight`): a rank-`r` card of
colour `κ` is safe iff both `κ`-colored foundations are built to
`r−2` and both `κ̄`-colored to `r−1`. -/
def safeToFound (st : State) (c : Card) : Bool :=
  Suit.all.all fun σ =>
    if σ.color = c.suit.color
    then decide (c.rank.toIdx ≤ st.foundHeight σ + 2)
    else decide (c.rank.toIdx ≤ st.foundHeight σ + 1)

/-! ## The win transport -/

/-- A win behind a play that runs there: prepending the play lifts
the verdict — the play-level lift of `WinFrom_of_succ`. -/
theorem WinFrom_of_runTo {s s' : State} {play : List Move}
    (h : s.run play = some s') (hs : WinFrom s') : WinFrom s := by
  induction play generalizing s with
  | nil =>
      have heq : s = s' := Option.some.inj h
      rw [heq]
      exact hs
  | cons m rest ih =>
      obtain ⟨t, hstep, hrest⟩ := State.run_cons h
      exact WinFrom_of_succ ⟨m, hstep⟩ (ih hrest)

/-- The undo transport: a reversible witness play from the successor
back to the origin re-lifts the origin's win — the R-cases' common
tail. -/
theorem WinFrom_of_undo {st : State} {m : Move} {s₁ : State}
    (hstep : State.step st m = some s₁) (hw : reversibleAtW st m)
    (hsolv : WinFrom st) : WinFrom s₁ := by
  obtain ⟨s₂, play, hstep2, hback⟩ := hw
  rw [hstep2] at hstep
  have he : s₂ = s₁ := Option.some.inj hstep
  rw [he] at hback
  exact WinFrom_of_runTo hback hsolv

/-! ## Small local kit (dedup at harvest)

The former `runOK_snoc_sit` and `lastOf_exists` mirrors are gone —
they cite the public rows in `Orig/State.lean` since the
dedup-collapse wave. -/

/-- The chop keeps every card it does not drop. -/
private theorem mem_of_chop : ∀ {l : List Card} {x : Card}, x ∈ chop l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      cases t with
      | nil => cases h
      | cons w t' =>
          show x ∈ y :: w :: t'
          rcases List.mem_cons.1 h with rfl | hrest
          · exact List.mem_cons.2 (Or.inl rfl)
          · exact List.mem_cons.2 (Or.inr (ih hrest))

/-! ## The tabToFound firing shape -/

private theorem tabToFound_fires {st : State} {c : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁) :
    st.nextUp c = true ∧ ∃ a, st.pileOfTop c = some a := by
  by_cases hn : st.nextUp c = true
  · refine ⟨hn, ?_⟩
    cases hp : st.pileOfTop c with
    | none =>
        exfalso
        have hnone : State.step st (Move.tabToFound c) = none := by
          show (if st.nextUp c then
              match st.pileOfTop c with
              | none => none
              | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
                  piles := fun a' => if a' = a then
                      Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                    else st.piles a' }
              else none) = none
          rw [ite_eq_left hn, hp]
        rw [hnone] at hstep
        exact absurd hstep (by simp)
    | some a => exact ⟨a, rfl⟩
  · exfalso
    have hnone : State.step st (Move.tabToFound c) = none := by
      show (if st.nextUp c then
          match st.pileOfTop c with
          | none => none
          | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
              piles := fun a' => if a' = a then
                  Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
                else st.piles a' }
          else none) = none
      rw [ite_eq_right hn]
    rw [hnone] at hstep
    exact absurd hstep (by simp)

private theorem tabToFound_shape {st : State} {c : Card} {a : Anchor} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a) :
    s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
           piles := fun a' => if a' = a then
               Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
             else st.piles a' } := by
  obtain ⟨hnext, -⟩ := tabToFound_fires hstep
  have hstep' : State.step st (Move.tabToFound c) =
      some { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' => if a' = a then
                 Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
               else st.piles a' } := by
    show (if st.nextUp c then
        match st.pileOfTop c with
        | none => none
        | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
            piles := fun a' => if a' = a then
                Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
              else st.piles a' }
        else none) = some { st.setFound c.suit (st.found c.suit ++ [c]) with
            piles := fun a' => if a' = a then
                Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
              else st.piles a' }
    rw [ite_eq_left hnext, hpa]
  exact ((Option.some.inj (hstep'.symm.trans hstep))).symm

/-! ## §5.1 — the safe tabToFound -/

/-- The R1 search premise at the source's `WF`: after the raise of a
card with a live below-run, the below-run's last card tops the source
pile and tops no other. -/
private theorem pileOfTop_after_tabToFound {st : State} {c z : Card} {k : Anchor}
    {s₁ : State}
    (hwf : st.WF)
    (hz : lastOf (chop (st.piles k).faceUp) = some z)
    (hs : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
           piles := fun a' => if a' = k then
               Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
             else st.piles a' }) :
    s₁.pileOfTop z = some k := by
  have hzmem : z ∈ (st.piles k).faceUp := by
    have h1 : z ∈ chop (st.piles k).faceUp := lastOf_mem hz
    exact mem_of_chop h1
  have hpilek : s₁.piles k = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp) := by
    rw [hs]
    show (if k = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles k) = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
    rw [ite_eq_left rfl]
  have hpothers : ∀ a', a' ≠ k → s₁.piles a' = st.piles a' := by
    intro a' hne
    rw [hs]
    show (if a' = k then
        Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      else st.piles a') = st.piles a'
    rw [ite_eq_right hne]
  -- s₁'s pile k tops z (the removal kept the below-run)
  have htops : s₁.topOf k = some z := by
    show lastOf ((s₁.piles k).faceUp) = some z
    rw [hpilek]
    show lastOf (Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)).faceUp = some z
    cases hch : chop (st.piles k).faceUp with
    | nil =>
        rw [hch] at hz
        exact absurd hz (by simp [lastOf])
    | cons x t =>
        have hz' : lastOf (x :: t) = some z := by rw [← hch]; exact hz
        show lastOf (Pile.afterRunRemoved (st.piles k) (x :: t)).faceUp = some z
        rw [show Pile.afterRunRemoved (st.piles k) (x :: t)
            = { (st.piles k) with faceUp := x :: t } from rfl]
        exact hz'
  -- no other pile tops z at st, hence none at s₁
  have hother : ∀ y ∈ Anchor.all, y ≠ k → s₁.topOf y ≠ some z := by
    intro y hy hyne htop
    have hyeq : s₁.piles y = st.piles y := hpothers y hyne
    have htop' : (st.piles y).top = some z := by
      show lastOf ((st.piles y).faceUp) = some z
      rw [← hyeq]
      exact htop
    exact ((mem_faceUp_unique hwf hzmem) (a' := y) hyne).1 (Pile.mem_of_top htop')
  show firstWhere (fun a' => decide (s₁.topOf a' = some z)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) (by
    show decide (s₁.topOf k = some z) = true
    rw [htops]
    exact decide_eq_true rfl) (fun y hy hyne => decide_false_of_not (fun hcon =>
    hother y hy hyne hcon))

/-! ## The ground compliance (§5.1-N skeleton kit)

The (N) residue splits the B&G Thm-1 transform into its mechanical
replay half — proven below — and its normal-form half, which is the
one named sub-residue `tabToFound_groundNormalForm`.  The compliance
vocabulary a compliant winning play must satisfy before its rung
pass is `Move.groundBlocked`: no move may park on `c`'s vacated seat
(channel A's subject), no move may worry back `c`'s suit (channel
B's subject), and `c` itself may not be re-homed sideways before
the raise (the dig-without-raise shape — its dig-parity datum is
exhibited in `witnesses/OrigGroundWitness.lean`).  Every arm of the
predicate is inhabited by genuinely playable moves at the corner
states (the witness battery), and every arm's canonical replacement
is decided-live there. -/

/-- The pre-rung compliance: the move shapes whose legality at the
source cannot be echoed from the raised state — parks onto `c`'s
seat (the raised `c` is founded, so its seat searches away), worry
backs of `c`'s own suit (the raised foundation tops `c`, so the
prefix cards' worry-backs are not verbatim), and `c`'s own sideways
relocation (the raised state has `c` on the foundation, so the
relocation would need the worry-back first).  The rung pass itself
`.tabToFound c` is NOT blocked — it closes the window. -/
def Move.groundBlocked (c : Card) : Move → Bool
  | .wasteToTab _ b => decide (b = Sum.inr c)
  | .foundToTab x b => decide (x.suit = c.suit) || decide (b = Sum.inr c)
  | .tabToTab x b => decide (x = c) || decide (b = Sum.inr c)
  | _ => false

/-! ### The channel-A quantitative spine (the two-rank descent)

`safeToFound` puts every potential live tenant of `c`'s seat at
rank `r−1` opposite colour, every second-level tenant at `r−2` in
`c`'s own colour; a THIRD fit-step up the streak lands at `r−3`,
opposite colour again — where the opposite-colour conjunct of
`safeToFound` puts both such foundations at `r−1`, two ABOVE the
card.  A foundation built strictly past a card's index holds it
(the prefixes are honest), so no `hsafe`-consistent streak over
`c`'s seat is ever three deep — "the safety bounds descend exactly
two ranks" (B&G Cor. 3) made a lemma. -/

/-- The position of `x` in `l` (its first-occurrence index; a
self-rolled core-free helper for the take-membership kit). -/
private def posOf {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: t => if y = x then 0 else posOf x t + 1

/-- Below the first-occurrence position is inside the take. -/
private theorem mem_take_of_pos {α : Type} [DecidableEq α] :
    ∀ (l : List α) (x : α), x ∈ l → ∀ (n : Nat),
      posOf x l < n → x ∈ l.take n := by
  intro l x
  induction l with
  | nil => intro hx; cases hx
  | cons y t ih =>
      intro hx n hlt
      cases n with
      | zero => exact absurd hlt (by omega)
      | succ m =>
          rw [show posOf x (y :: t) = if y = x then 0 else posOf x t + 1 from rfl] at hlt
          split at hlt
          · rename_i hyx
            show x ∈ y :: t.take m
            exact List.mem_cons.2 (Or.inl hyx.symm)
          · rename_i hyx
            show x ∈ y :: t.take m
            refine List.mem_cons.2 (Or.inr ?_)
            have hmemt : x ∈ t := by
              rcases List.mem_cons.1 hx with he | hrest
              · exact absurd he.symm hyx
              · exact hrest
            exact ih hmemt m (by omega)

/-- The build order is the rank order: each card of the standard
build sits in the foundation-prefix take exactly when its index is
below the prefix length. -/
private theorem posOf_upCards (σ : Suit) (r : Rank) :
    posOf (Card.mk σ r) (Suit.upCards σ) = r.toIdx := by
  cases σ <;> cases r <;> rfl

/-- The take-membership half the ray lemma rides: strictly below
the prefix length is inside the take. -/
theorem mem_upCards_take (σ : Suit) (n : Nat) (r : Rank) (hlt : r.toIdx < n) :
    Card.mk σ r ∈ (Suit.upCards σ).take n :=
  mem_take_of_pos (Suit.upCards σ) (Card.mk σ r) (Suit.mem_upCards) n
    (by have := posOf_upCards σ r; omega)

/-- A foundation built strictly past a card's index holds it. -/
theorem mem_found_of_height {st : State} {x : Card} (hwf : st.WF)
    (hlt : x.rank.toIdx < st.foundHeight x.suit) : x ∈ st.found x.suit := by
  obtain ⟨n, hpre⟩ := hwf.found_prefix x.suit
  have hlen : ((x.suit.upCards).take n).length ≤ n := List.length_take_le n _
  have hfh : st.foundHeight x.suit = ((x.suit.upCards).take n).length := by
    show (st.found x.suit).length = _
    rw [hpre]
  have hlt' : x.rank.toIdx < n := by omega
  have hmem := mem_upCards_take x.suit n x.rank hlt'
  have hxe : x = Card.mk x.suit x.rank := by cases x; rfl
  rw [hpre, hxe]
  exact hmem

/-- The two-colour bounce of a three-deep fit chain: the first and
third steps alternate away from the middle, landing on the far
colour again. -/
private theorem color_ne_trans {a b c : Color} (h1 : a ≠ b) (h2 : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- **The ray lemma** — the channel-A quantitative spine: any card
that would sit three fit-steps deep over `c` is already founded at
a `hsafe` state (its own foundation stands two ABOVE its index), so
no `hsafe`-consistent streak over `c`'s seat is ever three deep.
"The safety bounds descend exactly two ranks" (B&G Cor. 3), made a
lemma. -/
theorem ground_streak_founded {st : State} {c : Card} (hwf : st.WF)
    (hsafe : safeToFound st c = true) {y z x : Card}
    (h1 : canSitOn y c = true) (h2 : canSitOn z y = true) (h3 : canSitOn x z = true) :
    x ∈ st.found x.suit := by
  obtain ⟨hy1, hy2⟩ := (canSitOn_eq y c).mp h1
  obtain ⟨hz1, hz2⟩ := (canSitOn_eq z y).mp h2
  obtain ⟨hx1, hx2⟩ := (canSitOn_eq x z).mp h3
  have hzc : z.suit.color = c.suit.color := color_ne_trans hz2 hy2
  have hxc : x.suit.color ≠ c.suit.color := by
    intro hcon
    exact hx2 (hcon.trans hzc.symm)
  have hsuite0 : ((fun σ : Suit =>
      if σ.color = c.suit.color then decide (c.rank.toIdx ≤ st.foundHeight σ + 2)
      else decide (c.rank.toIdx ≤ st.foundHeight σ + 1)) x.suit) = true :=
    List.all_eq_true.mp hsafe (x.suit) (Suit.mem_all x.suit)
  have hsuite : (if x.suit.color = c.suit.color
      then decide (c.rank.toIdx ≤ st.foundHeight x.suit + 2)
      else decide (c.rank.toIdx ≤ st.foundHeight x.suit + 1)) = true := hsuite0
  rw [ite_eq_right hxc] at hsuite
  have hle : c.rank.toIdx ≤ st.foundHeight x.suit + 1 := of_decide_eq_true hsuite
  have hsum : x.rank.toIdx + 3 = c.rank.toIdx := by omega
  exact mem_found_of_height hwf (by omega)

/-! ### The named sub-residue (the normal-form half) -/

/-- **(N) The normal-form half** — §5.1's one remaining piece as a PROVEN
skeleton's sole named sub-residue (the `replay_head_residue` /
`vacate_secondMove_residue` house pattern): at the bare-floor corner,
every winning play has a `groundBlocked`-clean winning counterpart
that raises `c` at its first `tabToFound c`.

**Why the row reduces here.**  `tabToFound_dominant_of_ground` below is
PROVEN from this residue plus the ground replay (`ground_replay_go`,
also below): a compliant winning play `π₁ ++ tabToFound c :: π₂`
replays from the raised state `s₁` as the verbatim prefix and the
verbatim tail — the raise moves to the front for free, the two states
coincide from the rung pass on, and the compliant prefix commutes
through the divergence field (found `c.suit` one ahead, pile `k` the
revealed counterpart of `c`'s seat).  The residue is exactly the
transform content, stated as the existence of the compliant shape.

**The compliance is the replay's verbatim demand, nothing more.**
Each `groundBlocked` arm covers a move kind whose legality at the
source cannot be echoed from the raised state: a park onto `c`'s
seat needs `c` seated and searchable (`pileOfTop c = some k` — false
once `c` is founded); a worry-back of `c`'s suit needs the founded
prefix's top — which at the raised state is `c` itself; `c`'s own
relocation needs it seated.  Every arm is INHABITED by a genuinely
playable move at the corner states and every arm's replacement is
decided-live there (`witnesses/OrigGroundWitness.lean`: the waste
park with its twin tenant raises, the two-deep run-park raising
end-to-end through the foundations `g1_streak_raise_chain`, the
c-suit worry onto a black mate, the relocation with its dig-parity —
the raise digs the same reveal).

**The route** (the B&G App. B.1 Thm-1 transform, physically): taken
last-noncompliant-first.  (α) a park on `c`'s seat before the rung
pass: the parked head `y` fits `c`, so `y` is a rank-`r−1`
opposite-colour live tenant; `ground_streak_founded` (above) bounds
the parked streak at depth two, and each parked member is at its own
foundation index by the window's `hsafe`-preservation (the
substitutions themselves never drop a live tenant's suit below its
rung: `foundTotal` only rises through them), so the park
*substitutes away* — raise the streak through the foundations
instead, the replay converging at the raise just as `g1_diamond`
exhibits two-way.  (β) a worry-back of `c`'s suit: B&G Cor. 2's
pointless-loop deletion — the worried card is re-raised later in the
same play (it must found) and the pair nets to identity on heights;
the one-move adjacent cancel is LANDED (`foundToTab_undo` /
`RevEqW`), the spread case carries `y`-blind segments by the B&G
Case-2 displacement.  (γ) a relocation of `c` before the raise: the
raise was available all along (the window's `nextUp c` never drops —
the c-suit height is frozen pre-pass by (β)), digs identically
(`g1_dig_parity`), and `c`-as-a-base was treated by (α).  Termination
is the B&G lexicographic `(noncompliant count, play length)`.

**The physical dividends** that make the port faithful rather than
mechanical: the reveal is part of the move (no dead-pile corner — the
locked-strand refutation of the old engine has no physical
analogue), pile-to-pile runs are first-class (a parked streak is ONE
move, not a climb of single-card relocations), and the foundation
shuttle is unconditional downwards (`foundToTab` needs only a
fitting seat — every physical run is whole-run transportable, where
the old engine's relocations were gated on heights).

**Refute-first gate** (the residue's own, individually probeable):
the negation shape is a WF `hsafe` corner state where EVERY winning
play carries a `groundBlocked` move before its first
`tabToFound c`.  The witness battery hunted exactly this: the
banned shapes are all LEGAL at the corner states (so the predicate
bans real moves, not ghosts) and every canonical replacement is
decide-live, the dig parity is decide-equal, and the streak-raise
channel runs end-to-end; no countermodel was found (the bounded-DFS
boundary is recorded).  TODO(proof). -/
theorem tabToFound_groundNormalForm {st : State} {c : Card} {k : Anchor}
    (hwf : st.WF) (hsafe : safeToFound st c = true)
    (hk : st.pileOfTop c = some k)
    (hnext : st.nextUp c = true)
    (hbare : chop (st.piles k).faceUp = [])
    (hcorner : (st.piles k).hidden ≠ [] ∨ c.rank ≠ Rank.king)
    (hsolv : WinFrom st) :
    ∃ π₁ π₂ w, st.run (π₁ ++ Move.tabToFound c :: π₂) = some w ∧ w.isWin = true ∧
      ∀ m ∈ π₁, m ≠ Move.tabToFound c ∧ Move.groundBlocked c m = false := sorry

/-! ### The ground replay (the mechanical half)

The divergence field a compliant prefix crosses: the replay state's
`c`-suit foundation runs one card ahead (the raise front-loaded),
its source pile `k` holds the revealed counterpart of `c`'s seat,
and everything else — the other suits, the other piles, the draw
zone — is verbatim.  `GroundSplit` packages the field; the step
lemma below carries it through every non-blocked move kind; the
convergence lemma closes it at the rung pass, where the source's
own `tabToFound c` writes exactly the field's ahead-half. -/

/-! ## Small local kit (dedup at harvest)

The five per-kind step inversions and the draw inversion are
re-proven here: `Orig.Irreversible` owns identical private copies
(this chapter sits above it but they are not importable), and this
chapter's reply needs them at full premise strength.  The list
helpers extend the `Orig.State` ones.  Promote or delete against
the canonical versions at the merge. -/

/-- A face-up singleton pile is not empty. -/
private theorem pile_isEmpty_false_of_faceUp {u : State} {c : Card} {k : Anchor}
    (hface : (u.piles k).faceUp = [c]) : (u.piles k).isEmpty = false := by
  cases hi : (u.piles k).isEmpty with
  | true =>
      obtain ⟨-, hfu⟩ := (Pile.isEmpty_eq _).mp hi
      rw [hface] at hfu
      exact absurd hfu (by simp)
  | false => rfl

/-- Waste-top tests agree on equal wastes. -/
private theorem wasteIs_congr {u v : State} {x : Card} (h : v.waste = u.waste) :
    v.wasteIs x = u.wasteIs x := by
  show (match v.waste with
    | [] => false
    | c' :: _ => decide (c' = x)) =
    (match u.waste with
    | [] => false
    | c' :: _ => decide (c' = x))
  rw [h]

/-- Next-up tests agree on equal suit foundations. -/
private theorem nextUp_congr_suit {u v : State} {x : Card} (h : v.found x.suit = u.found x.suit) :
    v.nextUp x = u.nextUp x := by
  show decide (x.rank.toIdx = (v.found x.suit).length)
      = decide (x.rank.toIdx = (u.found x.suit).length)
  rw [h]

/-- The face-up run of a run-removed pile keeps only cards of the
prefix it keeps (a reveal's fresh card is the one exception). -/
private theorem mem_afterRunRemoved_faceUp {p : Pile} {pre : List Card} {z : Card}
    (hmem : z ∈ (Pile.afterRunRemoved p pre).faceUp) :
    z ∈ pre ∨ (pre = [] ∧ ∃ h t, p.hidden = h :: t ∧ z = h) := by
  cases pre with
  | nil =>
      rcases p with ⟨hd, fl⟩
      cases hd with
      | nil =>
          have hcon : z ∈ ([] : List Card) := hmem
          cases hcon
      | cons h t =>
          have hrev : Pile.afterRunRemoved ⟨h :: t, fl⟩ ([] : List Card)
              = ⟨t, ([] : List Card) ++ [h]⟩ := rfl
          rw [hrev] at hmem
          have hz2 : z ∈ ([] : List Card) ++ [h] := hmem
          rw [List.nil_append] at hz2
          have hzh : z = h := List.mem_singleton.1 hz2
          refine Or.inr ⟨rfl, z, t, ?_, rfl⟩
          show h :: t = z :: t
          rw [hzh]
  | cons w ws =>
      rw [show Pile.afterRunRemoved p (w :: ws) = { p with faceUp := w :: ws } from rfl] at hmem
      exact Or.inl hmem

/-- The step's draw arm is the draw pipeline (definitionally). -/
private theorem g_step_draw_inv {st s' : State}
    (h : State.step st Move.draw = some s') : st.stepDraw = some s' := h

/-- A successful `.wasteToFound`. -/
private theorem g_step_wasteToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    st.wasteIs c = true ∧ st.nextUp c = true ∧
    ∃ ws, st.waste = c :: ws ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with waste := ws } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    rw [Bool.and_eq_true] at hg
    obtain ⟨hw, hn⟩ := hg
    split at h
    · rename_i c₀ ws hcon
      have hcc : c₀ = c := by
        have hwdec := State.wasteIs_cons hcon c
        rw [hwdec] at hw
        exact of_decide_eq_true hw
      subst hcc
      injection h with hEq
      exact ⟨hw, hn, ws, hcon, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToTab`. -/
private theorem g_step_wasteToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.wasteToTab c b) = some s') :
    st.wasteIs c = true ∧ st.canPlace c b = true ∧
    ∃ ws, st.waste = c :: ws ∧
      s' = { st.putCard c b with waste := ws } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    rw [Bool.and_eq_true] at hg
    obtain ⟨hw, hc⟩ := hg
    split at h
    · rename_i c₀ ws hcon
      have hcc : c₀ = c := by
        have hwdec := State.wasteIs_cons hcon c
        rw [hwdec] at hw
        exact of_decide_eq_true hw
      subst hcc
      injection h with hEq
      exact ⟨hw, hc, ws, hcon, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToFound`. -/
private theorem g_step_tabToFound_inv {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.tabToFound c) = some s') :
    st.nextUp c = true ∧
    ∃ a, st.pileOfTop c = some a ∧
      s' = { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' =>
               if a' = a then Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
               else st.piles a' } := by
  simp only [State.step] at h
  split at h
  · rename_i hn
    split at h
    · exact absurd h (by simp)
    · rename_i _ a hp
      injection h with hEq
      exact ⟨hn, a, hp, hEq.symm⟩
  · exact absurd h (by simp)

/-- A successful `.foundToTab`. -/
private theorem g_step_foundToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    ∃ c', st.foundTop c.suit = some c' ∧ c' = c ∧ st.canPlace c b = true ∧
      s' = (st.setFound c.suit (chop (st.found c.suit))).putCard c b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      injection h with hEq
      exact ⟨c', ht, of_decide_eq_true hg.1, hg.2, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToTab`. -/
private theorem g_step_tabToTab_inv {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.tabToTab c b) = some s') :
    ∃ a, st.pileHolding c = some a ∧ st.canPlace c b = true ∧
      fromCard c (st.piles a).faceUp ≠ [] ∧
        s' = (st.setPile a
            (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
              (fromCard c (st.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        injection h with hEq
        exact ⟨a, hh, hcp, hne, hEq.symm⟩
    · exact absurd h (by simp)

/-! ## The divergence field -/

/-- The replay side of a compliant prefix: the found `c.suit` runs
one card ahead, the other suits/piles/draw agree, and pile `k` holds
the revealed counterpart (`afterRunRemoved` of the source pile at
the empty chop). -/
private def GroundSplit (st : State) (c : Card) (k : Anchor) (u v : State) : Prop :=
  v.found c.suit = u.found c.suit ++ [c] ∧
  (∀ σ, σ ≠ c.suit → v.found σ = u.found σ) ∧
  u.found c.suit = st.found c.suit ∧
  v.stock = u.stock ∧ v.waste = u.waste ∧ v.drawStep = u.drawStep ∧
  (∀ a, a ≠ k → v.piles a = u.piles a) ∧
  u.piles k = st.piles k ∧
  v.piles k = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)

/-- The raise establishes the field at the start. -/
private theorem ground_split_init {st : State} {c : Card} {k : Anchor} {s₁ : State}
    (hk : st.pileOfTop c = some k)
    (hstep : State.step st (Move.tabToFound c) = some s₁) :
    GroundSplit st c k st s₁ := by
  have hs := tabToFound_shape hstep hk
  refine ⟨by rw [hs]; exact setFound_found_self, ?_, rfl,
    by rw [hs]; rfl, by rw [hs]; rfl, by rw [hs]; rfl, ?_, rfl, ?_⟩
  · intro σ hσ
    rw [hs]
    show (if σ = c.suit then st.found c.suit ++ [c] else st.found σ) = st.found σ
    rw [ite_eq_right hσ]
  · intro a ha
    rw [hs]
    show (if a = k then Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        else st.piles a) = st.piles a
    rw [ite_eq_right ha]
  · rw [hs]
    show (if k = k then Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        else st.piles k)
      = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
    rw [ite_eq_left rfl]

/-- The revealed counterpart's catalogue, component form: a pile
whose sole face-up run is `[c]`, run-removed at the empty chop, is
either fully empty or seats exactly the boundary card. -/
private theorem afterRunRemoved_bare_vshape {hd fl : List Card} {c : Card} {x : Pile}
    (hmk : x = Pile.afterRunRemoved ⟨hd, fl⟩ (chop fl))
    (hfl : fl = [c]) :
    x.faceUp = [] ∨
    ∃ fr tl, hd = fr :: tl ∧ x.faceUp = [fr] ∧ x.hidden = tl := by
  subst hmk
  rw [hfl]
  rw [show chop [c] = ([] : List Card) from rfl]
  cases hd with
  | nil =>
      exact Or.inl rfl
  | cons fr tl =>
      refine Or.inr ⟨fr, tl, rfl, ?_, ?_⟩
      · rfl
      · rfl

/-- The revealed counterpart's catalogue, state form. -/
private theorem ground_k_vshape {st : State} {c : Card} {k : Anchor} {v : State}
    (hface : (st.piles k).faceUp = [c])
    (hvk : v.piles k =
      Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)) :
    (v.piles k).faceUp = [] ∨
    ∃ fr tl, (st.piles k).hidden = fr :: tl ∧
      (v.piles k).faceUp = [fr] ∧ (v.piles k).hidden = tl :=
  afterRunRemoved_bare_vshape hvk hface

/-- The boundary card is hidden on the source side, so no search of
the source state can sit it anywhere (the `mem_hidden_only`
one-hidden-membership fence). -/
private theorem ground_fresh_elim {st : State} {k : Anchor} {u : State} {z : Card}
    (huwf : u.WF) (huk : u.piles k = st.piles k)
    (hz : z ∈ (st.piles k).hidden) {a : Anchor} (hmem : z ∈ (u.piles a).faceUp) : False := by
  have hz9 : z ∈ (u.piles k).hidden := by rw [huk]; exact hz
  have hfence := mem_hidden_only huwf hz9
  by_cases hak : a = k
  · rw [hak] at hmem
    exact absurd hmem hfence.2.1
  · exact absurd hmem (hfence.1 a hak).2

/-- The two searches agree on any card that is neither `c` nor
seated on the replay side of pile `k`. -/
private theorem ground_search_agree {st : State} {c : Card} {k : Anchor} {u v : State}
    {z : Card}
    (hsplit : GroundSplit st c k u v)
    (hface : (u.piles k).faceUp = [c])
    (hz : z ≠ c) (hzv : z ∉ (v.piles k).faceUp) :
    u.pileOfTop z = v.pileOfTop z ∧ u.pileHolding z = v.pileHolding z := by
  obtain ⟨-, -, -, -, -, -, hG, hH, -⟩ := hsplit
  have hpw : ∀ a,
      decide (u.topOf a = some z) = decide (v.topOf a = some z) ∧
      decide (z ∈ (u.piles a).faceUp) = decide (z ∈ (v.piles a).faceUp) := by
    intro a
    by_cases hak : a = k
    · rw [hak]
      have hut : u.topOf k = some c := by
        show lastOf (u.piles k).faceUp = some c
        rw [hface]
        rfl
      have hvut : v.topOf k ≠ some z := fun hcon => hzv (Pile.mem_of_top hcon)
      have huut : u.topOf k ≠ some z := by
        intro hcon
        rw [hut] at hcon
        exact hz (Option.some.inj hcon).symm
      refine ⟨by rw [decide_false_of_not huut, decide_false_of_not hvut], by
        rw [hface]
        rw [decide_false_of_not (fun hmem => hz (List.mem_singleton.1 hmem)),
          decide_false_of_not (fun hmem => hzv hmem)]⟩
    · have hpu : v.piles a = u.piles a := hG a hak
      exact ⟨by rw [show u.topOf a = lastOf (u.piles a).faceUp from rfl,
          show v.topOf a = lastOf (v.piles a).faceUp from rfl, ← hpu],
        by rw [← hpu]⟩
  have h1 : u.pileOfTop z = v.pileOfTop z := by
    show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all
      = firstWhere (fun a => decide (v.topOf a = some z)) Anchor.all
    exact firstWhere_congr (fun a => (hpw a).1)
  have h2 : u.pileHolding z = v.pileHolding z := by
    show firstWhere (fun a => decide (z ∈ (u.piles a).faceUp)) Anchor.all
      = firstWhere (fun a => decide (z ∈ (v.piles a).faceUp)) Anchor.all
    exact firstWhere_congr (fun a => (hpw a).2)
  exact ⟨h1, h2⟩

/-! ## The draw congruence

The draw pipeline reads exactly the draw zone (stock, waste, draw
step) — two states agreeing there draw to the same stock/waste
future, each keeping its own found and tableau. -/

/-- The recycle's branch catalogue. -/
private theorem recycle_fields (x : State) :
    (x.stock = [] → x.waste = [] → State.recycle x = x) ∧
    (x.stock = [] → x.waste ≠ [] →
      State.recycle x = { x with stock := x.waste.reverse, waste := [] }) ∧
    (x.stock ≠ [] → State.recycle x = x) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · show (match x.stock with
        | [] => match x.waste with
          | [] => x
          | w => { x with stock := w.reverse, waste := ([] : List Card) }
        | _ => x) = x
    rw [h1, h2]
  · show (match x.stock with
        | [] => match x.waste with
          | [] => x
          | w => { x with stock := w.reverse, waste := ([] : List Card) }
        | _ => x)
      = { x with stock := x.waste.reverse, waste := [] }
    rw [h1]
    show (match x.waste with
      | [] => x
      | w => { x with stock := w.reverse, waste := ([] : List Card) })
      = { x with stock := x.waste.reverse, waste := [] }
    cases hcon : x.waste with
    | nil =>
        rw [hcon] at h2
        exact absurd rfl h2
    | cons a as =>
        rfl
  · obtain ⟨a, as, hcon⟩ := list_cons_of_ne_nil h1
    show (match x.stock with
      | [] => match x.waste with
        | [] => x
        | w => { x with stock := w.reverse, waste := ([] : List Card) }
      | _ => x) = x
    rw [hcon]

/-- Two states with equal draw zones draw to the same dealt stock
and waste, each keeping its own found and tableau. -/
private theorem stepDraw_congr {x y : State}
    (hx1 : y.stock = x.stock) (hx2 : y.waste = x.waste) (hx3 : y.drawStep = x.drawStep)
    {s' : State} (hstep : State.step x Move.draw = some s') :
    State.step y Move.draw = some { s' with found := y.found, piles := y.piles } := by
  obtain ⟨r, hru, hrne, hshape⟩ := draw_unfold hstep
  have hrr : (State.recycle y).stock = (State.recycle x).stock ∧
      (State.recycle y).waste = (State.recycle x).waste ∧
      (State.recycle y).drawStep = (State.recycle x).drawStep ∧
      (State.recycle y).found = y.found ∧ (State.recycle y).piles = y.piles := by
    cases hs : y.stock with
    | nil =>
        cases hw : y.waste with
        | nil =>
            have hxs : x.stock = [] := hx1.symm.trans hs
            have hxw : x.waste = [] := hx2.symm.trans hw
            rw [(recycle_fields y).1 hs hw, (recycle_fields x).1 hxs hxw]
            exact ⟨hx1, hx2, hx3, rfl, rfl⟩
        | cons w ws =>
            have hxs : x.stock = [] := hx1.symm.trans hs
            have hxw : x.waste = w :: ws := hx2.symm.trans hw
            have hxr : State.recycle x =
                { x with stock := x.waste.reverse, waste := [] } :=
              (recycle_fields x).2.1 hxs (by rw [hxw]; simp)
            have hyr : State.recycle y =
                { y with stock := y.waste.reverse, waste := [] } :=
              (recycle_fields y).2.1 hs (by rw [hw]; simp)
            rw [hyr, hxr, hxw, hw]
            exact ⟨rfl, rfl, hx3, rfl, rfl⟩
    | cons a as =>
        have hxs : x.stock = a :: as := hx1.symm.trans hs
        have hxr : State.recycle x = x := (recycle_fields x).2.2 (by rw [hxs]; simp)
        have hyr : State.recycle y = y := (recycle_fields y).2.2 (by rw [hs]; simp)
        rw [hyr, hxr]
        exact ⟨hx1, hx2, hx3, rfl, rfl⟩
  have hvne : (State.recycle y).stock ≠ [] := by
    rw [hrr.1, hru]
    exact hrne
  show State.dealStock (State.recycle y) = _
  rw [dealStock_eq_of_ne_nil _ hvne]
  rw [hshape]
  rw [hrr.2.2.1, hrr.1, hrr.2.1, hrr.2.2.2.1, hrr.2.2.2.2, hru]

/-! ## The per-kind step lemmas -/

/-- **Kind draw**: the draw zone is one of the agreeing fields; both
threads deal the same cards onto the same zone, keeping their own
found and tableau. -/
private theorem ground_step_draw {st : State} {c : Card} {k : Anchor} {u v t : State}
    (hvwf : v.WF)
    (hsplit : GroundSplit st c k u v)
    (hstep : State.step u Move.draw = some t) :
    ∃ v', State.step v Move.draw = some v' ∧ GroundSplit st c k t v' ∧ v'.WF := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩ := hsplit
  have hd : State.step v Move.draw = some { t with found := v.found, piles := v.piles } :=
    stepDraw_congr hD hE hF hstep
  refine ⟨{ t with found := v.found, piles := v.piles }, hd, ?_, step_wf hvwf hd⟩
  have htf : t.found = u.found ∧ t.piles = u.piles ∧ t.drawStep = u.drawStep := by
    obtain ⟨r, hru, -, hshape⟩ := draw_unfold hstep
    rw [hshape]
    rw [← hru]
    cases hs : u.stock with
    | nil =>
        cases hw : u.waste with
        | nil => rw [(recycle_fields u).1 hs hw]; exact ⟨rfl, rfl, rfl⟩
        | cons w ws =>
            rw [(recycle_fields u).2.1 hs (by rw [hw]; simp)]
            exact ⟨rfl, rfl, rfl⟩
    | cons a as =>
        rw [(recycle_fields u).2.2 (by rw [hs]; simp)]
        exact ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · show v.found c.suit = t.found c.suit ++ [c]
    rw [htf.1]
    exact hA
  · intro σ hσ
    show v.found σ = t.found σ
    rw [htf.1]
    exact hB σ hσ
  · show t.found c.suit = st.found c.suit
    rw [htf.1]
    exact hC
  · intro a' ha'
    show v.piles a' = t.piles a'
    rw [htf.2.1]
    exact hG a' ha'
  · show t.piles k = st.piles k
    rw [htf.2.1]
    exact hH
  · show v.piles k = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
    exact hI

/-! ## The step lemma -/

/-- Two cards of one suit at one index are one card. -/
private theorem card_eq_of_suit_toIdx {x y : Card}
    (hs : x.suit = y.suit) (hi : x.rank.toIdx = y.rank.toIdx) : x = y := by
  obtain ⟨xs, xr⟩ := x
  obtain ⟨ys, yr⟩ := y
  simp only [Card.mk.injEq]
  exact ⟨hs, Rank.toIdx_inj hi⟩

/-- Inside the field the `c`-suit frontier is `c` itself: the field
freezes `u.found c.suit = st.found c.suit`, so the only stackable
card of `c`'s suit at an in-field source position is `c`. -/
private theorem ground_frontier_self {st u : State} {c x : Card}
    (hC : u.found c.suit = st.found c.suit)
    (hnextst : st.nextUp c = true)
    (hx : u.nextUp x = true) (hxs : x.suit = c.suit) : x = c := by
  have h1 : x.rank.toIdx = (u.found x.suit).length := of_decide_eq_true hx
  have h2 : (u.found x.suit).length = (st.found c.suit).length := by
    rw [hxs, hC]
  have h3 : c.rank.toIdx = (st.found c.suit).length :=
    (show st.foundHeight c.suit = (st.found c.suit).length from rfl) ▸
      of_decide_eq_true hnextst
  exact card_eq_of_suit_toIdx hxs (by omega)

/-- A successful waste raise is never of `c`'s suit: the frontier
argument plus the conservation fence. -/
private theorem ground_step_wasteToFound {st : State} {c : Card} {k : Anchor}
    {u v t : State} {x : Card}
    (huwf : u.WF) (hvwf : v.WF)
    (hnextst : st.nextUp c = true)
    (hface : (st.piles k).faceUp = [c])
    (hsplit : GroundSplit st c k u v)
    (hstep : State.step u (Move.wasteToFound x) = some t) :
    ∃ v', State.step v (Move.wasteToFound x) = some v' ∧
      GroundSplit st c k t v' ∧ v'.WF := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩ := hsplit
  obtain ⟨hwis, hnext, ws, hcon, hshape⟩ := g_step_wasteToFound_inv hstep
  have hfaceU : (u.piles k).faceUp = [c] := by rw [hH]; exact hface
  by_cases hxs : x.suit = c.suit
  · exfalso
    have hxc : x = c := ground_frontier_self hC hnextst hnext hxs
    rw [hxc] at hcon
    have hmemw : c ∈ u.waste := by
      show c ∈ u.waste
      rw [hcon]
      exact List.mem_cons_self
    have hmemf : c ∈ (u.piles k).faceUp := by
      rw [hfaceU]
      exact List.mem_cons_self
    exact absurd hmemw (mem_pile_unique huwf (Or.inr hmemf)).2.2.1
  · have hwisv : v.wasteIs x = true := by
      rw [wasteIs_congr hE]
      exact hwis
    have hnextv : v.nextUp x = true := by
      rw [nextUp_congr_suit (hB x.suit hxs)]
      exact hnext
    have hwv : v.waste = x :: ws := by rw [hE]; exact hcon
    have hstepv : State.step v (Move.wasteToFound x) =
        some { v.setFound x.suit (v.found x.suit ++ [x]) with waste := ws } := by
      show (if v.wasteIs x && v.nextUp x then
          match v.waste with
          | _ :: ws₀ => some { v.setFound x.suit (v.found x.suit ++ [x]) with waste := ws₀ }
          | [] => none
        else none) = _
      rw [hwisv, hnextv]
      split
      · rw [hwv]
      · rename_i hcon2
        simp at hcon2
    refine ⟨{ v.setFound x.suit (v.found x.suit ++ [x]) with waste := ws },
      hstepv, ?_, step_wf hvwf hstepv⟩
    · rw [hshape]
      have hnx : c.suit ≠ x.suit := fun hcon => hxs hcon.symm
      refine ⟨?_, ?_, ?_, hD, rfl, hF, ?_, ?_, ?_⟩
      · show (v.setFound x.suit (v.found x.suit ++ [x]) : State).found c.suit
          = (u.setFound x.suit (u.found x.suit ++ [x]) : State).found c.suit ++ [c]
        rw [setFound_found_ne hnx, setFound_found_ne hnx]
        exact hA
      · intro σ hσ
        show (v.setFound x.suit (v.found x.suit ++ [x]) : State).found σ
            = (u.setFound x.suit (u.found x.suit ++ [x]) : State).found σ
        by_cases hσx : σ = x.suit
        · subst hσx
          rw [setFound_found_self, setFound_found_self]
          rw [hB x.suit hxs]
        · rw [setFound_found_ne hσx, setFound_found_ne hσx]
          exact hB σ hσ
      · show (u.setFound x.suit (u.found x.suit ++ [x]) : State).found c.suit
          = st.found c.suit
        rw [setFound_found_ne hnx]
        exact hC
      · intro a' ha'
        show (v.setFound x.suit (v.found x.suit ++ [x]) : State).piles a'
            = (u.setFound x.suit (u.found x.suit ++ [x]) : State).piles a'
        rw [setFound_piles, setFound_piles]
        exact hG a' ha'
      · show (u.setFound x.suit (u.found x.suit ++ [x]) : State).piles k = st.piles k
        rw [setFound_piles]
        exact hH
      · show (v.setFound x.suit (v.found x.suit ++ [x]) : State).piles k
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [setFound_piles]
        exact hI

/-- **Kind `tabToFound` (a non-`c` raiser)**: the located pile is
off `k`, its reveal (if any) matches the replay side's, and the
raise of a foreign suit writes the same suit on both threads. -/
private theorem ground_step_tabToFound {st : State} {c : Card} {k : Anchor}
    {u v t : State} {x : Card}
    (huwf : u.WF) (hvwf : v.WF)
    (hnextst : st.nextUp c = true)
    (hface : (st.piles k).faceUp = [c])
    (hsplit : GroundSplit st c k u v)
    (hxc : x ≠ c)
    (hstep : State.step u (Move.tabToFound x) = some t) :
    ∃ v', State.step v (Move.tabToFound x) = some v' ∧
      GroundSplit st c k t v' ∧ v'.WF := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩ := hsplit
  obtain ⟨hnext, a, hsearch, hshape⟩ := g_step_tabToFound_inv hstep
  have hfaceU : (u.piles k).faceUp = [c] := by rw [hH]; exact hface
  by_cases hxs : x.suit = c.suit
  · exfalso
    exact hxc (ground_frontier_self hC hnextst hnext hxs)
  · have hak : a ≠ k := by
      intro hka
      have hs2 : u.pileOfTop x = some k := by rw [hsearch, hka]
      have htx : (u.piles k).top = some x := (pileOfTop_eq_some_iff huwf).mp hs2
      have htc : (u.piles k).top = some c := by
        show lastOf (u.piles k).faceUp = some c
        rw [hfaceU]
        rfl
      exact hxc (Option.some.inj (htx.symm.trans htc))
    have hxa : x ∉ (v.piles k).faceUp := by
      intro hmem
      obtain hvk2 | ⟨fr, tl, hfr, hvfr, -⟩ := ground_k_vshape (v := v) hface hI
      · rw [hvk2] at hmem
        cases hmem
      · have hzfr : x = fr := List.mem_singleton.1 (by rw [hvfr] at hmem; exact hmem)
        have hzst : x ∈ (st.piles k).hidden := by
          rw [hzfr, hfr]
          exact List.mem_cons_self
        have hxu : x ∈ (u.piles a).faceUp :=
          Pile.mem_of_top ((pileOfTop_eq_some_iff huwf).mp hsearch)
        exact ground_fresh_elim huwf hH hzst hxu
    obtain ⟨hsa1, -⟩ := ground_search_agree ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩
      (st := st) hfaceU hxc hxa
    have hvsearch : v.pileOfTop x = some a := by
      rw [← hsa1]
      exact hsearch
    have hnextv : v.nextUp x = true := by
      rw [nextUp_congr_suit (hB x.suit hxs)]
      exact hnext
    have hstepv : State.step v (Move.tabToFound x) =
        some { v.setFound x.suit (v.found x.suit ++ [x]) with
          piles := fun a' =>
            if a' = a then Pile.afterRunRemoved (v.piles a) (chop (v.piles a).faceUp)
            else v.piles a' } := by
      show (if v.nextUp x then
          match v.pileOfTop x with
          | none => none
          | some a₀ => some { v.setFound x.suit (v.found x.suit ++ [x]) with
              piles := fun a' =>
                if a' = a₀ then Pile.afterRunRemoved (v.piles a₀) (chop (v.piles a₀).faceUp)
                else v.piles a' }
          else none) = _
      rw [hnextv, hvsearch]
      rfl
    refine ⟨{ v.setFound x.suit (v.found x.suit ++ [x]) with
        piles := fun a' =>
          if a' = a then Pile.afterRunRemoved (v.piles a) (chop (v.piles a).faceUp)
          else v.piles a' }, hstepv, ?_, step_wf hvwf hstepv⟩
    · rw [hshape]
      have hnx : c.suit ≠ x.suit := fun hcon => hxs hcon.symm
      refine ⟨?_, ?_, ?_, hD, hE, hF, ?_, ?_, ?_⟩
      · show (v.setFound x.suit (v.found x.suit ++ [x]) : State).found c.suit
          = (u.setFound x.suit (u.found x.suit ++ [x]) : State).found c.suit ++ [c]
        rw [setFound_found_ne hnx, setFound_found_ne hnx]
        exact hA
      · intro σ hσ
        show (v.setFound x.suit (v.found x.suit ++ [x]) : State).found σ
            = (u.setFound x.suit (u.found x.suit ++ [x]) : State).found σ
        by_cases hσx : σ = x.suit
        · subst hσx
          rw [setFound_found_self, setFound_found_self, hB x.suit hxs]
        · rw [setFound_found_ne hσx, setFound_found_ne hσx]
          exact hB σ hσ
      · show (u.setFound x.suit (u.found x.suit ++ [x]) : State).found c.suit
          = st.found c.suit
        rw [setFound_found_ne hnx]
        exact hC
      · intro a' ha'
        show (if a' = a then Pile.afterRunRemoved (v.piles a) (chop (v.piles a).faceUp)
            else v.piles a')
            = (if a' = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
            else u.piles a')
        by_cases haa' : a' = a
        · rw [ite_eq_left haa', ite_eq_left haa', hG a hak]
        · rw [ite_eq_right haa', ite_eq_right haa']
          exact hG a' ha'
      · show (if k = a then Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
          else u.piles k) = st.piles k
        rw [ite_eq_right (fun hcon => hak hcon.symm)]
        exact hH
      · show (if k = a then Pile.afterRunRemoved (v.piles a) (chop (v.piles a).faceUp)
          else v.piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [ite_eq_right (fun hcon => hak hcon.symm)]
        exact hI

/-- The replay-side pile `k` seats only the boundary card, which is
hidden at the source — so no source search ever finds a card seated
on the replay side of `k`. -/
private theorem ground_seated_never_searches {st : State} {c : Card} {k : Anchor}
    {u v : State} {z : Card}
    (huwf : u.WF) (hface : (st.piles k).faceUp = [c])
    (huk : u.piles k = st.piles k)
    (hvk : v.piles k = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp))
    (hz : z ∈ (v.piles k).faceUp) :
    u.pileOfTop z = none ∧ u.pileHolding z = none := by
  obtain hvk2 | ⟨fr, tl, hfr, hvfr, -⟩ := ground_k_vshape (v := v) hface hvk
  · rw [hvk2] at hz
    exact absurd hz (by simp)
  · have hzfr : z = fr := List.mem_singleton.1 (by rw [hvfr] at hz; exact hz)
    have hzst : z ∈ (st.piles k).hidden := by
      rw [hzfr, hfr]
      exact List.mem_cons_self
    have hmemnone : ∀ a', z ∉ (u.piles a').faceUp := by
      intro a' hmem
      exact ground_fresh_elim huwf huk hzst hmem
    refine ⟨?_, ?_⟩
    · cases hsearch : u.pileOfTop z with
      | none => rfl
      | some a =>
          exfalso
          exact hmemnone a
            (Pile.mem_of_top ((pileOfTop_eq_some_iff huwf).mp hsearch))
    · cases hhold : u.pileHolding z with
      | none => rfl
      | some a =>
          exfalso
          exact hmemnone a (pileHolding_mem hhold)

/-- **Kind `wasteToTab`**: a landing never touches pile `k` (it is
nonempty at the source, and the block set removes `c`'s seat from
the legal bases), so the placement replays verbatim. -/
private theorem ground_step_wasteToTab {st : State} {c : Card} {k : Anchor}
    {u v t : State} {x : Card} {b : Base}
    (huwf : u.WF) (hvwf : v.WF)
    (hface : (st.piles k).faceUp = [c])
    (hsplit : GroundSplit st c k u v)
    (hnblk : Move.groundBlocked c (Move.wasteToTab x b) = false)
    (hstep : State.step u (Move.wasteToTab x b) = some t) :
    ∃ v', State.step v (Move.wasteToTab x b) = some v' ∧
      GroundSplit st c k t v' ∧ v'.WF := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩ := hsplit
  obtain ⟨hwis, hcp, ws, hcon, hshape⟩ := g_step_wasteToTab_inv hstep
  have hfaceU : (u.piles k).faceUp = [c] := by rw [hH]; exact hface
  have hwisv : v.wasteIs x = true := by rw [wasteIs_congr hE]; exact hwis
  have hwv : v.waste = x :: ws := by rw [hE]; exact hcon
  cases b with
  | inl a =>
      obtain ⟨hemp, hking⟩ := canPlace_inl hcp
      have hak : a ≠ k := by
        intro hka
        rw [hka] at hemp
        rw [pile_isEmpty_false_of_faceUp hfaceU] at hemp
        exact absurd hemp (by simp)
      have hkd : decide (x.rank = Rank.king) = true := decide_eq_true hking
      have hvcp : v.canPlace x (Sum.inl a) = true := by
        show ((v.piles a).isEmpty && decide (x.rank = Rank.king)) = true
        rw [hG a hak, hemp, hkd]
        rfl
      have hstepv : State.step v (Move.wasteToTab x (Sum.inl a)) =
          some { v.putCard x (Sum.inl a) with waste := ws } := by
        show (if v.wasteIs x && v.canPlace x (Sum.inl a) then
            match v.waste with
            | _ :: ws₀ => some { v.putCard x (Sum.inl a) with waste := ws₀ }
            | [] => none
          else none) = _
        rw [hwisv, hvcp]
        split
        · rw [hwv]
        · rename_i hcon2
          simp at hcon2
      refine ⟨{ v.putCard x (Sum.inl a) with waste := ws }, hstepv, ?_,
        step_wf hvwf hstepv⟩
      rw [hshape]
      refine ⟨?_, ?_, ?_, hD, rfl, hF, ?_, ?_, ?_⟩
      · show (v.putCard x (Sum.inl a) : State).found c.suit
          = (u.putCard x (Sum.inl a) : State).found c.suit ++ [c]
        rw [putCard_keep.1, putCard_keep.1]
        exact hA
      · intro σ hσ
        show (v.putCard x (Sum.inl a) : State).found σ
            = (u.putCard x (Sum.inl a) : State).found σ
        rw [putCard_keep.1, putCard_keep.1]
        exact hB σ hσ
      · show (u.putCard x (Sum.inl a) : State).found c.suit = st.found c.suit
        rw [putCard_keep.1]
        exact hC
      · intro a' ha'
        show (v.putCard x (Sum.inl a) : State).piles a'
            = (u.putCard x (Sum.inl a) : State).piles a'
        rw [putCard_piles_inl, putCard_piles_inl]
        show (if a' = a then ⟨[], [x]⟩ else v.piles a')
            = (if a' = a then ⟨[], [x]⟩ else u.piles a')
        by_cases haa' : a' = a
        · rw [ite_eq_left haa', ite_eq_left haa']
        · rw [ite_eq_right haa', ite_eq_right haa']
          exact hG a' ha'
      · show (u.putCard x (Sum.inl a) : State).piles k = st.piles k
        rw [putCard_piles_inl]
        show (if k = a then ⟨[], [x]⟩ else u.piles k) = st.piles k
        rw [ite_eq_right (fun hcon => hak hcon.symm)]
        exact hH
      · show (v.putCard x (Sum.inl a) : State).piles k
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [putCard_piles_inl]
        show (if k = a then ⟨[], [x]⟩ else v.piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [ite_eq_right (fun hcon => hak hcon.symm)]
        exact hI
  | inr z =>
      have hzc : z ≠ c := by
        intro hcon
        have hblk : Move.groundBlocked c (Move.wasteToTab x (Sum.inr z)) = true :=
          show (match Move.wasteToTab x (Sum.inr z) with
            | .wasteToTab _ b₀ => decide (b₀ = Sum.inr c)
            | _ => false) = true from by
            rw [show (Sum.inr z : Base) = Sum.inr c from congrArg Sum.inr hcon]
            exact decide_eq_true rfl
        exact absurd hblk (by rw [hnblk]; simp)
      obtain ⟨q, hqu, hfit⟩ := canPlace_inr hcp
      have hzv : z ∉ (v.piles k).faceUp := by
        intro hmem
        obtain ⟨hnone1, -⟩ := ground_seated_never_searches huwf hface hH hI hmem
        exact absurd hqu (by rw [hnone1]; simp)
      have hqk : q ≠ k := by
        intro hkq
        have hs2 : u.pileOfTop z = some k := by rw [hqu, hkq]
        have htx : (u.piles k).top = some z := (pileOfTop_eq_some_iff huwf).mp hs2
        have htc : (u.piles k).top = some c := by
          show lastOf (u.piles k).faceUp = some c
          rw [hfaceU]
          rfl
        exact hzc (Option.some.inj (htx.symm.trans htc))
      obtain ⟨hag1, -⟩ := ground_search_agree ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩
        (st := st) hfaceU hzc hzv
      have hvsearch : v.pileOfTop z = some q := by
        rw [← hag1]
        exact hqu
      have hvcp : v.canPlace x (Sum.inr z) = true := by
        show (match v.pileOfTop z with
          | some _ => canSitOn x z
          | none => false) = true
        rw [hvsearch]
        exact hfit
      have hstepv : State.step v (Move.wasteToTab x (Sum.inr z)) =
          some { v.putCard x (Sum.inr z) with waste := ws } := by
        show (if v.wasteIs x && v.canPlace x (Sum.inr z) then
            match v.waste with
            | _ :: ws₀ => some { v.putCard x (Sum.inr z) with waste := ws₀ }
            | [] => none
          else none) = _
        rw [hwisv, hvcp]
        split
        · rw [hwv]
        · rename_i hcon2
          simp at hcon2
      refine ⟨{ v.putCard x (Sum.inr z) with waste := ws }, hstepv, ?_,
        step_wf hvwf hstepv⟩
      rw [hshape]
      have hplv : (v.putCard x (Sum.inr z)).piles =
          (fun a' => if a' = q then { v.piles q with faceUp := (v.piles q).faceUp ++ [x] }
            else v.piles a') :=
        putCard_piles_inr v x z q hvsearch
      have hplu : (u.putCard x (Sum.inr z)).piles =
          (fun a' => if a' = q then { u.piles q with faceUp := (u.piles q).faceUp ++ [x] }
            else u.piles a') :=
        putCard_piles_inr u x z q hqu
      refine ⟨?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
      · show (v.putCard x (Sum.inr z) : State).found c.suit
          = (u.putCard x (Sum.inr z) : State).found c.suit ++ [c]
        rw [putCard_keep.1, putCard_keep.1]
        exact hA
      · intro σ hσ
        show (v.putCard x (Sum.inr z) : State).found σ
            = (u.putCard x (Sum.inr z) : State).found σ
        rw [putCard_keep.1, putCard_keep.1]
        exact hB σ hσ
      · show (u.putCard x (Sum.inr z) : State).found c.suit = st.found c.suit
        rw [putCard_keep.1]
        exact hC
      · show (v.putCard x (Sum.inr z) : State).stock
            = (u.putCard x (Sum.inr z) : State).stock
        rw [putCard_stock, putCard_stock]
        exact hD
      · show (v.putCard x (Sum.inr z) : State).drawStep
            = (u.putCard x (Sum.inr z) : State).drawStep
        rw [putCard_keep.2.2.2, putCard_keep.2.2.2]
        exact hF
      · intro a' ha'
        show (v.putCard x (Sum.inr z) : State).piles a'
            = (u.putCard x (Sum.inr z) : State).piles a'
        rw [hplv, hplu]
        show (if a' = q then { v.piles q with faceUp := (v.piles q).faceUp ++ [x] }
            else v.piles a')
            = (if a' = q then { u.piles q with faceUp := (u.piles q).faceUp ++ [x] }
            else u.piles a')
        by_cases haa' : a' = q
        · rw [ite_eq_left haa', ite_eq_left haa', hG q hqk]
        · rw [ite_eq_right haa', ite_eq_right haa']
          exact hG a' ha'
      · show (u.putCard x (Sum.inr z) : State).piles k = st.piles k
        rw [hplu]
        show (if k = q then { u.piles q with faceUp := (u.piles q).faceUp ++ [x] }
            else u.piles k) = st.piles k
        rw [ite_eq_right (fun hcon => hqk hcon.symm)]
        exact hH
      · show (v.putCard x (Sum.inr z) : State).piles k
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [hplv]
        show (if k = q then { v.piles q with faceUp := (v.piles q).faceUp ++ [x] }
            else v.piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [ite_eq_right (fun hcon => hqk hcon.symm)]
        exact hI

/-! ## The step lemma -/

/-- A false disjunct split (a tiny local Bool helper). -/
private theorem boolOrFalse {b₁ b₂ : Bool} (h : (b₁ || b₂) = false) :
    b₁ = false ∧ b₂ = false := by
  cases b₁ with
  | true => rw [Bool.true_or] at h; exact absurd h (by simp)
  | false =>
      cases b₂ with
      | true => rw [Bool.false_or] at h; exact absurd h (by simp)
      | false => exact ⟨rfl, rfl⟩

/-- `putRun` keeps the founds regardless of the landing's shape. -/
private theorem g_putRun_found (st : State) (run : List Card) (b : Base) :
    (st.putRun run b).found = st.found := by
  cases b with
  | inl a => rfl
  | inr z =>
      cases hz : st.pileOfTop z with
      | none =>
          simp only [State.putRun, hz]
      | some k₂ =>
          simp only [State.putRun, hz]
          rfl

/-- **Kind `foundToTab`**: the block set removes the worry of `c`'s
own suit entirely, and any other suit's worry lands off `k` — the
chopped prefix write and the placement both replay verbatim. -/
private theorem ground_step_foundToTab {st : State} {c : Card} {k : Anchor}
    {u v t : State} {x : Card} {b : Base}
    (huwf : u.WF) (hvwf : v.WF)
    (hface : (st.piles k).faceUp = [c])
    (hsplit : GroundSplit st c k u v)
    (hnblk : Move.groundBlocked c (Move.foundToTab x b) = false)
    (hstep : State.step u (Move.foundToTab x b) = some t) :
    ∃ v', State.step v (Move.foundToTab x b) = some v' ∧
      GroundSplit st c k t v' ∧ v'.WF := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩ := hsplit
  obtain ⟨c₀, htop, hceq, hcp, hshape⟩ := g_step_foundToTab_inv hstep
  rw [hceq] at htop
  have hfaceU : (u.piles k).faceUp = [c] := by rw [hH]; exact hface
  have hbb : (decide (x.suit = c.suit) || decide (b = Sum.inr c)) = false := hnblk
  obtain ⟨hf1, hf2⟩ := boolOrFalse hbb
  have hxsc : x.suit ≠ c.suit := by
    intro hcon
    have hd : decide (x.suit = c.suit) = true := by rw [hcon]; exact decide_eq_true rfl
    rw [hf1] at hd
    exact absurd hd (by simp)
  have hnx : c.suit ≠ x.suit := fun hcon => hxsc hcon.symm
  have htopv : v.foundTop x.suit = some x := by
    show lastOf (v.found x.suit) = some x
    rw [hB x.suit hxsc]
    exact htop
  cases b with
  | inl a =>
      obtain ⟨hemp, hking⟩ := canPlace_inl hcp
      have hak : a ≠ k := by
        intro hka
        rw [hka] at hemp
        rw [pile_isEmpty_false_of_faceUp hfaceU] at hemp
        exact absurd hemp (by simp)
      have hkd : decide (x.rank = Rank.king) = true := decide_eq_true hking
      have hvcp : v.canPlace x (Sum.inl a) = true := by
        show ((v.piles a).isEmpty && decide (x.rank = Rank.king)) = true
        rw [hG a hak, hemp, hkd]
        rfl
      have hstepv : State.step v (Move.foundToTab x (Sum.inl a)) =
          some ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a)) := by
        show (match v.foundTop x.suit with
          | some c₀' =>
              if decide (c₀' = x) && v.canPlace x (Sum.inl a) then
                some ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a))
              else none
          | none => none) = _
        rw [htopv]
        show (if (decide (x = x) && v.canPlace x (Sum.inl a)) = true then
              some ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a))
            else none) = _
        rw [show (decide (x = x) && v.canPlace x (Sum.inl a)) = true from by
              rw [decide_eq_true rfl, hvcp]
              rfl]
        rfl
      refine ⟨(v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a),
        hstepv, ?_, step_wf hvwf hstepv⟩
      rw [hshape]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a) : State).found c.suit
          = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).found c.suit
            ++ [c]
        rw [putCard_keep.1, putCard_keep.1, setFound_found_ne hnx, setFound_found_ne hnx]
        exact hA
      · intro σ hσ
        show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a) : State).found σ
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).found σ
        rw [putCard_keep.1, putCard_keep.1]
        by_cases hσx : σ = x.suit
        · subst hσx
          rw [setFound_found_self, setFound_found_self, hB x.suit hxsc]
        · rw [setFound_found_ne hσx, setFound_found_ne hσx]
          exact hB σ hσ
      · show ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).found c.suit
          = st.found c.suit
        rw [putCard_keep.1, setFound_found_ne hnx]
        exact hC
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a) : State).stock
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).stock
        rw [putCard_stock, putCard_stock, setFound_stock, setFound_stock]
        exact hD
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a) : State).waste
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).waste
        rw [putCard_waste, putCard_waste, setFound_waste, setFound_waste]
        exact hE
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a) : State).drawStep
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).drawStep
        rw [putCard_keep.2.2.2, putCard_keep.2.2.2, setFound_drawStep, setFound_drawStep]
        exact hF
      · intro a' ha'
        show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a) : State).piles a'
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).piles a'
        rw [putCard_piles_inl, putCard_piles_inl]
        show (if a' = a then ⟨[], [x]⟩ else v.piles a')
            = (if a' = a then ⟨[], [x]⟩ else u.piles a')
        by_cases haa' : a' = a
        · rw [ite_eq_left haa', ite_eq_left haa']
        · rw [ite_eq_right haa', ite_eq_right haa']
          exact hG a' ha'
      · show ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inl a) : State).piles k
            = st.piles k
        rw [putCard_piles_inl]
        show (if k = a then ⟨[], [x]⟩
            else (u.setFound x.suit (chop (u.found x.suit)) : State).piles k) = st.piles k
        rw [ite_eq_right (fun hcon => hak hcon.symm)]
        rw [setFound_piles]
        exact hH
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inl a) : State).piles k
            = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [putCard_piles_inl]
        show (if k = a then ⟨[], [x]⟩
            else (v.setFound x.suit (chop (v.found x.suit)) : State).piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [ite_eq_right (fun hcon => hak hcon.symm)]
        rw [setFound_piles]
        exact hI
  | inr z =>
      have hzc : z ≠ c := by
        intro hcon
        have hbd : decide (Sum.inr z = Sum.inr c) = true :=
          decide_eq_true (congrArg (f := fun (w : Card) => (Sum.inr w : Base)) hcon)
        rw [hf2] at hbd
        exact absurd hbd (by simp)
      obtain ⟨q, hqu, hfit⟩ := canPlace_inr hcp
      have hzv : z ∉ (v.piles k).faceUp := by
        intro hmem
        obtain ⟨hnone1, -⟩ := ground_seated_never_searches huwf hface hH hI hmem
        exact absurd hqu (by rw [hnone1]; simp)
      have hqk : q ≠ k := by
        intro hkq
        have hs2 : u.pileOfTop z = some k := by rw [hqu, hkq]
        have htx : (u.piles k).top = some z := (pileOfTop_eq_some_iff huwf).mp hs2
        have htc : (u.piles k).top = some c := by
          show lastOf (u.piles k).faceUp = some c
          rw [hfaceU]
          rfl
        exact hzc (Option.some.inj (htx.symm.trans htc))
      obtain ⟨hag1, -⟩ := ground_search_agree ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩
        (st := st) hfaceU hzc hzv
      have hvsearch : v.pileOfTop z = some q := by
        rw [← hag1]
        exact hqu
      have hvcp : v.canPlace x (Sum.inr z) = true := by
        show (match v.pileOfTop z with
          | some _ => canSitOn x z
          | none => false) = true
        rw [hvsearch]
        exact hfit
      have hstepv : State.step v (Move.foundToTab x (Sum.inr z)) =
          some ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z)) := by
        show (match v.foundTop x.suit with
          | some c₀' =>
              if decide (c₀' = x) && v.canPlace x (Sum.inr z) then
                some ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z))
              else none
          | none => none) = _
        rw [htopv]
        show (if (decide (x = x) && v.canPlace x (Sum.inr z)) = true then
              some ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z))
            else none) = _
        rw [show (decide (x = x) && v.canPlace x (Sum.inr z)) = true from by
              rw [decide_eq_true rfl, hvcp]
              rfl]
        rfl
      refine ⟨(v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z),
        hstepv, ?_, step_wf hvwf hstepv⟩
      rw [hshape]
      have hplv : ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z)).piles =
          (fun a' => if a' = q then { v.piles q with faceUp := (v.piles q).faceUp ++ [x] }
            else v.piles a') :=
        putCard_piles_inr (v.setFound x.suit (chop (v.found x.suit))) x z q hvsearch
      have hplu : ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z)).piles =
          (fun a' => if a' = q then { u.piles q with faceUp := (u.piles q).faceUp ++ [x] }
            else u.piles a') :=
        putCard_piles_inr (u.setFound x.suit (chop (u.found x.suit))) x z q hqu
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z) : State).found c.suit
          = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).found c.suit
            ++ [c]
        rw [putCard_keep.1, putCard_keep.1, setFound_found_ne hnx, setFound_found_ne hnx]
        exact hA
      · intro σ hσ
        show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z) : State).found σ
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).found σ
        rw [putCard_keep.1, putCard_keep.1]
        by_cases hσx : σ = x.suit
        · subst hσx
          rw [setFound_found_self, setFound_found_self, hB x.suit hxsc]
        · rw [setFound_found_ne hσx, setFound_found_ne hσx]
          exact hB σ hσ
      · show ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).found c.suit
          = st.found c.suit
        rw [putCard_keep.1, setFound_found_ne hnx]
        exact hC
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z) : State).stock
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).stock
        rw [putCard_stock, putCard_stock, setFound_stock, setFound_stock]
        exact hD
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z) : State).waste
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).waste
        rw [putCard_waste, putCard_waste, setFound_waste, setFound_waste]
        exact hE
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z) : State).drawStep
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).drawStep
        rw [putCard_keep.2.2.2, putCard_keep.2.2.2, setFound_drawStep, setFound_drawStep]
        exact hF
      · intro a' ha'
        show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z) : State).piles a'
            = ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).piles a'
        rw [hplv, hplu]
        show (if a' = q then { v.piles q with faceUp := (v.piles q).faceUp ++ [x] }
            else v.piles a')
            = (if a' = q then { u.piles q with faceUp := (u.piles q).faceUp ++ [x] }
            else u.piles a')
        by_cases haa' : a' = q
        · rw [ite_eq_left haa', ite_eq_left haa', hG q hqk]
        · rw [ite_eq_right haa', ite_eq_right haa']
          exact hG a' ha'
      · show ((u.setFound x.suit (chop (u.found x.suit))).putCard x (Sum.inr z) : State).piles k
            = st.piles k
        rw [hplu]
        show (if k = q then
              { (u.setFound x.suit (chop (u.found x.suit)) : State).piles q with
                faceUp := ((u.setFound x.suit (chop (u.found x.suit)) : State).piles q).faceUp ++ [x] }
            else (u.setFound x.suit (chop (u.found x.suit)) : State).piles k) = st.piles k
        rw [ite_eq_right (fun hcon => hqk hcon.symm)]
        rw [setFound_piles]
        exact hH
      · show ((v.setFound x.suit (chop (v.found x.suit))).putCard x (Sum.inr z) : State).piles k
            = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [hplv]
        show (if k = q then
              { (v.setFound x.suit (chop (v.found x.suit)) : State).piles q with
                faceUp := ((v.setFound x.suit (chop (v.found x.suit)) : State).piles q).faceUp ++ [x] }
            else (v.setFound x.suit (chop (v.found x.suit)) : State).piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [ite_eq_right (fun hcon => hqk hcon.symm)]
        rw [setFound_piles]
        exact hI

/-! ## The step lemma -/

/-- A `firstWhere` answer satisfies its own test (a bare soundness
copy of the `Integrity` internal; the carrier states of a run move
are not `WF`, so the exact search fact must not demand it). -/
private theorem g_pileOfTop_sound {st : State} {z : Card} {a : Anchor}
    (h : st.pileOfTop z = some a) : (st.piles a).top = some z := by
  have hs : decide (st.topOf a = some z) = true :=
    firstWhere_sound (p := fun a' => decide (st.topOf a' = some z)) h
  show lastOf (st.piles a).faceUp = some z
  show st.topOf a = some z
  exact of_decide_eq_true hs

/-- **Kind `tabToTab`**: the block set removes `c`'s own moves
entirely; a run head off `k` never reads the divergence, and the
putRun landing is located by a search that agrees through the
setPile carrier (the divergence field persists under the run move's
write). -/
private theorem ground_step_tabToTab {st : State} {c : Card} {k : Anchor}
    {u v t : State} {x : Card} {b : Base}
    (huwf : u.WF) (hvwf : v.WF)
    (hface : (st.piles k).faceUp = [c])
    (hsplit : GroundSplit st c k u v)
    (hnblk : Move.groundBlocked c (Move.tabToTab x b) = false)
    (hstep : State.step u (Move.tabToTab x b) = some t) :
    ∃ v', State.step v (Move.tabToTab x b) = some v' ∧
      GroundSplit st c k t v' ∧ v'.WF := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩ := hsplit
  obtain ⟨a, hhold, hcp, hrn, hshape⟩ := g_step_tabToTab_inv hstep
  have hfaceU : (u.piles k).faceUp = [c] := by rw [hH]; exact hface
  have hbb : (decide (x = c) || decide (b = Sum.inr c)) = false := hnblk
  obtain ⟨hf1, hf2⟩ := boolOrFalse hbb
  have hxc : x ≠ c := by
    intro hcon
    have hd : decide (x = c) = true := by rw [hcon]; exact decide_eq_true rfl
    rw [hf1] at hd
    exact absurd hd (by simp)
  have hak : a ≠ k := by
    intro hka
    have hmem : x ∈ (u.piles k).faceUp := pileHolding_mem (by rw [hhold, hka])
    rw [hfaceU] at hmem
    exact hxc (List.mem_singleton.1 hmem)
  have hpa : v.piles a = u.piles a := hG a hak
  have hQ : Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
      = Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp) := by rw [hpa]
  have hrun : fromCard x (v.piles a).faceUp = fromCard x (u.piles a).faceUp := by rw [hpa]
  have hxa : x ∉ (v.piles k).faceUp := by
    intro hmem
    obtain ⟨-, hnone2⟩ := ground_seated_never_searches huwf hface hH hI hmem
    exact absurd hhold (by rw [hnone2]; simp)
  obtain ⟨-, hag2⟩ := ground_search_agree ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩
    (st := st) hfaceU hxc hxa
  have hholdv : v.pileHolding x = some a := by
    rw [← hag2]
    exact hhold
  have hrnv : fromCard x (v.piles a).faceUp ≠ [] := by rw [hpa]; exact hrn
  -- the setPile carriers stay in the field
  have hsplmid : GroundSplit st c k
      (u.setPile a (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)))
      (v.setPile a (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))) := by
    refine ⟨hA, hB, hC, hD, hE, hF, ?_, ?_, ?_⟩
    · intro a' ha'
      show (if a' = a then
              Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
            else v.piles a')
          = (if a' = a then
              Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
            else u.piles a')
      by_cases haa' : a' = a
      · rw [ite_eq_left haa', ite_eq_left haa', hQ]
      · rw [ite_eq_right haa', ite_eq_right haa']
        exact hG a' ha'
    · show (u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles k
          = st.piles k
      rw [setPile_piles]
      show (if k = a then Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
          else u.piles k) = st.piles k
      rw [ite_eq_right (fun hcon => hak hcon.symm)]
      exact hH
    · show (v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles k
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      rw [setPile_piles]
      show (if k = a then Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
          else v.piles k)
        = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
      rw [ite_eq_right (fun hcon => hak hcon.symm)]
      exact hI
  -- the two notable carrier searches agree (pile k keeps its two
  -- shapes through the run-removal write)
  have hfaceU₀ : ((u.setPile a
      (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles k).faceUp
        = [c] := by
    show (if k = a then
            Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
          else u.piles k).faceUp = [c]
    rw [ite_eq_right (fun hcon => hak hcon.symm)]
    exact hfaceU
  have hGc : ∀ a', a' ≠ k →
      (v.setPile a (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles a'
        = (u.setPile a (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles a' :=
    hsplmid.2.2.2.2.2.2.1
  cases b with
  | inl a₂ =>
      obtain ⟨hemp, hking⟩ := canPlace_inl hcp
      have hak₂ : a₂ ≠ k := by
        intro hka
        rw [hka] at hemp
        rw [pile_isEmpty_false_of_faceUp hfaceU] at hemp
        exact absurd hemp (by simp)
      have hkd : decide (x.rank = Rank.king) = true := decide_eq_true hking
      have hvcp : v.canPlace x (Sum.inl a₂) = true := by
        show ((v.piles a₂).isEmpty && decide (x.rank = Rank.king)) = true
        rw [hG a₂ hak₂, hemp, hkd]
        rfl
      have hstepv : State.step v (Move.tabToTab x (Sum.inl a₂)) =
          some ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂)) := by
        show (match v.pileHolding x with
          | none => none
          | some a₀ =>
              if v.canPlace x (Sum.inl a₂) then
                match fromCard x (v.piles a₀).faceUp with
                | [] => none
                | r =>
                    some ((v.setPile a₀
                      (Pile.afterRunRemoved (v.piles a₀) (below x (v.piles a₀).faceUp))).putRun
                      r (Sum.inl a₂))
              else none) = _
        rw [hholdv, hvcp]
        show (match fromCard x (v.piles a).faceUp with
              | [] => none
              | r =>
                  some ((v.setPile a
                    (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                    r (Sum.inl a₂))) = _
        cases hfc : fromCard x (v.piles a).faceUp with
        | nil => exact absurd hfc hrnv
        | cons hdt rest =>
            rfl
      refine ⟨(v.setPile a
          (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
          (fromCard x (v.piles a).faceUp) (Sum.inl a₂), hstepv, ?_, step_wf hvwf hstepv⟩
      rw [hshape]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂) : State).found c.suit
          = ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).found c.suit ++ [c]
        rw [g_putRun_found, g_putRun_found, setPile_found, setPile_found]
        exact hA
      · intro σ hσ
        show ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂) : State).found σ
          = ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).found σ
        rw [g_putRun_found, g_putRun_found, setPile_found, setPile_found]
        exact hB σ hσ
      · show ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).found c.suit
          = st.found c.suit
        rw [g_putRun_found, setPile_found]
        exact hC
      · show ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂) : State).stock
          = ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).stock
        rw [putRun_stock, putRun_stock, setPile_stock, setPile_stock]
        exact hD
      · show ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂) : State).waste
          = ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).waste
        rw [putRun_waste, putRun_waste, setPile_waste, setPile_waste]
        exact hE
      · show ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂) : State).drawStep
          = ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).drawStep
        rw [putRun_drawStep, putRun_drawStep, setPile_drawStep, setPile_drawStep]
        exact hF
      · intro a' ha'
        show ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂) : State).piles a'
          = ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).piles a'
        rw [putRun_piles_inl, putRun_piles_inl]
        show (if a' = a₂ then ⟨[], fromCard x (v.piles a).faceUp⟩
            else if a' = a then
              Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
            else v.piles a')
            = (if a' = a₂ then ⟨[], fromCard x (u.piles a).faceUp⟩
            else if a' = a then
              Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
            else u.piles a')
        by_cases h2 : a' = a₂
        · rw [ite_eq_left h2, ite_eq_left h2, hrun]
        · rw [ite_eq_right h2, ite_eq_right h2]
          by_cases h3 : a' = a
          · rw [ite_eq_left h3, ite_eq_left h3, hQ]
          · rw [ite_eq_right h3, ite_eq_right h3]
            exact hG a' ha'
      · show ((u.setPile a
            (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
            (fromCard x (u.piles a).faceUp) (Sum.inl a₂) : State).piles k = st.piles k
        rw [putRun_piles_inl]
        show (if k = a₂ then ⟨[], fromCard x (u.piles a).faceUp⟩
            else if k = a then
              Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
            else u.piles k) = st.piles k
        rw [ite_eq_right (fun hcon => hak₂ hcon.symm),
          ite_eq_right (fun hcon => hak hcon.symm)]
        exact hH
      · show ((v.setPile a
            (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
            (fromCard x (v.piles a).faceUp) (Sum.inl a₂) : State).piles k
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [putRun_piles_inl]
        show (if k = a₂ then ⟨[], fromCard x (v.piles a).faceUp⟩
            else if k = a then
              Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
            else v.piles k)
          = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
        rw [ite_eq_right (fun hcon => hak₂ hcon.symm),
          ite_eq_right (fun hcon => hak hcon.symm)]
        exact hI
  | inr z =>
      have hzc : z ≠ c := by
        intro hcon
        have hbd : decide (Sum.inr z = Sum.inr c) = true :=
          decide_eq_true (congrArg (f := fun (w : Card) => (Sum.inr w : Base)) hcon)
        rw [hf2] at hbd
        exact absurd hbd (by simp)
      obtain ⟨q, hqu, hfit⟩ := canPlace_inr hcp
      have hzv : z ∉ (v.piles k).faceUp := by
        intro hmem
        obtain ⟨hnone1, -⟩ := ground_seated_never_searches huwf hface hH hI hmem
        exact absurd hqu (by rw [hnone1]; simp)
      obtain ⟨hag1, -⟩ := ground_search_agree ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩
        (st := st) hfaceU hzc hzv
      have hvsearch : v.pileOfTop z = some q := by
        rw [← hag1]
        exact hqu
      have hvcp : v.canPlace x (Sum.inr z) = true := by
        show (match v.pileOfTop z with
          | some _ => canSitOn x z
          | none => false) = true
        rw [hvsearch]
        exact hfit
      have hzv₀ : z ∉ ((v.setPile a
          (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles k).faceUp := by
        show z ∉ (if k = a then
              Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
            else v.piles k).faceUp
        rw [ite_eq_right (fun hcon => hak hcon.symm)]
        exact hzv
      obtain ⟨hag0, -⟩ := ground_search_agree hsplmid (st := st) hfaceU₀ hzc hzv₀
      cases hsea₀ : (u.setPile a
          (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).pileOfTop z
      with
      | none =>
          have hvsea₀ : (v.setPile a
              (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).pileOfTop z
                = none := by
            rw [← hag0]
            exact hsea₀
          have hstepv : State.step v (Move.tabToTab x (Sum.inr z)) =
              some ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z)) := by
            show (match v.pileHolding x with
              | none => none
              | some a₀ =>
                  if v.canPlace x (Sum.inr z) then
                    match fromCard x (v.piles a₀).faceUp with
                    | [] => none
                    | r =>
                        some ((v.setPile a₀
                          (Pile.afterRunRemoved (v.piles a₀) (below x (v.piles a₀).faceUp))).putRun
                          r (Sum.inr z))
                  else none) = _
            rw [hholdv, hvcp]
            show (match fromCard x (v.piles a).faceUp with
                  | [] => none
                  | r =>
                      some ((v.setPile a
                        (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                        r (Sum.inr z))) = _
            cases hfc : fromCard x (v.piles a).faceUp with
            | nil => exact absurd hfc hrnv
            | cons hdt rest =>
                rfl
          refine ⟨(v.setPile a
              (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
              (fromCard x (v.piles a).faceUp) (Sum.inr z), hstepv, ?_, step_wf hvwf hstepv⟩
          rw [hshape]
          rw [show (u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z)
              = (u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))) from by
              simp only [State.putRun, hsea₀]]
          rw [show (v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z)
              = (v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))) from by
              simp only [State.putRun, hvsea₀]]
          exact hsplmid
      | some q₀ =>
          have hvsea₀ : (v.setPile a
              (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).pileOfTop z
                = some q₀ := by
            rw [← hag0]
            exact hsea₀
          have hq₀k : q₀ ≠ k := by
            intro hkq
            have hs2 : (u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).pileOfTop z
                  = some k := by rw [hsea₀, hkq]
            have htopz : ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles k).top
                  = some z := g_pileOfTop_sound hs2
            have htopc : ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles k).top
                  = some c := by
              show (if k = a then
                  Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
                else (u.piles k : Pile)).top = some c
              rw [ite_eq_right (fun hcon => hak hcon.symm)]
              show lastOf (u.piles k).faceUp = some c
              rw [hfaceU]
              rfl
            exact hzc (Option.some.inj (htopz.symm.trans htopc))
          have hstepv : State.step v (Move.tabToTab x (Sum.inr z)) =
              some ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z)) := by
            show (match v.pileHolding x with
              | none => none
              | some a₀ =>
                  if v.canPlace x (Sum.inr z) then
                    match fromCard x (v.piles a₀).faceUp with
                    | [] => none
                    | r =>
                        some ((v.setPile a₀
                          (Pile.afterRunRemoved (v.piles a₀) (below x (v.piles a₀).faceUp))).putRun
                          r (Sum.inr z))
                  else none) = _
            rw [hholdv, hvcp]
            show (match fromCard x (v.piles a).faceUp with
                  | [] => none
                  | r =>
                      some ((v.setPile a
                        (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                        r (Sum.inr z))) = _
            cases hfc : fromCard x (v.piles a).faceUp with
            | nil => exact absurd hfc hrnv
            | cons hdt rest =>
                rfl
          refine ⟨(v.setPile a
              (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
              (fromCard x (v.piles a).faceUp) (Sum.inr z), hstepv, ?_, step_wf hvwf hstepv⟩
          rw [hshape]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · show ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z) : State).found c.suit
              = ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).found c.suit ++ [c]
            rw [g_putRun_found, g_putRun_found, setPile_found, setPile_found]
            exact hA
          · intro σ hσ
            show ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z) : State).found σ
              = ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).found σ
            rw [g_putRun_found, g_putRun_found, setPile_found, setPile_found]
            exact hB σ hσ
          · show ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).found c.suit
              = st.found c.suit
            rw [g_putRun_found, setPile_found]
            exact hC
          · show ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z) : State).stock
              = ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).stock
            rw [putRun_stock, putRun_stock, setPile_stock, setPile_stock]
            exact hD
          · show ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z) : State).waste
              = ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).waste
            rw [putRun_waste, putRun_waste, setPile_waste, setPile_waste]
            exact hE
          · show ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z) : State).drawStep
              = ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).drawStep
            rw [putRun_drawStep, putRun_drawStep, setPile_drawStep, setPile_drawStep]
            exact hF
          · intro a' ha'
            show ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z) : State).piles a'
              = ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).piles a'
            rw [putRun_piles_inr _ _ z q₀ hvsea₀, putRun_piles_inr _ _ z q₀ hsea₀]
            show (if a' = q₀ then
                  { (v.setPile a
                      (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles q₀ with
                    faceUp := ((v.setPile a
                      (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles q₀).faceUp
                      ++ fromCard x (v.piles a).faceUp }
                else
                  (if a' = a then
                    Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
                  else v.piles a'))
                = (if a' = q₀ then
                  { (u.setPile a
                      (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles q₀ with
                    faceUp := ((u.setPile a
                      (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles q₀).faceUp
                      ++ fromCard x (u.piles a).faceUp }
                else
                  (if a' = a then
                    Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
                  else u.piles a'))
            by_cases h2 : a' = q₀
            · rw [ite_eq_left h2, ite_eq_left h2, hGc q₀ hq₀k, hrun]
            · rw [ite_eq_right h2, ite_eq_right h2]
              by_cases h3 : a' = a
              · rw [ite_eq_left h3, ite_eq_left h3, hQ]
              · rw [ite_eq_right h3, ite_eq_right h3]
                exact hG a' ha'
          · show ((u.setPile a
                (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
                (fromCard x (u.piles a).faceUp) (Sum.inr z) : State).piles k = st.piles k
            rw [putRun_piles_inr _ _ z q₀ hsea₀]
            show (if k = q₀ then
                  { (u.setPile a
                      (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles q₀ with
                    faceUp := ((u.setPile a
                      (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles q₀).faceUp
                      ++ fromCard x (u.piles a).faceUp }
                else (u.setPile a
                      (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)) : State).piles k)
              = st.piles k
            rw [ite_eq_right (fun hcon => hq₀k hcon.symm)]
            show (if k = a then
                  Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp)
                else u.piles k) = st.piles k
            rw [ite_eq_right (fun hcon => hak hcon.symm)]
            exact hH
          · show ((v.setPile a
                (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp))).putRun
                (fromCard x (v.piles a).faceUp) (Sum.inr z) : State).piles k
              = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
            rw [putRun_piles_inr _ _ z q₀ hvsea₀]
            show (if k = q₀ then
                  { (v.setPile a
                      (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles q₀ with
                    faceUp := ((v.setPile a
                      (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles q₀).faceUp
                      ++ fromCard x (v.piles a).faceUp }
                else (v.setPile a
                      (Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)) : State).piles k)
              = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
            rw [ite_eq_right (fun hcon => hq₀k hcon.symm)]
            show (if k = a then
                  Pile.afterRunRemoved (v.piles a) (below x (v.piles a).faceUp)
                else v.piles k)
              = Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
            rw [ite_eq_right (fun hcon => hak hcon.symm)]
            exact hI

/-- The field survives every non-blocked move kind: the step replays
verbatim through the divergence, and the pair of successors still
sits in the field. -/
private theorem ground_split_step {st : State} {c : Card} {k : Anchor} {u v t : State}
    {m : Move}
    (huwf : u.WF) (hvwf : v.WF)
    (hnextst : st.nextUp c = true)
    (hface : (st.piles k).faceUp = [c])
    (hsplit : GroundSplit st c k u v)
    (hnb : m ≠ Move.tabToFound c) (hnblk : Move.groundBlocked c m = false)
    (hstep : State.step u m = some t) :
    ∃ v', State.step v m = some v' ∧ GroundSplit st c k t v' ∧ v'.WF := by
  cases m with
  | draw => exact ground_step_draw hvwf hsplit hstep
  | wasteToFound x => exact ground_step_wasteToFound huwf hvwf hnextst hface hsplit hstep
  | wasteToTab x b => exact ground_step_wasteToTab huwf hvwf hface hsplit hnblk hstep
  | tabToFound x =>
      by_cases hxc : x = c
      · exact absurd (by rw [hxc]) hnb
      · exact ground_step_tabToFound huwf hvwf hnextst hface hsplit hxc hstep
  | foundToTab x b => exact ground_step_foundToTab huwf hvwf hface hsplit hnblk hstep
  | tabToTab x b => exact ground_step_tabToTab huwf hvwf hface hsplit hnblk hstep

/-! ### The convergence at the rung and the replay -/

/-- At the rung pass, the source's own `tabToFound c` writes exactly
the field's ahead half: the raised successor and the replay
coincide, so the whole divergence collapses. -/
private theorem ground_converge {st : State} {c : Card} {k : Anchor} {u v t : State}
    (huwf : u.WF) (hnextst : st.nextUp c = true)
    (hface : (st.piles k).faceUp = [c])
    (hsplit : GroundSplit st c k u v)
    (hstep : State.step u (Move.tabToFound c) = some t) : t = v := by
  obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI⟩ := hsplit
  have hfaceU : (u.piles k).faceUp = [c] := by rw [hH]; exact hface
  have hnextU : u.nextUp c = true := by
    show decide (c.rank.toIdx = (u.found c.suit).length) = true
    rw [hC]
    exact decide_eq_true (of_decide_eq_true hnextst)
  have htopU : (u.piles k).top = some c := by
    show lastOf (u.piles k).faceUp = some c
    rw [hfaceU]
    rfl
  have hsearch : u.pileOfTop c = some k := (pileOfTop_eq_some_iff huwf).mpr htopU
  have hs := tabToFound_shape hstep hsearch
  rw [hs]
  refine State.ext (funext fun σ => ?_) (funext fun a' => ?_) ?_ ?_ ?_
  · show (if σ = c.suit then u.found c.suit ++ [c] else u.found σ) = v.found σ
    by_cases hσc : σ = c.suit
    · rw [ite_eq_left hσc, hσc]
      exact hA.symm
    · rw [ite_eq_right hσc]
      exact (hB σ hσc).symm
  · show (if a' = k then Pile.afterRunRemoved (u.piles k) (chop (u.piles k).faceUp)
        else u.piles a') = v.piles a'
    by_cases ha'k : a' = k
    · rw [ite_eq_left ha'k, ha'k, hH]
      exact hI.symm
    · rw [ite_eq_right ha'k]
      exact (hG a' ha'k).symm
  · show u.stock = v.stock
    exact hD.symm
  · show u.waste = v.waste
    exact hE.symm
  · show u.drawStep = v.drawStep
    exact hF.symm

/-- **The ground replay**: a compliant winning play `π₁ ++ tabToFound c
:: π₂` from an in-field source replays from the raised half as the
verbatim prefix and the verbatim tail — the raise is the front-loaded
one, both threads coincide from the rung pass on. -/
private theorem ground_replay_go {st : State} {c : Card} {k : Anchor}
    (hnextst : st.nextUp c = true)
    (hface : (st.piles k).faceUp = [c]) :
    ∀ π₁ u v, GroundSplit st c k u v → u.WF → v.WF →
      (∀ m ∈ π₁, m ≠ Move.tabToFound c ∧ Move.groundBlocked c m = false) →
      ∀ π₂ w, u.run (π₁ ++ Move.tabToFound c :: π₂) = some w →
        v.run (π₁ ++ π₂) = some w := by
  intro π₁ u v
  induction π₁ generalizing u v with
  | nil =>
      intro hsplit huwf hvwf _ π₂ w hrun
      rw [List.nil_append] at hrun
      obtain ⟨t, hstept, htrest⟩ := State.run_cons hrun
      have hconv : t = v := ground_converge huwf hnextst hface hsplit hstept
      rw [hconv] at htrest
      exact htrest
  | cons m π₁' ih =>
      intro hsplit huwf hvwf hclean π₂ w hrun
      rw [List.cons_append] at hrun
      obtain ⟨t, hstept, htrest⟩ := State.run_cons hrun
      obtain ⟨hnb, hnblk⟩ := hclean m (List.mem_cons_self)
      obtain ⟨v', hvstep, hvsplit, hvwf'⟩ :=
        ground_split_step huwf hvwf hnextst hface hsplit hnb hnblk hstept
      have hgo := ih t v' hvsplit (step_wf huwf hstept) hvwf'
        (fun m' hm' => hclean m' (List.mem_cons_of_mem _ hm')) π₂ w htrest
      show v.run ((m :: π₁') ++ π₂) = some w
      rw [List.cons_append]
      show (match State.step v m with
        | some s' => s'.run (π₁' ++ π₂)
        | none => none) = some w
      rw [hvstep]
      exact hgo


/-- **(N) The bare-floor residue** — §5.1's one open piece, the old
[GAP] channel-A/B reshape in physical dress: the raised card's
below-run is empty, and either the automatic reveal seated the
boundary card (the fresh top is not a fitting base for `c`) or the
card is no king (the emptied pile will not take it back).  The
classical remedy (B&G App. B.1, the safety instances): under
`safeToFound`, every card that could ever sit on `c` is a rank-`r−1`
opposite-colour live tenant with its own foundation already at its
index — the tenant subtree channels through the foundations (channel
A, depth at most two — the safety bounds descend exactly two ranks),
and the worry-backs of `c`'s suit-prefix in the source play are
skipped (channel B — same-colour conjunct).  The divergence is
one-two-step: parks onto `c`'s vacated seat re-home through
`tabToTab` runs; the shuffle-replay template is `RevEqW`
(`Orig/Combine`), the walk agreement `excursionSim`-shaped.
Refute-first target: a bare-floor state where compliancy fails —
every winning play parks onto `c`'s fresh seat before `c`'s suit
climbs past it.  See `tabToFound_groundNormalForm` for the named
residue this ride assumes.  STATUS (wave 24, farm-orig-dom-n-ground):
PROVEN as the assembly over that single named residue — the replay
mechanics (the `GroundSplit` divergence field carried through all six
move kinds, the rung convergence, and the verbatim replay induction)
are proven here; the remaining content is exactly the normal-form
half, with its own refute-first battery in
`witnesses/OrigGroundWitness.lean`. -/
theorem tabToFound_dominant_of_ground {st : State} {c : Card} {k : Anchor} {s₁ : State}
    (hwf : st.WF) (hsafe : safeToFound st c = true)
    (hk : st.pileOfTop c = some k)
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hbare : chop (st.piles k).faceUp = [])
    (hcorner : (st.piles k).hidden ≠ [] ∨ c.rank ≠ Rank.king)
    (hsolv : WinFrom st) : WinFrom s₁ := by
  obtain ⟨hnext, -, -⟩ := tabToFound_fires hstep
  obtain ⟨π₁, π₂, w, hrun, hwin, hclean⟩ :=
    tabToFound_groundNormalForm hwf hsafe hk hnext hbare hcorner hsolv
  obtain ⟨-, hlastc⟩ := pileOfTop_top hk
  have hfull : (st.piles k).faceUp = chop (st.piles k).faceUp ++ [c] :=
    lastOf_chop hlastc
  have hface : (st.piles k).faceUp = [c] := by
    rw [hfull, hbare, List.nil_append]
  refine ⟨π₁ ++ π₂, w, ?_, hwin⟩
  exact ground_replay_go hnext hface π₁ st s₁ (ground_split_init hk hstep)
    hwf (step_wf hwf hstep) hclean π₂ w hrun

/-- **§5.1, physical form**: a legal `tabToFound` of a safe card is
dominant — the win survives the raise.  PROVEN here modulo the single
named residue above: the under-seat case rides the LANDED
`tabToFound_undo_under` (the below-run's last card fits — `runOK`
descent — and tops its pile — the search is unique at `WF`), the
bare-king case rides the LANDED `tabToFound_undo_bare`; both fall to
`WinFrom_of_undo`. -/
theorem tabToFound_safe_dominant {st : State} {c : Card} {s₁ : State}
    (hwf : st.WF) (hsafe : safeToFound st c = true)
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hsolv : WinFrom st) : WinFrom s₁ := by
  obtain ⟨hnext, k, hk⟩ := tabToFound_fires hstep
  cases hchop : chop (st.piles k).faceUp with
  | nil =>
      by_cases hking : c.rank = Rank.king
      · by_cases hhidden : (st.piles k).hidden = []
        · exact WinFrom_of_undo hstep
            (tabToFound_undo_bare hstep hk hchop hhidden hking) hsolv
        · exact tabToFound_dominant_of_ground hwf hsafe hk hstep hchop
            (Or.inl hhidden) hsolv
      · exact tabToFound_dominant_of_ground hwf hsafe hk hstep hchop
          (Or.inr hking) hsolv
  | cons x t =>
      have hchne : chop (st.piles k).faceUp ≠ [] := by
        rw [hchop]
        intro h
        exact absurd h (by simp)
      obtain ⟨-, hlastc⟩ := pileOfTop_top hk
      have hfull : (st.piles k).faceUp = chop (st.piles k).faceUp ++ [c] :=
        lastOf_chop hlastc
      have hrok : runOK (chop (st.piles k).faceUp ++ [c]) = true := by
        rw [← hfull]
        exact hwf.runOK_of k
      obtain ⟨z, hz, hsit⟩ := runOK_snoc_sit hchne hrok
      have hs := tabToFound_shape hstep hk
      have hsearch := pileOfTop_after_tabToFound hwf hz hs
      exact WinFrom_of_undo hstep
        (tabToFound_undo_under hstep hk hz hsit hsearch) hsolv

/-! ## §5.3 — the draw-1 deck dominance -/

/-- The draw cycle's content: the stock in draw order, then the waste
read back to front — invariant under dealing and recycling. -/
def cycleOf (st : State) : List Card := st.stock ++ st.waste.reverse

/-- Two states whose piles, foundations, draw step and cycle content
agree — differing at most in how far the cycle has been dealt. -/
def sameCycle (st st' : State) : Prop :=
  st.found = st'.found ∧ st.piles = st'.piles ∧ st.drawStep = st'.drawStep ∧
    cycleOf st = cycleOf st'

/-- c's **exit**: the waste-spending move that takes `c` out of the
cycle for good — the stack arm or the park arm. -/
def Move.leavesWaste (c : Card) : Move → Bool
  | .wasteToFound c' => decide (c' = c)
  | .wasteToTab c' _ => decide (c' = c)
  | _ => false

/-- The only move shape that reads (and drops) `c`'s foundation slot:
a worry-back of `c`'s suit.  (The rung vocabulary is the route map's
own, FUTURES-ORIG §1.) -/
def Move.lowersRung (c : Card) : Move → Bool
  | .foundToTab x _ => decide (x.suit = c.suit)
  | _ => false

/-- The §5.3 compliance (rung discipline): until `c` leaves the
waste, no worry-back of `c`'s suit.  Pre-exit, `c`'s suit cannot
stack (`c` is in the cycle, `WF` uniqueness; its frontier card is
`c` itself), so `foundToTab` of the suit is the only slot-dropper,
and the fronting play stays legal exactly while it is banned. -/
def rungHeldUntilExit (c : Card) : List Move → Prop
  | [] => True
  | m :: π' => (m.leavesWaste c = true) ∨
      ((m.lowersRung c = false) ∧ rungHeldUntilExit c π')

/-! ## (B)'s private development — the nine-case replay engine

The kit below serves `draw1_compliant_replay` only.  The list
surgery and the two deal composites are dedup-marked ports of
`Orig/Phase.lean`'s private orbit strip (`plain_draw_shape`,
`base_draw_shape`, `run_draw_cons`, `run_replicate_append`,
`drain_positions_one`, `base_positions_one`); the spend/board step
inversions are dedup-marked ports of the private copies in
`Orig/Shuttle.lean` and `Orig/Irreversible.lean` (same shapes, same
proof scripts, per the farm's private-isolation convention; they
dedup at merge). -/

/-! ### List surgery -/

/-- Membership as an infix split (the witness shape a stocked or
wasted `c` carries through the induction). -/
private theorem mem_infix_split {α : Type} : ∀ (l : List α) (x : α),
    x ∈ l → ∃ pre post, l = pre ++ x :: post := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rcases List.mem_cons.1 h with rfl | hm
      · exact ⟨[], t, rfl⟩
      · obtain ⟨pre, post, heq⟩ := ih x hm
        exact ⟨y :: pre, post, by rw [heq, List.cons_append]⟩

/-- The additive take split (dedup-marked port of `Phase`'s private
`take_drop_add`). -/
private theorem table_take_add {α : Type} :
    ∀ (i j : Nat) (l : List α),
    l.take (i + j) = l.take i ++ (l.drop i).take j := by
  intro i
  induction i with
  | zero => intro j l; simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.take_nil, List.drop_nil, List.nil_append]
      | cons a t =>
          show a :: t.take (i + j) = a :: (t.take i ++ (t.drop i).take j)
          exact congrArg (a :: ·) (ih j t)

/-- The additive drop split (dedup-marked port of `Phase`'s private
`drop_drop_add`). -/
private theorem table_drop_add {α : Type} :
    ∀ (i j : Nat) (l : List α),
    (l.drop i).drop j = l.drop (i + j) := by
  intro i
  induction i with
  | zero => intro j l; simp
  | succ i ih =>
      intro j l
      have hidx : i + 1 + j = i + j + 1 := by omega
      rw [hidx]
      cases l with
      | nil => simp only [List.drop_nil]
      | cons a t => exact ih j t

/-- Taking past (or exactly to) the end takes the whole list
(dedup-marked port of `Phase`'s private `take_ge_length`). -/
private theorem table_take_ge {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil => intro n _; exact List.take_nil
  | cons a t ih =>
      intro n h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hm : t.length ≤ m := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          show a :: t.take m = a :: t
          exact congrArg (a :: ·) (ih m hm)

/-- Dropping past (or exactly to) the end drops to nothing
(dedup-marked port of `Phase`'s private `drop_ge_length`). -/
private theorem table_drop_ge {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.drop n = [] := by
  intro l
  induction l with
  | nil => intro n _; exact List.drop_nil
  | cons a t ih =>
      intro n h
      match n with
      | 0 =>
          exact absurd h (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          exact ih m (by have hx : (a :: t).length = t.length + 1 := rfl; omega)

/-- Taking through a known prefix returns the prefix. -/
private theorem table_take_pre {α : Type} : ∀ (A B : List α),
    (A ++ B).take A.length = A := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih => intro B; exact congrArg (a :: ·) (ih B)

/-- Dropping past a known prefix returns the tail (dedup-marked port
of `Phase`'s private `drop_append_prefix`). -/
private theorem table_drop_pre {α : Type} : ∀ (A B : List α),
    (A ++ B).drop A.length = B := by
  intro A
  induction A with
  | nil => intro B; rfl
  | cons a t ih => intro B; exact ih B

/-- The take-side append split below the prefix. -/
private theorem table_take_app_le {α : Type} :
    ∀ (A B : List α) (n : Nat), n ≤ A.length →
    (A ++ B).take n = A.take n := by
  intro A
  induction A with
  | nil =>
      intro B n hn
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      rfl
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 => rfl
      | m + 1 =>
          show a :: (t ++ B).take m = a :: t.take m
          exact congrArg (a :: ·) (ih B m (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega))

/-- The drop-side append split below the prefix. -/
private theorem table_drop_app_le {α : Type} :
    ∀ (A B : List α) (n : Nat), n ≤ A.length →
    (A ++ B).drop n = A.drop n ++ B := by
  intro A
  induction A with
  | nil =>
      intro B n hn
      have hn0 : n = 0 := by simpa using hn
      subst hn0
      rfl
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 => rfl
      | m + 1 =>
          show (t ++ B).drop m = t.drop m ++ B
          exact ih B m (by have hx : (a :: t).length = t.length + 1 := rfl; omega)

/-- The take-side append split past the prefix. -/
private theorem table_take_app_ge {α : Type} :
    ∀ (A B : List α) (n : Nat), A.length ≤ n →
    (A ++ B).take n = A ++ B.take (n - A.length) := by
  intro A
  induction A with
  | nil =>
      intro B n _
      simp [Nat.sub_zero]
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 =>
          exact absurd hn (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          have hsub : m + 1 - (a :: t).length = m - t.length := by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega
          rw [hsub]
          show a :: (t ++ B).take m = a :: (t ++ B.take (m - t.length))
          exact congrArg (a :: ·) (ih B m (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega))

/-- The drop-side append split past the prefix. -/
private theorem table_drop_app_ge {α : Type} :
    ∀ (A B : List α) (n : Nat), A.length ≤ n →
    (A ++ B).drop n = B.drop (n - A.length) := by
  intro A
  induction A with
  | nil =>
      intro B n _
      simp [Nat.sub_zero]
  | cons a t ih =>
      intro B n hn
      match n with
      | 0 =>
          exact absurd hn (by
            have hx : (a :: t).length = t.length + 1 := rfl
            omega)
      | m + 1 =>
          show (t ++ B).drop m = B.drop ((m + 1) - (t.length + 1))
          have hx : (m + 1) - (t.length + 1) = m - t.length := by omega
          rw [hx]
          exact ih B m (by have h1 : (a :: t).length = t.length + 1 := rfl; omega)

/-! ### The draw composites

Dedup-marked ports of `Orig/Phase.lean`'s private orbit strip
(`plain_draw_shape`, `base_draw_shape`, `run_draw_cons`,
`run_replicate_append`, `drain_positions_one`, `base_positions_one`),
plus the `drawStep = 1` specializations the fronting engine reads. -/

/-- One plain draw (the stock is nonempty, so no recycle fires): the
head card moves stock-to-waste, list-exact. -/
private theorem plain_draw_shape1 {x : State} (hne : x.stock ≠ []) :
    State.step x Move.draw = some
      { x with stock := x.stock.drop x.drawStep,
               waste := (x.stock.take x.drawStep).reverse ++ x.waste } := by
  rw [show State.step x Move.draw = x.stepDraw from rfl, State.stepDraw,
    show State.recycle x = x from recycle_keep x hne,
    dealStock_eq_of_ne_nil x hne, dealUpTo_eq_take_drop]

/-- One pass-end draw (the stock is empty and the waste nonempty, so
the recycle fires): the waste becomes the stock reversed, and one
clipped deal moves back onto the waste. -/
private theorem base_draw_shape1 {x : State} (hstock : x.stock = ([] : List Card))
    (hw : x.waste ≠ []) :
    State.step x Move.draw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse ++ ([] : List Card) } := by
  have hrne : x.waste.reverse ≠ [] := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_reverse, List.length_nil] at hlen
    obtain ⟨c0, t0, hwcon0⟩ := list_cons_of_ne_nil hw
    have h1 : 1 ≤ x.waste.length := by
      rw [hwcon0, List.length_cons]; omega
    omega
  rw [show State.step x Move.draw = x.stepDraw from rfl, State.stepDraw,
    recycle_nil x hstock hw,
    dealStock_eq_of_ne_nil _ hrne, dealUpTo_eq_take_drop]

/-- One draw followed by the rest of the play (dedup-marked port of
`Phase`'s private `run_draw_cons`). -/
private theorem run_draw_cons1 {x y : State} {rest : List Move}
    (hstep : State.step x Move.draw = some y) :
    x.run (Move.draw :: rest) = y.run rest := by
  show (match State.step x Move.draw with
      | some st' => State.run st' rest
      | none => none) = State.run y rest
  rw [hstep]

/-- Append-glue for pure-draw plays (dedup-marked port of `Phase`'s
private `run_replicate_append`). -/
private theorem run_rep_append1 :
    ∀ (q : Nat) (x z : State) (rest : List Move),
    x.run (List.replicate q Move.draw) = some z →
    x.run (List.replicate q Move.draw ++ rest) = z.run rest := by
  intro q
  induction q with
  | zero =>
      intro x z rest h
      have hx : (some x : Option State) = some z := h
      injection hx with hx2
      rw [← hx2]
      rfl
  | succ q ih =>
      intro x z rest h
      obtain ⟨y, hstep, hrest⟩ := State.run_cons h
      show x.run (Move.draw :: (List.replicate q Move.draw ++ rest)) = z.run rest
      rw [run_draw_cons1 hstep]
      exact ih y z rest hrest

/-- Splitting a successful run at a play split. -/
private theorem run_append_split1 : ∀ (x : State) (A B : List Move) (w : State),
    x.run (A ++ B) = some w → ∃ z, x.run A = some z ∧ z.run B = some w := by
  intro x A
  induction A generalizing x with
  | nil =>
      intro B w h
      exact ⟨x, rfl, h⟩
  | cons m rest ih =>
      intro B w h
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      obtain ⟨z, hA, hB⟩ := ih s₁ B w hrest
      refine ⟨z, ?_, hB⟩
      show (match State.step x m with
        | some st' => State.run st' rest
        | none => none) = some z
      rw [hstep]
      exact hA

/-- One move runs by stepping it (dedup-marked port of `Shuttle`'s
private `run_one`). -/
private theorem run_one1 {st : State} {m : Move} {s : State}
    (h : State.step st m = some s) :
    st.run [m] = some s := by
  show (match State.step st m with
    | some st' => State.run st' []
    | none => none) = some s
  rw [h]
  rfl

/-- **The drain positions** (dedup-marked port of `Phase`'s private
`drain_positions_one`): from a state whose stock is `l`, `q` draws
— each a full deal of `x.drawStep`, the running offset `n = q *
drawStep` staying within the stock — move exactly those `n` cards
from the stock's front onto the waste's front, list-exact. -/
private theorem drain_positions1 :
    ∀ (q : Nat) (x : State) (n : Nat) (l : List Card),
    0 < x.drawStep → n = q * x.drawStep → n ≤ l.length → x.stock = l →
    x.run (List.replicate q Move.draw) = some
      { x with stock := l.drop n, waste := (l.take n).reverse ++ x.waste } := by
  intro q
  induction q with
  | zero =>
      intro x n l _hd hn _hle hstock
      have hn0 : n = 0 := by
        rw [Nat.zero_mul] at hn
        exact hn
      subst hn0
      show (some x : Option State) = some
        { x with stock := l.drop 0, waste := (l.take 0).reverse ++ x.waste }
      rw [List.drop_zero, List.take_zero, List.reverse_nil, List.nil_append,
        ← hstock]
  | succ q ih =>
      intro x n l hd hn hle hstock
      have hnsm : n = q * x.drawStep + x.drawStep := by
        rw [Nat.succ_mul] at hn
        exact hn
      have hlne : l ≠ [] := by
        intro hc
        have hlen : l.length = 0 := by rw [hc]; simp
        omega
      have hsne : x.stock ≠ [] := by
        intro hc
        apply hlne
        rw [← hstock]
        exact hc
      have hstep : State.step x Move.draw = some
        { x with stock := x.stock.drop x.drawStep,
                 waste := (x.stock.take x.drawStep).reverse ++ x.waste } :=
        plain_draw_shape1 hsne
      have hrep : List.replicate (q + 1) Move.draw
          = Move.draw :: List.replicate q Move.draw := rfl
      rw [hrep, run_draw_cons1 hstep, hstock]
      have hle' : q * x.drawStep ≤ (l.drop x.drawStep).length := by
        have h1 := List.length_drop (i := x.drawStep) (l := l)
        omega
      have hres := ih
        { x with stock := l.drop x.drawStep,
                 waste := (l.take x.drawStep).reverse ++ x.waste }
        (q * x.drawStep) (l.drop x.drawStep) hd rfl hle' rfl
      rw [hres]
      have hSw : (show State from
          { x with stock := l.drop x.drawStep,
                   waste := (l.take x.drawStep).reverse ++ x.waste }).waste
          = (l.take x.drawStep).reverse ++ x.waste := rfl
      rw [hSw]
      have hidx : x.drawStep + q * x.drawStep = n := by omega
      rw [table_drop_add x.drawStep (q * x.drawStep) l, hidx]
      have hmerge : (List.take (q * x.drawStep) (List.drop x.drawStep l)).reverse
            ++ ((List.take x.drawStep l).reverse ++ x.waste)
          = (l.take (x.drawStep + q * x.drawStep)).reverse ++ x.waste := by
        rw [table_take_add, List.reverse_append, List.append_assoc]
      rw [hmerge, hidx]

/-- **The redeal positions** (dedup-marked port of `Phase`'s private
`base_positions_one`): from a pass base (empty stock, nonempty
waste), `k + 1` consecutive draws move exactly that many cards back
onto the waste, list-exact. -/
private theorem base_positions1 :
    ∀ (k : Nat) (x : State),
    x.stock = ([] : List Card) → x.waste ≠ [] → 0 < x.drawStep →
    (k + 1) * x.drawStep ≤ x.waste.length →
    x.run (List.replicate (k + 1) Move.draw) = some
      { x with stock := x.waste.reverse.drop ((k + 1) * x.drawStep),
               waste := (x.waste.reverse.take ((k + 1) * x.drawStep)).reverse
                 ++ ([] : List Card) } := by
  intro k x hstock hw hd hsize
  rw [Nat.succ_mul] at hsize
  have hstep : State.step x Move.draw = some
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse
                 ++ ([] : List Card) } :=
    base_draw_shape1 hstock hw
  rw [show List.replicate (k + 1) Move.draw
        = Move.draw :: List.replicate k Move.draw from rfl,
    run_draw_cons1 hstep]
  have hle' : k * x.drawStep ≤ (x.waste.reverse.drop x.drawStep).length := by
    have h1 := List.length_drop (i := x.drawStep) (l := x.waste.reverse)
    have h2 : x.waste.reverse.length = x.waste.length := List.length_reverse
    omega
  have hres := drain_positions1 k
    { x with stock := x.waste.reverse.drop x.drawStep,
             waste := (x.waste.reverse.take x.drawStep).reverse
               ++ ([] : List Card) }
    (k * x.drawStep) (x.waste.reverse.drop x.drawStep) hd rfl hle' rfl
  rw [hres]
  have hSw : (show State from
      { x with stock := x.waste.reverse.drop x.drawStep,
               waste := (x.waste.reverse.take x.drawStep).reverse
                 ++ ([] : List Card) }).waste
      = (x.waste.reverse.take x.drawStep).reverse
          ++ ([] : List Card) := rfl
  rw [hSw]
  have hidx : x.drawStep + k * x.drawStep = (k + 1) * x.drawStep := by
    rw [Nat.succ_mul]; omega
  rw [table_drop_add x.drawStep (k * x.drawStep) x.waste.reverse, hidx]
  have hmerge : (List.take (k * x.drawStep)
          (List.drop x.drawStep x.waste.reverse)).reverse
        ++ ((List.take x.drawStep x.waste.reverse).reverse ++ ([] : List Card))
      = ((List.take (x.drawStep + k * x.drawStep) x.waste.reverse).reverse
          ++ ([] : List Card)) := by
    rw [table_take_add, List.reverse_append, List.append_assoc]
  rw [hmerge, hidx]

/-- Replicate's snoc form. -/
private theorem rep_snoc (n : Nat) (m : Move) :
    List.replicate n m ++ [m] = List.replicate (n + 1) m := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have e1 : List.replicate (n + 1) m = m :: List.replicate n m := List.replicate_succ
      have e2 : List.replicate (n + 1 + 1) m = m :: List.replicate (n + 1) m :=
        List.replicate_succ
      rw [e1, List.cons_append, ih, e2]

/-- Replicate addition (the pure-draw plays' split). -/
private theorem rep_add (a : Nat) : ∀ (b : Nat) (m : Move),
    List.replicate (a + b) m = List.replicate a m ++ List.replicate b m := by
  intro b
  induction b with
  | zero =>
      intro m
      have ha : a + 0 = a := Nat.add_zero a
      rw [ha]
      simp
  | succ b ih =>
      intro m
      have hab : a + (b + 1) = (a + b) + 1 := by omega
      have e1 : List.replicate ((a + b) + 1) m
          = List.replicate (a + b) m ++ [m] := (rep_snoc (a + b) m).symm
      have e2 : List.replicate (b + 1) m = List.replicate b m ++ [m] :=
        (rep_snoc b m).symm
      rw [hab, e1, e2, ih, List.append_assoc]

/-- The draw-1 drain: `r` draws from a state whose stock holds at
least `r` cards move exactly `r` stock cards onto the waste's front. -/
private theorem drain_run1 {x : State} (r : Nat) (hds : x.drawStep = 1)
    (hle : r ≤ x.stock.length) :
    x.run (List.replicate r Move.draw) = some
      { x with stock := x.stock.drop r, waste := (x.stock.take r).reverse ++ x.waste } := by
  have hpos : 0 < x.drawStep := by rw [hds]; omega
  have hm : r = r * x.drawStep := by rw [hds, Nat.mul_one]
  exact drain_positions1 r x r x.stock hpos hm hle rfl

/-- The draw-1 pass-base redeal: from an exhausted stock, `1 + m`
draws deal the first `1 + m` recycled cards back onto the waste. -/
private theorem redeal_run1 {x : State} (m : Nat) (hds : x.drawStep = 1)
    (hst : x.stock = ([] : List Card)) (hw : x.waste = [] → False)
    (hle : m + 1 ≤ x.waste.length) :
    x.run (List.replicate (m + 1) Move.draw) = some
      { x with stock := x.waste.reverse.drop (m + 1),
               waste := (x.waste.reverse.take (m + 1)).reverse ++ ([] : List Card) } := by
  have hwne : x.waste ≠ [] := by
    intro hc
    exact hw hc
  have hpos : 0 < x.drawStep := by rw [hds]; omega
  have hcnt : (m + 1) * x.drawStep = m + 1 := by rw [hds, Nat.mul_one]
  have hp := base_positions1 m x hst hwne hpos (by rw [hcnt]; exact hle)
  rw [hcnt] at hp
  exact hp

/-! ### The spend step, in raised form

The `wasteToFound` spend lands on `Shuttle`'s public `raisedMid`
literal — the same shape the worry-back identity's legs use. -/

/-- The waste-top stack, computed: given the waste head and the rung,
the step is the raise. -/
private theorem wtf_step_raised {s : State} {c : Card} {ws : List Card}
    (hw : s.waste = c :: ws) (hng : s.nextUp c = true) :
    State.step s (Move.wasteToFound c) = some (raisedMid s ws c) := by
  have hgt : (s.wasteIs c && s.nextUp c) = true := by
    rw [State.wasteIs_cons hw c, hng]
    simp
  show (if s.wasteIs c && s.nextUp c then
      match s.waste with
      | _ :: ws' => some { s.setFound c.suit (s.found c.suit ++ [c]) with waste := ws' }
      | [] => none
    else none) = some (raisedMid s ws c)
  rw [ite_eq_left hgt, hw]
  rfl

/-! ### Step inversions (dedup-marked ports) -/

/-- A successful `.wasteToFound`: the guard's two halves, and the
splice `s' = raisedMid st ws c`. -/
private theorem step_wtf_inv1 {st : State} {c : Card} {s' : State}
    (h : State.step st (Move.wasteToFound c) = some s') :
    st.wasteIs c = true ∧ st.nextUp c = true ∧
      ∃ ws, st.waste = c :: ws ∧ s' = raisedMid st ws c := by
  simp only [State.step] at h
  split at h
  · rename_i hcond
    rw [Bool.and_eq_true_iff] at hcond
    obtain ⟨hw, hng⟩ := hcond
    refine ⟨hw, hng, ?_⟩
    by_cases hwst : st.waste = []
    · rw [hwst] at h
      simp at h
    · obtain ⟨w', wsl, hcon⟩ := list_cons_of_ne_nil hwst
      have hw'c : w' = c := by
        rw [State.wasteIs_cons hcon c] at hw
        exact of_decide_eq_true hw
      rw [hw'c] at hcon
      simp only [hcon, Option.some.injEq] at h
      exact ⟨wsl, hcon, by rw [h.symm]; rfl⟩
  · simp at h

/-- A successful `.wasteToTab`: guard, nonempty waste, and the
placement with the waste popped (dedup-marked port of `Shuttle`'s
private `step_wasteToTab_inv`). -/
private theorem step_wtt_inv1 {u : State} {c : Card} {b : Base} {s' : State}
    (h : State.step u (Move.wasteToTab c b) = some s') :
    u.wasteIs c = true ∧ u.canPlace c b = true ∧
      ∃ wsl, u.waste = c :: wsl ∧ s' = { u.putCard c b with waste := wsl } := by
  simp only [State.step] at h
  split at h
  · rename_i hcond
    rw [Bool.and_eq_true_iff] at hcond
    obtain ⟨hw, hcp⟩ := hcond
    refine ⟨hw, hcp, ?_⟩
    by_cases hwst : u.waste = []
    · rw [hwst] at h
      simp at h
    · obtain ⟨w', wsl, hcon⟩ := list_cons_of_ne_nil hwst
      have hw'c : w' = c := by
        rw [State.wasteIs_cons hcon c] at hw
        exact of_decide_eq_true hw
      rw [hw'c] at hcon
      simp only [hcon, Option.some.injEq] at h
      exact ⟨wsl, hcon, h.symm⟩
  · simp at h

/-- A successful `.foundToTab` (dedup-marked port of `Irreversible`'s
private `step_foundToTab_inv`). -/
private theorem step_ftt_inv1 {st : State} {c : Card} {b : Base} {s' : State}
    (h : State.step st (Move.foundToTab c b) = some s') :
    st.canPlace c b = true ∧
      s' = (st.setFound c.suit (chop (st.found c.suit))).putCard c b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i c' ht hcond
      rw [Bool.and_eq_true_iff] at hcond
      obtain ⟨hdec, hcp⟩ := hcond
      injection h with hEq
      have hc'c : c' = c := of_decide_eq_true hdec
      refine ⟨hcp, ?_⟩
      rw [← hEq]
    · simp at h
  · simp at h

/-- The lower leg (dedup-marked port of `Shuttle`'s private
`lower_foundToTab`): from the mid state, `foundToTab c b` fires and
lands exactly on the `wasteToTab c b` successor — the worry-back
identity's second half. -/
private theorem lower_foundToTab1 {u : State} {c : Card} {ws : List Card}
    (hwastee : u.waste = c :: ws)
    {b : Base} {s : State}
    (h : State.step u (Move.wasteToTab c b) = some s) :
    State.step (raisedMid u ws c) (Move.foundToTab c b) = some s := by
  obtain ⟨-, hcp, ws1, hw', hs'⟩ := step_wtt_inv1 h
  rw [hw'] at hwastee
  injection hwastee with _ hws
  cases hws
  subst hs'
  -- the mid state's foundation top is exactly `c`, and its target
  -- guard is read against `u`'s verbatim piles
  have hMfc : (raisedMid u ws c).found c.suit = u.found c.suit ++ [c] := by
    show (if c.suit = c.suit then u.found c.suit ++ [c] else u.found c.suit) = _
    rw [ite_eq_left rfl]
  have hMtop : (raisedMid u ws c).foundTop c.suit = some c := by
    show lastOf ((raisedMid u ws c).found c.suit) = some c
    rw [hMfc]
    exact lastOf_snoc
  have hMcp : (raisedMid u ws c).canPlace c b = true := hcp
  rw [step_foundToTab_splice hMtop hMcp]
  -- restore the foundation, then place
  have hchop : chop ((raisedMid u ws c).found c.suit) = u.found c.suit := by
    rw [hMfc, chop_snoc]
  rw [hchop, Option.some.injEq]
  -- the lowered source's found-function and piles are exactly `u`'s
  have hMf : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).found
      = u.found := by
    funext s1'
    show ((raisedMid u ws c).setFound c.suit (u.found c.suit)).found s1'
      = u.found s1'
    by_cases hs1 : s1' = c.suit
    · show (if s1' = c.suit then u.found c.suit
           else (raisedMid u ws c).found s1') = u.found s1'
      rw [ite_eq_left hs1, hs1]
    · show (if s1' = c.suit then u.found c.suit
           else (raisedMid u ws c).found s1') = u.found s1'
      rw [ite_eq_right hs1]
      show (if s1' = c.suit then u.found c.suit ++ [c] else u.found s1') = _
      rw [ite_eq_right hs1]
  have hMsp : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles
      = u.piles := rfl
  cases b with
  | inl a2 =>
      apply State.ext
      · exact hMf
      · show (fun a' : Anchor =>
            if a' = a2 then ⟨[], [c]⟩ else
            ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles a') =
          (fun a' : Anchor => if a' = a2 then ⟨[], [c]⟩ else u.piles a')
        rw [hMsp]
      · rfl
      · rfl
      · rfl
  | inr z2 =>
      simp only [State.canPlace] at hcp
      cases hpo : u.pileOfTop z2 with
      | none =>
          simp only [hpo] at hcp
          exact Bool.noConfusion hcp
      | some k =>
          have hMpo : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).pileOfTop z2
              = some k := by
            show (u.pileOfTop z2 : Option Anchor) = some k
            exact hpo
          rw [putCard_inr_eq hMpo,
            show u.putCard c (.inr z2) =
              u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ [c] } from
              putCard_inr_eq hpo]
          apply State.ext
          · exact hMf
          · show (fun a' : Anchor =>
                if a' = k then
                  { ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles k with
                    faceUp :=
                    (((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles k).faceUp ++ [c] }
                else ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles a') =
              (fun a' : Anchor =>
                if a' = k then { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
                else u.piles a')
            rw [hMsp]
          · rfl
          · rfl
          · rfl

/-! ### The two fronting engines -/

/-- The two bump orders agree at distinct suits — the found half of
every exchange square at `x` and `c`. -/
private theorem bump2_comm {f : Suit → List Card} {x c : Card}
    (hne : x.suit ≠ c.suit) :
    (fun s' => if s' = c.suit then f c.suit ++ [c] else
        (if s' = x.suit then f x.suit ++ [x] else f s'))
    = (fun s' => if s' = x.suit then f x.suit ++ [x] else
        (if s' = c.suit then f c.suit ++ [c] else f s')) := by
  funext s'
  by_cases h1 : s' = c.suit
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (Ne.symm hne), ite_eq_left rfl]
  · by_cases h2 : s' = x.suit
    · subst h2
      rw [ite_eq_right hne, ite_eq_left rfl, ite_eq_left rfl]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]

/-- **The stock fronting engine**: with `c` stocked at depth
`|pre|` in the deal order, `|pre| + 1` draws bring it to hand and
the stack lands on the record state — `c`'s foundation bumped, the
suffix past `c` the new stock, `pre` reversed onto the waste. -/
private theorem front_stock {s : State} {c : Card} {pre post : List Card}
    (hd : s.drawStep = 1) (hng : s.nextUp c = true)
    (hs : s.stock = pre ++ c :: post) :
    s.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) =
      some (State.mk (fun s' => if s' = c.suit then s.found c.suit ++ [c] else s.found s')
        s.piles post (pre.reverse ++ s.waste) s.drawStep) := by
  have hls : s.stock.length = pre.length + post.length + 1 := by
    rw [hs, List.length_append, List.length_cons]; omega
  have hle : pre.length + 1 ≤ s.stock.length := by omega
  have hap : s.stock = pre ++ [c] ++ post := by
    rw [hs]
    exact (List.append_assoc pre [c] post).symm
  have hlenA : (pre ++ [c]).length = pre.length + 1 := by
    simp [List.length_append]
  have htake : s.stock.take (pre.length + 1) = pre ++ [c] := by
    rw [hap, ← hlenA]
    exact table_take_pre (pre ++ [c]) post
  have hdrop : s.stock.drop (pre.length + 1) = post := by
    rw [hap, ← hlenA]
    exact table_drop_pre (pre ++ [c]) post
  have hdr : s.run (List.replicate (pre.length + 1) Move.draw) = some
      (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep) := by
    have hd0 := drain_run1 (pre.length + 1) hd hle
    rw [hd0]
    refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
    · rw [hdrop]
    · rw [htake]
  have hw : (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep).waste
      = c :: (pre.reverse ++ s.waste) := by
    show ((pre ++ [c]).reverse ++ s.waste) = _
    rw [List.reverse_append]
    simp
  have hstep : State.step
      (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep)
      (Move.wasteToFound c) = some
      (raisedMid (State.mk s.found s.piles post ((pre ++ [c]).reverse ++ s.waste) s.drawStep)
        (pre.reverse ++ s.waste) c) :=
    wtf_step_raised hw hng
  rw [run_rep_append1 (pre.length + 1) s _
      [Move.wasteToFound c] hdr, run_one1 hstep]
  rfl

/-- **The waste fronting engine**: with `c` in the waste, `preW`
above it and `postW` below, the fronting is the drain to the pass
base, the recycle-deal, and `|postW|` more deals — landing on the
record state — `c`'s foundation bumped, the cards that were above
`c` back in the stock reversed ahead of it, `postW` the new waste. -/
private theorem front_waste {s : State} {c : Card} {preW postW : List Card}
    (hd : s.drawStep = 1) (hng : s.nextUp c = true)
    (hw : s.waste = preW ++ c :: postW) :
    s.run (List.replicate (s.stock.length + postW.length + 1) Move.draw ++
      [Move.wasteToFound c]) =
      some (State.mk (fun s' => if s' = c.suit then s.found c.suit ++ [c] else s.found s')
        s.piles (preW.reverse ++ s.stock) postW s.drawStep) := by
  have hlw : s.waste.length = preW.length + 1 + postW.length := by
    rw [hw, List.length_append, List.length_cons]; omega
  -- leg one: the drain to the pass base
  have hdr1 : s.run (List.replicate s.stock.length Move.draw) = some
      (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep) := by
    have hd0 := drain_run1 s.stock.length hd (Nat.le_refl _)
    rw [hd0]
    refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
    · rw [table_drop_ge _ _ (Nat.le_refl _)]
    · rw [table_take_ge _ _ (Nat.le_refl _)]
  have hst : (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep).stock
      = ([] : List Card) := rfl
  have hwne : (s.stock.reverse ++ s.waste) = [] → False := by
    intro hc
    have hcm : c ∈ s.waste := by
      rw [hw]; exact List.mem_append.2 (Or.inr List.mem_cons_self)
    have hm : c ∈ (s.stock.reverse ++ s.waste) :=
      List.mem_append.2 (Or.inr hcm)
    rw [hc] at hm
    exact absurd hm (by simp)
  -- the recycled order, left-deep
  have hrev : (s.stock.reverse ++ s.waste).reverse
      = (postW.reverse ++ [c] ++ preW.reverse) ++ s.stock := by
    rw [List.reverse_append, List.reverse_reverse, hw, List.reverse_append,
      List.reverse_cons]
  have hlen : postW.reverse.length = postW.length := by
    simp [List.length_reverse]
  have hlA : postW.length + 1 ≤ (postW.reverse ++ [c]).length := by
    rw [← hlen, List.length_append]; simp
  have hlX : postW.length + 1
      ≤ (postW.reverse ++ [c] ++ preW.reverse).length := by
    rw [← hlen, List.length_append, List.length_append]; simp
  have htak : (s.stock.reverse ++ s.waste).reverse.take (postW.length + 1)
      = postW.reverse ++ [c] := by
    rw [hrev,
      table_take_app_le (postW.reverse ++ [c] ++ preW.reverse) s.stock
        (postW.length + 1) hlX,
      table_take_app_le (postW.reverse ++ [c]) preW.reverse (postW.length + 1) hlA,
      table_take_ge (postW.reverse ++ [c]) (postW.length + 1) (by
        rw [← hlen, List.length_append]; simp)]
  have hdro : (s.stock.reverse ++ s.waste).reverse.drop (postW.length + 1)
      = preW.reverse ++ s.stock := by
    rw [hrev,
      table_drop_app_le (postW.reverse ++ [c] ++ preW.reverse) s.stock
        (postW.length + 1) hlX,
      table_drop_app_le (postW.reverse ++ [c]) preW.reverse (postW.length + 1) hlA,
      table_drop_ge (postW.reverse ++ [c]) (postW.length + 1) (by
        rw [← hlen, List.length_append]; simp),
      List.nil_append]
  have hle2 : postW.length + 1 ≤ (s.stock.reverse ++ s.waste).length := by
    rw [List.length_append, List.length_reverse]
    omega
  -- leg two: the redeal
  have hdr2 : (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep).run
      (List.replicate (postW.length + 1) Move.draw) = some
      (State.mk s.found s.piles (preW.reverse ++ s.stock) (c :: postW) s.drawStep) := by
    have hdsB : (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep).drawStep
        = 1 := hd
    have h0 := @redeal_run1 (State.mk s.found s.piles []
        (s.stock.reverse ++ s.waste) s.drawStep) postW.length hdsB hst hwne hle2
    rw [h0]
    refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
    · show ((s.stock.reverse ++ s.waste).reverse.drop (postW.length + 1)) = _
      rw [hdro]
    · show ((s.stock.reverse ++ s.waste).reverse.take (postW.length + 1)).reverse
          ++ ([] : List Card) = _
      rw [htak, List.reverse_append, List.reverse_reverse, List.append_nil]
      simp
  -- the count splits, the legs glue, the spend fires
  have hc : s.stock.length + postW.length + 1
      = s.stock.length + (postW.length + 1) := by omega
  rw [hc, rep_add, List.append_assoc,
    run_rep_append1 s.stock.length s
      (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep)
      (List.replicate (postW.length + 1) Move.draw ++ [Move.wasteToFound c]) hdr1,
    run_rep_append1 (postW.length + 1)
      (State.mk s.found s.piles [] (s.stock.reverse ++ s.waste) s.drawStep)
      (State.mk s.found s.piles (preW.reverse ++ s.stock) (c :: postW) s.drawStep)
      [Move.wasteToFound c] hdr2,
    run_one1 (wtf_step_raised (rfl : (State.mk s.found s.piles (preW.reverse ++ s.stock)
        (c :: postW) s.drawStep).waste = c :: postW) hng)]
  rfl

/-! ### The nine-case compliant replay induction (in progress) -/

/-- `isWin` reads the foundation heights alone. -/
private theorem isWin_len {s : State} (σ : Suit) (h : s.isWin = true) :
    (s.found σ).length = 13 := by
  have hall := List.all_eq_true.mp h
  exact of_decide_eq_true (hall σ (Suit.mem_all σ))

/-- The take/drop partition of a deal (dedup-marked port of
`Phase`'s private `take_drop_append`). -/
private theorem table_partition {α : Type} : ∀ (n : Nat) (l : List α),
    l.take n ++ l.drop n = l := by
  intro n
  induction n with
  | zero => intro l; simp
  | succ m ih =>
      intro l
      cases l with
      | nil => rfl
      | cons a t =>
          show (a :: t.take m) ++ (t.drop m) = a :: t
          exact congrArg (a :: ·) (ih t)

/-! ### The (C) engine's fuel — fires-readers, keepers, and the
two-step worry undo

The (C)-machinery's local kit.  Dedup-marks per piece: the four
fires-readers are adapted from `Orig/Irreversible.lean`'s private
step-inversion rows (and `Orig/Shuttle.lean`'s private
`step_wasteToTab_inv`, `step_foundToTab_splice`); `step_drawStep_keep`
mirrors `Orig/Progress.lean`'s private `step_drawStep` and
`Orig/Phase.lean`'s private `draw_drawStep`; `foundToTab_return` is
restated at the ONE-Move undo shape (the `reversibleAtW` ∃-form of
`foundToTab_undo` / Classify's `foundToTab_reversibleAtW_of_legal_wf`
does not expose the play it constructs, and the adjacent-cancellation
consumes exactly `step s₁ (tabToFound x) = some st`); `setFound_comm`
is a `State.lean` reader-section candidate.  Everything here cites
publics only. -/

/-- A successful `.foundToTab`: the named card is its suit's
foundation top, the placement is legal, and the successor is the
chopped foundation with the card placed. -/
private theorem foundToTab_fires {st : State} {x : Card} {b : Base} {s₁ : State}
    (h : State.step st (Move.foundToTab x b) = some s₁) :
    st.foundTop x.suit = some x ∧ st.canPlace x b = true ∧
      s₁ = (st.setFound x.suit (chop (st.found x.suit))).putCard x b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      injection h with hEq
      refine ⟨ht.trans (congrArg some (of_decide_eq_true hg.1)), hg.2, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToFound`: the guards held, the waste head is
the moved card, and the successor is the raised foundation with the
waste popped. -/
private theorem wasteToFound_fires {st : State} {y : Card} {s₁ : State}
    (h : State.step st (Move.wasteToFound y) = some s₁) :
    st.wasteIs y = true ∧ st.nextUp y = true ∧
      ∃ w', st.waste = y :: w' ∧
        s₁ = { st.setFound y.suit (st.found y.suit ++ [y]) with waste := w' } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    rw [Bool.and_eq_true] at hg
    split at h
    · rename_i _ v' ws hw
      have hwis := hg.1
      rw [State.wasteIs_cons hw y] at hwis
      have hv : v' = y := of_decide_eq_true hwis
      rw [hv] at hw
      injection h with hEq
      exact ⟨hg.1, hg.2, ws, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.wasteToTab`: the guards held, the waste head is
the moved card, and the successor is the placement with the waste
popped. -/
private theorem wasteToTab_fires {st : State} {y : Card} {b : Base} {s₁ : State}
    (h : State.step st (Move.wasteToTab y b) = some s₁) :
    st.wasteIs y = true ∧ st.canPlace y b = true ∧
      ∃ w', st.waste = y :: w' ∧
        s₁ = { st.putCard y b with waste := w' } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    rw [Bool.and_eq_true] at hg
    split at h
    · rename_i _ v' ws hw
      have hwis := hg.1
      rw [State.wasteIs_cons hw y] at hwis
      have hv : v' = y := of_decide_eq_true hwis
      rw [hv] at hw
      injection h with hEq
      exact ⟨hg.1, hg.2, ws, hw, hEq.symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `.tabToTab`: the run head's pile was located, the
placement is legal, and the successor is the source pile minus the run
with the run placed. -/
private theorem tabToTab_fires {st : State} {y : Card} {b : Base} {s₁ : State}
    (h : State.step st (Move.tabToTab y b) = some s₁) :
    ∃ a, st.pileHolding y = some a ∧ st.canPlace y b = true ∧
      s₁ = (st.setPile a
          (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
            (fromCard y (st.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        injection h with hEq
        exact ⟨a, hh, hcp, hEq.symm⟩
    · exact absurd h (by simp)

/-- The draw step is permanent: no move in the model re-labels the
draw width.  (Mirrors `Orig/Progress.lean`'s private `step_drawStep`;
re-proven here so this chapter cites publics only.) -/
private theorem step_drawStep_keep {st s₁ : State} {m : Move}
    (h : State.step st m = some s₁) : s₁.drawStep = st.drawStep := by
  cases m with
  | draw =>
      obtain ⟨r, hrec, -, hy⟩ := draw_unfold h
      have hrd : r.drawStep = st.drawStep := by
        rw [← hrec]
        by_cases hst : st.stock = []
        · by_cases hw : st.waste = []
          · rw [recycle_allEmpty st hst hw]
          · rw [recycle_nil st hst hw]
        · rw [recycle_keep st hst]
      have : s₁.drawStep = r.drawStep := by rw [hy]
      rw [this, hrd]
  | wasteToFound y =>
      obtain ⟨-, -, w', -, hs⟩ := wasteToFound_fires h
      rw [hs]
      show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = st.drawStep
      exact setFound_drawStep st y.suit _
  | wasteToTab y b =>
      obtain ⟨-, -, w', -, hs⟩ := wasteToTab_fires h
      rw [hs]
      show (st.putCard y b).drawStep = st.drawStep
      exact putCard_drawStep st y b
  | tabToFound y =>
      obtain ⟨-, a, ha⟩ := tabToFound_fires h
      rw [tabToFound_shape h ha]
      show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = st.drawStep
      exact setFound_drawStep st y.suit _
  | foundToTab y b =>
      obtain ⟨-, -, hs⟩ := foundToTab_fires h
      rw [hs]
      have h1 := setFound_drawStep st y.suit (chop (st.found y.suit))
      have h2 := putCard_drawStep (st.setFound y.suit (chop (st.found y.suit))) y b
      rw [h2, h1]
  | tabToTab y b =>
      obtain ⟨a, -, -, hs⟩ := tabToTab_fires h
      rw [hs]
      have h1 := setPile_drawStep st a
        (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))
      have h2 := putRun_drawStep
        (st.setPile a (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp)))
        (fromCard y (st.piles a).faceUp) b
      rw [h2, h1]

/-- The draw keeps every cycle card somewhere spendable: each card of
the recycled-and-dealt pool lands either in the dealt batch (the new
waste) or in the stock remainder. -/
private theorem draw_inCycle {st s₁ : State} {c : Card}
    (h : State.step st Move.draw = some s₁)
    (hc : c ∈ st.stock ∨ c ∈ st.waste) :
    c ∈ s₁.stock ∨ c ∈ s₁.waste := by
  obtain ⟨r, hrec, hrne, hy⟩ := draw_unfold h
  -- the recycle stage keeps the cycle membership
  have hrc : c ∈ r.stock ∨ c ∈ r.waste := by
    rcases hc with hcs | hcw
    · by_cases hst : st.stock = []
      · exact absurd hcs (by rw [hst]; simp)
      · left; rw [← hrec, recycle_keep st hst]; exact hcs
    · by_cases hst : st.stock = []
      · by_cases hwst : st.waste = []
        · exfalso
          rw [← hrec, recycle_allEmpty st hst hwst] at hrne
          rw [hst] at hrne
          exact absurd rfl hrne
        · left
          have hrr : State.recycle st = { st with stock := st.waste.reverse, waste := [] } :=
            recycle_nil st hst hwst
          rw [← hrec, hrr]
          show c ∈ st.waste.reverse
          exact List.mem_reverse.mpr hcw
      · right; rw [← hrec, recycle_keep st hst]; exact hcw
  -- the deal stage splits the stock into take/drop; both parts stay
  -- spendable (the taken batch reverses onto the new waste)
  have hs : s₁.stock = r.stock.drop r.drawStep := by rw [hy, dealUpTo_eq_take_drop]
  have hw : s₁.waste = (r.stock.take r.drawStep).reverse ++ r.waste := by
    rw [hy, dealUpTo_eq_take_drop]
  rcases hrc with hcs | hcw
  · have hsplit : c ∈ r.stock.take r.drawStep ++ r.stock.drop r.drawStep := by
      rw [List.take_append_drop r.drawStep r.stock]
      exact hcs
    rcases List.mem_append.mp hsplit with hleft | hright
    · right
      rw [hw]
      exact List.mem_append.2 (Or.inl (List.mem_reverse.mpr hleft))
    · left; rw [hs]; exact hright
  · right
    rw [hw]
    exact List.mem_append.2 (Or.inr hcw)

/-- An un-exited rung card blocks the win: with `c` still in the draw
cycle, the foundations cannot be complete — a completed foundation
holds every card of its suit, and `WF` conservation forbids `c` from
being both founded and in the cycle. -/
private theorem inCycle_notisWin {st : State} {c : Card}
    (hwf : st.WF) (hc : c ∈ st.stock ∨ c ∈ st.waste) : st.isWin = false := by
  cases hwin : st.isWin with
  | false => rfl
  | true =>
      exfalso
      have h13 : (st.found c.suit).length = 13 := by
        have hall := (List.all_eq_true).mp hwin
        exact of_decide_eq_true (hall c.suit (Suit.mem_all c.suit))
      obtain ⟨n, hn⟩ := hwf.found_prefix c.suit
      have hmin : (st.found c.suit).length = min n 13 := by
        rw [hn, List.length_take, Suit.upCards_length]
      have hnge : 13 ≤ n := by
        rcases Nat.lt_or_ge n 13 with hlt | hge
        · rw [Nat.min_eq_left (Nat.le_of_lt hlt)] at hmin
          omega
        · exact hge
      have hmem : c ∈ st.found c.suit := by
        have hle : (c.suit.upCards).length ≤ n := by
          rw [Suit.upCards_length]; exact hnge
        rw [hn, take_ge_length _ n hle]
        exact Suit.mem_upCards
      obtain ⟨-, hns, hnw, -⟩ := mem_found_unique hwf hmem
      rcases hc with hcs | hcw
      · exact hns hcs
      · exact hnw hcw

/-- **The two-step worry undo.**  At a `WF` state, the adjacent window
`[foundToTab x b; tabToFound x]` is the identity: the restack returns
to the origin in one move, with the foundation restored by the
`chop`-snoc law, the written pile by the round trip of the placement
(`putCard_inr_roundtrip`'s shape), and every other field untouched by
readers.  This is `foundToTab_undo` (Irreversible, private) restated
at the ONE-MOVE shape the adjacent cancellation consumes — the
`reversibleAtW` ∃-form does not expose the constructed play; the
`hnext` arithmetic is Classify's public `wf_found_chop_toIdx`, the
search exactness Integrity's public `pileOfTop_eq_some_iff`. -/
private theorem foundToTab_return {st : State} {x : Card} {b : Base} {s₁ : State}
    (hwf : st.WF) (h : State.step st (Move.foundToTab x b) = some s₁) :
    State.step s₁ (Move.tabToFound x) = some st := by
  obtain ⟨htop, hcp, hs₁⟩ := foundToTab_fires h
  have hwf' : s₁.WF := step_wf hwf h
  have hs₁f : s₁.found x.suit = chop (st.found x.suit) := by
    rw [hs₁, putCard_found, setFound_found_self]
  have hchopidx : (chop (st.found x.suit)).length = x.rank.toIdx :=
    wf_found_chop_toIdx hwf htop
  have hnext : s₁.nextUp x = true := by
    show decide (x.rank.toIdx = (s₁.found x.suit).length) = true
    rw [hs₁f, hchopidx]
    exact decide_eq_true rfl
  have hsnoc : chop (st.found x.suit) ++ [x] = st.found x.suit :=
    (lastOf_chop htop).symm
  -- the foundation with the moved card re-appended is the origin's:
  -- at the moved suit by the snoc law, at every other by the readers
  have hfound : (fun σ => if σ = x.suit then s₁.found x.suit ++ [x] else s₁.found σ)
      = st.found := by
    funext σ
    by_cases hσ : σ = x.suit
    · rw [ite_eq_left hσ, hs₁f, hsnoc, hσ]
    · rw [ite_eq_right hσ]
      show s₁.found σ = st.found σ
      rw [hs₁, putCard_found, setFound_found_ne hσ]
  cases b with
  | inl a =>
      obtain ⟨hempty, -⟩ := canPlace_inl hcp
      obtain ⟨hhid, hface⟩ := (Pile.isEmpty_eq _).mp hempty
      have hstpile : st.piles a = ((⟨[], []⟩ : Pile)) := Pile.ext hhid hface
      have hsk : s₁.piles a = ((⟨[], [x]⟩ : Pile)) := by
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inl a)).piles a = _
        rw [putCard_piles_inl]
        show (if a = a then ((⟨[], [x]⟩ : Pile)) else _) = _
        rw [ite_eq_left rfl]
      have hkeep : ∀ a' : Anchor, a' ≠ a → s₁.piles a' = st.piles a' := by
        intro a' hne
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inl a)).piles a'
          = st.piles a'
        rw [putCard_piles_inl]
        show (if a' = a then ((⟨[], [x]⟩ : Pile)) else _) = st.piles a'
        rw [ite_eq_right hne, setFound_piles]
      have htops₁ : (s₁.piles a).top = some x := by
        rw [hsk]
        rfl
      have hsrch : s₁.pileOfTop x = some a :=
        (pileOfTop_eq_some_iff hwf').mpr htops₁
      rw [step_tabToFound_splice hnext hsrch]
      refine congrArg some (?_ :
        { s₁.setFound x.suit (s₁.found x.suit ++ [x]) with
          piles := fun a' => if a' = a then
              Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp)
            else s₁.piles a' } = st)
      apply State.ext
      · exact hfound
      · funext a'
        show (if a' = a then
              Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp)
            else s₁.piles a') = st.piles a'
        by_cases ha' : a' = a
        · rw [ha', ite_eq_left rfl]
          show Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp) = st.piles a
          rw [hsk, hstpile]
          rfl
        · rw [ite_eq_right ha']
          exact hkeep a' ha'
      · show s₁.stock = st.stock
        rw [hs₁, putCard_stock, setFound_stock]
      · show s₁.waste = st.waste
        rw [hs₁, putCard_waste, setFound_waste]
      · show s₁.drawStep = st.drawStep
        rw [hs₁, putCard_drawStep, setFound_drawStep]
  | inr z =>
      obtain ⟨k, hz, -⟩ := canPlace_inr hcp
      have hz' : (st.setFound x.suit (chop (st.found x.suit))).pileOfTop z = some k := hz
      obtain ⟨hfkne, -⟩ := pileOfTop_top hz
      have hsk : s₁.piles k = { st.piles k with faceUp := (st.piles k).faceUp ++ [x] } := by
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inr z)).piles k = _
        rw [putCard_piles_inr _ _ _ _ hz']
        show (if k = k then
            ({ st.piles k with faceUp := (st.piles k).faceUp ++ [x] } : Pile) else _) = _
        rw [ite_eq_left rfl]
      have hkeep : ∀ a' : Anchor, a' ≠ k → s₁.piles a' = st.piles a' := by
        intro a' hne
        rw [hs₁]
        show ((st.setFound x.suit (chop (st.found x.suit))).putCard x (Sum.inr z)).piles a'
          = st.piles a'
        rw [putCard_piles_inr _ _ _ _ hz']
        show (if a' = k then
            ({ st.piles k with faceUp := (st.piles k).faceUp ++ [x] } : Pile) else _) = st.piles a'
        rw [ite_eq_right hne, setFound_piles]
      have htops₁ : (s₁.piles k).top = some x := by
        rw [hsk]
        exact lastOf_snoc
      have hsrch : s₁.pileOfTop x = some k :=
        (pileOfTop_eq_some_iff hwf').mpr htops₁
      rw [step_tabToFound_splice hnext hsrch]
      refine congrArg some (?_ :
        { s₁.setFound x.suit (s₁.found x.suit ++ [x]) with
          piles := fun a' => if a' = k then
              Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
            else s₁.piles a' } = st)
      apply State.ext
      · exact hfound
      · funext a'
        show (if a' = k then
              Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
            else s₁.piles a') = st.piles a'
        by_cases ha' : a' = k
        · rw [ha', ite_eq_left rfl]
          show Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp) = st.piles k
          rw [hsk]
          show Pile.afterRunRemoved
              { st.piles k with faceUp := (st.piles k).faceUp ++ [x] }
              (chop ((st.piles k).faceUp ++ [x])) = st.piles k
          rw [chop_snoc, afterRunRemoved_ne hfkne]
        · rw [ite_eq_right ha']
          exact hkeep a' ha'
      · show s₁.stock = st.stock
        rw [hs₁, putCard_stock, setFound_stock]
      · show s₁.waste = st.waste
        rw [hs₁, putCard_waste, setFound_waste]
      · show s₁.drawStep = st.drawStep
        rw [hs₁, putCard_drawStep, setFound_drawStep]

/-- Two foundation writes at distinct suits commute.  (A
`State.lean` reader-section candidate, dedup-marked.) -/
private theorem setFound_comm {st : State} {s₁ s₂ : Suit} {l₁ l₂ : List Card}
    (hne : s₁ ≠ s₂) :
    (st.setFound s₁ l₁).setFound s₂ l₂ = (st.setFound s₂ l₂).setFound s₁ l₁ := by
  apply State.ext
  · funext σ
    show (if σ = s₂ then l₂ else (if σ = s₁ then l₁ else st.found σ)) =
      (if σ = s₁ then l₁ else (if σ = s₂ then l₂ else st.found σ))
    by_cases hs : σ = s₁
    · have hs2 : σ ≠ s₂ := by rw [hs]; exact hne
      rw [ite_eq_right hs2, ite_eq_left hs, ite_eq_left hs]
    · by_cases hs' : σ = s₂
      · rw [ite_eq_left hs', ite_eq_right hs, ite_eq_left hs']
      · rw [ite_eq_right hs', ite_eq_right hs, ite_eq_right hs, ite_eq_right hs']
  · rfl
  · rfl
  · rfl
  · rfl

/-- Placements at twin carriers write the same piles when the
carriers' piles agree.  (The putCard readers, lifted one state up —
the squares' shared channel; a `State.lean`/`Play.lean` reader-section
candidate, dedup-marked.) -/
private theorem putCard_piles_eq_of_eq {A B : State} (hpl : A.piles = B.piles)
    (c : Card) (b : Base) :
    (A.putCard c b).piles = (B.putCard c b).piles := by
  cases b with
  | inl a =>
      rw [putCard_piles_inl, putCard_piles_inl]
      funext a'
      by_cases haa : a' = a
      · rw [ite_eq_left haa, ite_eq_left haa]
      · rw [ite_eq_right haa, ite_eq_right haa]
        show A.piles a' = B.piles a'
        rw [hpl]
  | inr z =>
      have hzEq : A.pileOfTop z = B.pileOfTop z := by
        show firstWhere (fun a' => decide ((A.piles a').top = some z)) Anchor.all =
          firstWhere (fun a' => decide ((B.piles a').top = some z)) Anchor.all
        rw [hpl]
      cases hzA : A.pileOfTop z with
      | none =>
          have hzB : B.pileOfTop z = none := by rw [← hzEq, hzA]
          have hAn : A.putCard c (Sum.inr z) = A := by
            show (match A.pileOfTop z with
              | some k => A.setPile k { A.piles k with faceUp := (A.piles k).faceUp ++ [c] }
              | none => A) = A
            rw [hzA]
          have hBn : B.putCard c (Sum.inr z) = B := by
            show (match B.pileOfTop z with
              | some k => B.setPile k { B.piles k with faceUp := (B.piles k).faceUp ++ [c] }
              | none => B) = B
            rw [hzB]
          show (A.putCard c (Sum.inr z)).piles = (B.putCard c (Sum.inr z)).piles
          rw [hAn, hBn, hpl]
      | some k =>
          have hzB : B.pileOfTop z = some k := by rw [← hzEq, hzA]
          have hAk : A.piles k = B.piles k := by rw [hpl]
          rw [putCard_piles_inr _ _ _ _ hzA, putCard_piles_inr _ _ _ _ hzB]
          funext a'
          by_cases haa : a' = k
          · rw [ite_eq_left haa, ite_eq_left haa, hAk]
          · rw [ite_eq_right haa, ite_eq_right haa]
            show A.piles a' = B.piles a'
            rw [hpl]

/-- The raise's successor at the popped tail — the square's
intermediate, once (local to the square's bookkeeping). -/
private def sq2S (st : State) (y : Card) (w' : List Card) : State :=
  { st.setFound y.suit (st.found y.suit ++ [y]) with waste := w' }

/-- **The window square: `wasteToFound`.**  A foundation raise of
another suit and a c-suit worry-back commute — the raise reads the
waste and writes its own suit's slot; the worry reads the worried
suit's slot and the piles — so both orders land at the SAME
composite.  The raised suit must differ from the worry's own (an
x-suited raiser inside the open window would have to be the restack
itself, pinned by the rung and conservation).  (The spread
residue's route names this square as a paid leg of the window
bubbling; it is the pattern-kernel — the same guard-transfer shape
and the same `putCard_piles_eq_of_eq` channel — for the remaining
squares' cornered statements.) -/
private theorem foundToTab_wasteToFound_square {st : State} {x y : Card} {b : Base}
    {s₁ t : State}
    (hxs : y.suit ≠ x.suit)
    (hf : State.step st (Move.foundToTab x b) = some s₁)
    (hm : State.step s₁ (Move.wasteToFound y) = some t) :
    ∃ s₂, State.step st (Move.wasteToFound y) = some s₂ ∧
      State.step s₂ (Move.foundToTab x b) = some t := by
  obtain ⟨htop, hcp, hs₁⟩ := foundToTab_fires hf
  obtain ⟨hwis, hny, w', hw, ht⟩ := wasteToFound_fires hm
  -- the worry's readers at the two slots
  have hs₁read : ∀ σ, s₁.found σ =
      (if σ = x.suit then chop (st.found x.suit) else st.found σ) := by
    intro σ
    rw [hs₁, putCard_found]
    rfl
  have hs₁p : s₁.piles = (st.putCard x b).piles := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).piles = _
    exact putCard_piles_eq_of_eq (setFound_piles st x.suit (chop (st.found x.suit))) x b
  have hsw : s₁.waste = st.waste := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).waste = _
    rw [putCard_waste, setFound_waste]
  have hwst : st.waste = y :: w' := by rw [← hsw]; exact hw
  -- the raise's guards reread at `st`: the waste is the worry's
  -- verbatim, and the raise's slot shares no suit with the worry
  have hstfy : st.found y.suit = s₁.found y.suit := by
    rw [hs₁]
    show st.found y.suit =
      ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).found y.suit
    rw [putCard_found, setFound_found_ne hxs]
  have hwis' : st.wasteIs y = true := by
    show (match st.waste with
      | [] => false
      | c' :: _ => decide (c' = y)) = true
    rw [hwst]
    exact decide_eq_true rfl
  have hny' : st.nextUp y = true := by
    show decide (y.rank.toIdx = (st.found y.suit).length) = true
    rw [hstfy]
    exact hny
  have hs₁stock : s₁.stock = st.stock := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).stock = _
    rw [putCard_stock, setFound_stock]
  have hs₁ds : s₁.drawStep = st.drawStep := by
    rw [hs₁]
    show ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).drawStep = _
    rw [putCard_drawStep, setFound_drawStep]
  -- the raise fires at `st` with the same waste tail
  have hraise : State.step st (Move.wasteToFound y) =
      some { st.setFound y.suit (st.found y.suit ++ [y]) with waste := w' } := by
    show (if st.wasteIs y && st.nextUp y then
        match st.waste with
        | _ :: cs => some { st.setFound y.suit (st.found y.suit ++ [y]) with waste := cs }
        | [] => none
      else none) = _
    rw [show (st.wasteIs y && st.nextUp y) = true from by rw [hwis', hny']; rfl, hwst]
    rfl
  refine ⟨sq2S st y w', hraise, ?_⟩
  -- the worry's guards reread at the raise's successor
  have hs₂fx : (sq2S st y w').found x.suit = st.found x.suit := by
    show (st.setFound y.suit (st.found y.suit ++ [y])).found x.suit = _
    exact setFound_found_ne (Ne.symm hxs)
  have hs₂read : ∀ σ, (sq2S st y w').found σ
      = (if σ = y.suit then st.found y.suit ++ [y] else st.found σ) := fun _ => rfl
  have htop₂ : (sq2S st y w').foundTop x.suit = some x := by
    show lastOf ((sq2S st y w').found x.suit) = some x
    rw [hs₂fx]
    exact htop
  have hcp₂ : (sq2S st y w').canPlace x b = true := by
    show st.canPlace x b
    exact hcp
  rw [step_foundToTab_splice htop₂ hcp₂, Option.some.injEq]
  apply State.ext
  · funext σ
    rw [putCard_found, ht]
    show (if σ = x.suit then chop ((sq2S st y w').found x.suit) else (sq2S st y w').found σ) =
      (if σ = y.suit then s₁.found y.suit ++ [y] else s₁.found σ)
    rw [hs₂fx, hs₂read σ, hs₁read σ, hs₁read y.suit, ite_eq_right hxs]
    by_cases hσx : σ = x.suit
    · rw [hσx, ite_eq_left rfl, ite_eq_right (Ne.symm hxs), ite_eq_left rfl]
    · by_cases hσy : σ = y.suit
      · rw [hσy, ite_eq_right hxs, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right hσx, ite_eq_right hσy, ite_eq_right hσy, ite_eq_right hσx]
  · funext a'
    have hAT : (((sq2S st y w').setFound x.suit
          (chop ((sq2S st y w').found x.suit))).putCard x b).piles
        = (st.putCard x b).piles := by
        refine putCard_piles_eq_of_eq ?_ x b
        show ((sq2S st y w').setFound x.suit
            (chop ((sq2S st y w').found x.suit))).piles = st.piles
        show (st.setFound y.suit (st.found y.suit ++ [y])).piles = st.piles
        rw [setFound_piles]
    have htp : t.piles a' = (st.putCard x b).piles a' := by
      rw [ht]
      show (s₁.setFound y.suit (s₁.found y.suit ++ [y])).piles a' = (st.putCard x b).piles a'
      rw [setFound_piles, hs₁p]
    show (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).piles a'
      = t.piles a'
    rw [hAT, ← htp]
  · have hL : (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).stock
        = st.stock := by
      rw [putCard_stock, setFound_stock]
      show (st.setFound y.suit (st.found y.suit ++ [y])).stock = st.stock
      rw [setFound_stock]
    rw [hL, ht]
    show st.stock = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).stock
    rw [setFound_stock, hs₁stock]
  · have hL : (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).waste
        = w' := by
      rw [putCard_waste, setFound_waste]
      rfl
    rw [hL, ht]
  · have hL : (((sq2S st y w').setFound x.suit (chop ((sq2S st y w').found x.suit))).putCard x b).drawStep
        = st.drawStep := by
      rw [putCard_drawStep, setFound_drawStep]
      show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = st.drawStep
      rw [setFound_drawStep]
    rw [hL, ht]
    show st.drawStep = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).drawStep
    rw [setFound_drawStep, hs₁ds]

/-! ### The (A) kit — congruence readers, run glue, draw readers

The replay machinery for the reserve lemma below: the per-state field
congruences (over `Orig/Twin.lean`'s public `firstWhere_congr`), the
run glue (`run_step_cons`, `run_replicate_append`) and the draw
readers (`draw_shape_plain`/`_base`, `draw_cycleOf`, `drain_full`),
which mirror `Orig/Phase.lean`'s private copies
(`drain_positions_one` et al.) specialized to `drawStep = 1` —
dedup-marked, promote at harvest. -/

/-- The pile-top read is a piles-field read. -/
private theorem topOf_congr {u v : State} (a : Anchor) (h : u.piles = v.piles) :
    u.topOf a = v.topOf a := by
  show (u.piles a).top = (v.piles a).top
  exact congrArg Pile.top (congrFun h a)

/-- The top-search is a piles-field read. -/
private theorem pileOfTop_congr {u v : State} (z : Card) (h : u.piles = v.piles) :
    u.pileOfTop z = v.pileOfTop z := by
  show firstWhere (fun a => decide (u.topOf a = some z)) Anchor.all = _
  exact firstWhere_congr (p := fun a => decide (u.topOf a = some z))
    (q := fun a => decide (v.topOf a = some z)) (fun a => by rw [topOf_congr a h])
    (l := Anchor.all)

/-- The placement guard is a piles-field read. -/
private theorem canPlace_congr {u v : State} (c : Card) (b : Base)
    (h : u.piles = v.piles) : u.canPlace c b = v.canPlace c b := by
  cases b with
  | inl a =>
      show ((u.piles a).isEmpty && decide (c.rank = Rank.king))
          = ((v.piles a).isEmpty && decide (c.rank = Rank.king))
      rw [congrArg Pile.isEmpty (congrFun h a)]
  | inr z =>
      show (match u.pileOfTop z with
        | some _ => canSitOn c z | none => false) = _
      rw [pileOfTop_congr z h]
      rfl

/-- The foundation-next read is a found-field read. -/
private theorem nextUp_congr {u v : State} (c : Card) (h : u.found = v.found) :
    u.nextUp c = v.nextUp c :=
  congrArg (fun (f : Suit → List Card) => decide (c.rank.toIdx = (f c.suit).length)) h

/-- The foundation-top read is a found-field read. -/
private theorem foundTop_congr {u v : State} (s : Suit) (h : u.found = v.found) :
    u.foundTop s = v.foundTop s := by
  simp only [State.foundTop]
  rw [congrFun h s]

/-- The win predicate is a found-field read. -/
private theorem isWin_congr {u v : State} (h : u.found = v.found) :
    u.isWin = v.isWin := by
  show (Suit.all.all fun σ => decide ((u.found σ).length = 13)) =
    (Suit.all.all fun σ => decide ((v.found σ).length = 13))
  rw [h]

/-- A foundation update's `found` field, read as the guard function. -/
private theorem setFound_found_eq (st : State) (s : Suit) (l : List Card) :
    (st.setFound s l).found = fun σ => if σ = s then l else st.found σ := rfl

/-- A pile update's `piles` field, read as the guard function. -/
private theorem setPile_piles_eq (st : State) (a : Anchor) (p : Pile) :
    (st.setPile a p).piles = fun a' => if a' = a then p else st.piles a' := rfl

/-- The readers' transfer: the append-write agrees under found equality. -/
private theorem found_append_transfer {s t : State} {c : Card}
    (hf : s.found = t.found) :
    (s.setFound c.suit (s.found c.suit ++ [c])).found =
      (t.setFound c.suit (t.found c.suit ++ [c])).found := by
  rw [setFound_found_eq, setFound_found_eq]
  funext σ
  by_cases hs : σ = c.suit
  · rw [ite_eq_left hs, ite_eq_left hs, congrFun hf c.suit]
  · rw [ite_eq_right hs, ite_eq_right hs, congrFun hf σ]

/-- The readers' transfer: the chop-write agrees under found equality. -/
private theorem found_chop_transfer {s t : State} {c : Card}
    (hf : s.found = t.found) :
    (s.setFound c.suit (chop (s.found c.suit))).found =
      (t.setFound c.suit (chop (t.found c.suit))).found := by
  rw [setFound_found_eq, setFound_found_eq]
  funext σ
  by_cases hs : σ = c.suit
  · rw [ite_eq_left hs, ite_eq_left hs, congrFun hf c.suit]
  · rw [ite_eq_right hs, ite_eq_right hs, congrFun hf σ]

/-- The placement of one card agrees under piles equality. -/
private theorem putCard_piles_congr {s t : State} {c : Card} {b : Base}
    (hp : s.piles = t.piles) :
    (s.putCard c b).piles = (t.putCard c b).piles := by
  cases b with
  | inl a =>
      rw [show s.putCard c (Sum.inl a) = s.setPile a ⟨[], [c]⟩ from rfl,
        show t.putCard c (Sum.inl a) = t.setPile a ⟨[], [c]⟩ from rfl,
        setPile_piles_eq, setPile_piles_eq]
      funext a'
      by_cases ha : a' = a
      · rw [ha, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']
  | inr z =>
      rw [show s.putCard c (Sum.inr z) =
          (match s.pileOfTop z with
            | some k => s.setPile k { s.piles k with faceUp := (s.piles k).faceUp ++ [c] }
            | none => s) from rfl,
        show t.putCard c (Sum.inr z) =
          (match t.pileOfTop z with
            | some k => t.setPile k { t.piles k with faceUp := (t.piles k).faceUp ++ [c] }
            | none => t) from rfl,
        pileOfTop_congr z hp]
      cases hopt : t.pileOfTop z with
      | none => exact hp
      | some k =>
          rw [setPile_piles_eq, setPile_piles_eq]
          funext a'
          by_cases ha : a' = k
          · rw [ha, ite_eq_left rfl, ite_eq_left rfl, congrFun hp k]
          · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']

/-- The placement of a run agrees under piles equality. -/
private theorem putRun_piles_congr {s t : State} {r₁ r₂ : List Card} {b : Base}
    (hp : s.piles = t.piles) (hr : r₁ = r₂) :
    (s.putRun r₁ b).piles = (t.putRun r₂ b).piles := by
  cases b with
  | inl a =>
      rw [show s.putRun r₁ (Sum.inl a) = s.setPile a ⟨[], r₁⟩ from rfl,
        show t.putRun r₂ (Sum.inl a) = t.setPile a ⟨[], r₂⟩ from rfl,
        setPile_piles_eq, setPile_piles_eq, hr]
      funext a'
      by_cases ha : a' = a
      · rw [ha, ite_eq_left rfl, ite_eq_left rfl]
      · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']
  | inr z =>
      rw [show s.putRun r₁ (Sum.inr z) =
          (match s.pileOfTop z with
            | some k => s.setPile k { s.piles k with faceUp := (s.piles k).faceUp ++ r₁ }
            | none => s) from rfl,
        show t.putRun r₂ (Sum.inr z) =
          (match t.pileOfTop z with
            | some k => t.setPile k { t.piles k with faceUp := (t.piles k).faceUp ++ r₂ }
            | none => t) from rfl,
        pileOfTop_congr z hp, hr]
      cases hopt : t.pileOfTop z with
      | none => exact hp
      | some k =>
          rw [setPile_piles_eq, setPile_piles_eq]
          funext a'
          by_cases ha : a' = k
          · rw [ha, ite_eq_left rfl, ite_eq_left rfl, congrFun hp k]
          · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']

/-! ### The (A) kit — the run glue and the draw readers -/

/-- The step projection of `State.run`, one move. -/
private theorem run_step_cons {u u₁ : State} {m : Move} {rest : List Move}
    (h : State.step u m = some u₁) : u.run (m :: rest) = u₁.run rest := by
  show (match State.step u m with
      | some st' => State.run st' rest | none => none) = State.run u₁ rest
  rw [h]

/-- The plain draw at step 1, exactly: one card off the stock's front,
reversed onto the waste's front. -/
private theorem draw_shape_plain {u : State} {c : Card} {cs : List Card}
    (hds : u.drawStep = 1) (h : u.stock = c :: cs) : State.step u Move.draw = some
      { u with stock := cs, waste := c :: u.waste } := by
  rw [show State.step u Move.draw = State.dealStock (State.recycle u) from rfl,
    show State.recycle u = u from recycle_keep u (by
      rw [h]; exact fun hc => absurd hc (by simp)),
    dealStock_eq_of_ne_nil u (by rw [h]; exact fun hc => absurd hc (by simp)),
    dealUpTo_eq_take_drop, hds, h]
  rfl

/-- The pass-end draw at step 1: the recycled waste's first card comes
back out. -/
private theorem draw_shape_base {u : State} {b : Card} {bs : List Card}
    (hds : u.drawStep = 1) (hst : u.stock = [])
    (hw : u.waste.reverse = b :: bs) :
    State.step u Move.draw = some { u with stock := bs, waste := [b] } := by
  have hne : u.waste ≠ [] := by
    intro hc
    rw [hc, List.reverse_nil] at hw
    exact absurd hw (by simp)
  rw [show State.step u Move.draw = State.dealStock (State.recycle u) from rfl,
    show State.recycle u = { u with stock := u.waste.reverse, waste := [] } from by
      rw [recycle_nil u hst hne, hw],
    hw, dealStock_eq_of_ne_nil _ (by simp),
    dealUpTo_eq_take_drop, hds]
  rfl

/-- A step-1 draw needs only the cycle. -/
private theorem draw_step_fires {u : State} (hds : u.drawStep = 1)
    (hcy : cycleOf u ≠ []) : ∃ u₁, State.step u Move.draw = some u₁ := by
  cases hs : u.stock with
  | cons c cs => exact ⟨_, draw_shape_plain hds hs⟩
  | nil =>
      cases hw : u.waste with
      | nil =>
          exfalso
          exact hcy (by
            rw [show cycleOf u = u.stock ++ u.waste.reverse from rfl, hs, hw]
            rfl)
      | cons x xs =>
          have hrev : u.waste.reverse ≠ [] := by
            intro hc
            have hl : u.waste.length = 0 := by
              have h1 := congrArg List.length hc
              rw [List.length_reverse, List.length_nil] at h1
              exact h1
            rw [hw] at hl
            have h2 : (x :: xs).length = xs.length + 1 := rfl
            omega
          obtain ⟨b, bs, hbs⟩ := list_cons_of_ne_nil hrev
          exact ⟨_, draw_shape_base hds hs hbs⟩

/-- A successful step-1 draw succeeds only over a nonempty cycle. -/
private theorem draw_ne_of_fires {u u₁ : State}
    (h : State.step u Move.draw = some u₁) : cycleOf u ≠ [] := by
  obtain ⟨r, hreq, hrne, -⟩ := draw_unfold h
  cases hs : u.stock with
  | cons c cs =>
      intro hc
      rw [show cycleOf u = u.stock ++ u.waste.reverse from rfl, hs] at hc
      exact absurd hc (by simp)
  | nil =>
      have hwl : u.waste ≠ [] := by
        intro hc0
        have hru : State.recycle u = u := by simp only [State.recycle, hs, hc0]
        rw [hru] at hreq
        rw [← hreq] at hrne
        rw [hs] at hrne
        exact hrne rfl
      intro hc
      obtain ⟨y, ys, hcon⟩ := list_cons_of_ne_nil hwl
      rw [show cycleOf u = u.stock ++ u.waste.reverse from rfl, hs, hcon] at hc
      exact absurd hc (by simp)

/-- **The draw rotation.**  A successful draw at step 1 moves the dealt
cycle's head to its tail — `cycleOf` rotates left, regardless of the
phase (how far the cycle has been dealt). -/
private theorem draw_cycleOf {s s' : State}
    (hds : s.drawStep = 1) (h : State.step s Move.draw = some s') :
    cycleOf s' = (cycleOf s).drop 1 ++ (cycleOf s).take 1 := by
  cases hs : s.stock with
  | cons c cs =>
      rw [draw_shape_plain hds hs] at h
      have heq : s' = { s with stock := cs, waste := c :: s.waste } :=
        (Option.some.inj h).symm
      have hcy : cycleOf s = c :: (cs ++ s.waste.reverse) := by
        show s.stock ++ s.waste.reverse = _
        rw [hs]
        rfl
      rw [heq, hcy]
      show cs ++ (c :: s.waste).reverse
          = (c :: (cs ++ s.waste.reverse)).drop 1
            ++ (c :: (cs ++ s.waste.reverse)).take 1
      rw [show (c :: (cs ++ s.waste.reverse)).drop 1 = cs ++ s.waste.reverse from rfl,
          show (c :: (cs ++ s.waste.reverse)).take 1 = [c] from rfl,
          List.reverse_cons, List.append_assoc]
  | nil =>
      cases hw : s.waste with
      | nil =>
          exfalso
          have hrd : State.recycle s = s := by simp only [State.recycle, hs, hw]
          rw [show State.step s Move.draw = State.dealStock (State.recycle s) from rfl,
              hrd, dealStock_nil s hs] at h
          exact absurd h (by simp)
      | cons x xs =>
          have hrev : s.waste.reverse ≠ [] := by
            intro hc
            have hl : s.waste.length = 0 := by
              have h1 := congrArg List.length hc
              rw [List.length_reverse, List.length_nil] at h1
              exact h1
            rw [hw] at hl
            have h2 : (x :: xs).length = xs.length + 1 := rfl
            omega
          obtain ⟨b, bs, hbs⟩ := list_cons_of_ne_nil hrev
          rw [draw_shape_base hds hs hbs] at h
          have heq : s' = { s with stock := bs, waste := [b] } :=
            (Option.some.inj h).symm
          have hcy : cycleOf s = b :: bs := by
            show s.stock ++ s.waste.reverse = _
            rw [hs, hbs]
            rfl
          rw [heq, hcy]
          show bs ++ [b].reverse = (b :: bs).drop 1 ++ (b :: bs).take 1
          rw [show (b :: bs).drop 1 = bs from rfl,
              show (b :: bs).take 1 = [b] from rfl]
          rfl

/-- **The full drain.**  At step 1, `q` consecutive draws from a
matching stock move exactly its first `q` cards onto the waste,
list-exact (`drain_positions_one` at `drawStep = 1`, the Phase copy's
step-1 specialization). -/
private theorem drain_full : ∀ (q : Nat) (u : State) (l : List Card),
    u.drawStep = 1 → l.length = q → u.stock = l →
    u.run (List.replicate q Move.draw) = some
      { u with stock := l.drop q, waste := (l.take q).reverse ++ u.waste } := by
  intro q
  induction q with
  | zero =>
      intro u l hds hlen hst
      have hl : l = [] := by
        cases l with
        | nil => rfl
        | cons a t =>
            have h1 : (a :: t).length = t.length + 1 := rfl
            rw [hlen] at h1
            omega
      subst hl
      exact congrArg some (State.ext rfl rfl hst rfl rfl)
  | succ q ih =>
      intro u l hds hlen hst
      have hne : l ≠ [] := by
        cases l with
        | cons a t' =>
            show (a :: t') ≠ []
            exact List.cons_ne_nil a t'
        | nil =>
            have h0 : (0 : Nat) = q + 1 := hlen
            exact absurd h0 (by omega)
      obtain ⟨x, t, hl⟩ := list_cons_of_ne_nil hne
      have hsx : u.stock = x :: t := by rw [hst, hl]
      have hstep := draw_shape_plain hds hsx
      rw [show List.replicate (q + 1) Move.draw
            = Move.draw :: List.replicate q Move.draw from rfl,
          run_step_cons hstep]
      have htlen : t.length = q := by
        rw [hl] at hlen
        have h1 : (x :: t).length = t.length + 1 := rfl
        omega
      have hrecv := ih { u with stock := t, waste := x :: u.waste } t hds htlen rfl
      rw [hrecv, hl]
      have hw : (t.take q).reverse ++ (x :: u.waste)
          = ((x :: t).take (q + 1)).reverse ++ u.waste := by
        rw [show (x :: t).take (q + 1) = x :: t.take q from rfl,
            List.reverse_cons, List.append_assoc]
        rfl
      exact congrArg some (State.ext rfl rfl rfl hw rfl)

/-- The presented cycle ends at the waste top. -/
private theorem cycleOf_eq_snoc {u : State} {x : Card} {ws : List Card}
    (h : u.waste = x :: ws) : cycleOf u = (u.stock ++ ws.reverse) ++ [x] := by
  show u.stock ++ u.waste.reverse = _
  rw [h, List.reverse_cons, List.append_assoc]

/-- Two states with equal cycles agree on the waste top. -/
private theorem waste_head_of_cycle {s t : State} {x y : Card} {ws xs : List Card}
    (hu : s.waste = x :: ws) (hv : t.waste = y :: xs)
    (hcy : cycleOf s = cycleOf t) : y = x := by
  have h1 : (s.stock ++ ws.reverse) ++ [x] = (t.stock ++ xs.reverse) ++ [y] := by
    rw [← cycleOf_eq_snoc hu, ← cycleOf_eq_snoc hv, hcy]
  have h2 := congrArg lastOf h1
  rw [lastOf_snoc (front := s.stock ++ ws.reverse),
      lastOf_snoc (front := t.stock ++ xs.reverse)] at h2
  exact (Option.some.inj h2).symm

/-- A successful `wasteToFound`, exactly: guard, the waste top is the
move's own card, the successor's shape. -/
private theorem step_wasteToFound_inv' {u : State} {x : Card} {u₁ : State}
    (h : State.step u (.wasteToFound x) = some u₁) :
    (u.wasteIs x && u.nextUp x) = true ∧ ∃ ws, u.waste = x :: ws ∧
      u₁ = { u.setFound x.suit (u.found x.suit ++ [x]) with waste := ws } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ y ys hw
      have hg0 : (u.wasteIs x && u.nextUp x) = true := hg
      rw [Bool.and_eq_true, State.wasteIs_cons hw x] at hg
      have hy : y = x := of_decide_eq_true hg.1
      rw [hy] at hw
      exact ⟨hg0, ys, hw, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `wasteToTab`, exactly: guard, the waste top is the
move's own card, the successor's shape. -/
private theorem step_wasteToTab_inv' {u : State} {x : Card} {b : Base} {u₁ : State}
    (h : State.step u (.wasteToTab x b) = some u₁) :
    (u.wasteIs x && u.canPlace x b) = true ∧ ∃ ws, u.waste = x :: ws ∧
      u₁ = { u.putCard x b with waste := ws } := by
  simp only [State.step] at h
  split at h
  · rename_i hg
    split at h
    · rename_i _ y ys hw
      have hg0 : (u.wasteIs x && u.canPlace x b) = true := hg
      rw [Bool.and_eq_true, State.wasteIs_cons hw x] at hg
      have hy : y = x := of_decide_eq_true hg.1
      rw [hy] at hw
      exact ⟨hg0, ys, hw, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `foundToTab`, exactly: the named card is the top of
its foundation, the placement is legal, the successor is the chopped
foundation with the card placed. -/
private theorem step_foundToTab_inv' {u : State} {x : Card} {b : Base} {u₁ : State}
    (h : State.step u (.foundToTab x b) = some u₁) :
    ∃ c', u.foundTop x.suit = some c' ∧ c' = x ∧ u.canPlace x b = true ∧
      u₁ = (u.setFound x.suit (chop (u.found x.suit))).putCard x b := by
  simp only [State.step] at h
  split at h
  · split at h
    · rename_i _ c' ht hg
      rw [Bool.and_eq_true] at hg
      exact ⟨c', ht, of_decide_eq_true hg.1, hg.2, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- A successful `tabToTab`, exactly: the run head's pile was located,
the placement is legal, the face-up run from the head is nonempty, and
the successor is the pile-with-run-removed then the run placed. -/
private theorem step_tabToTab_inv' {u : State} {x : Card} {b : Base} {u₁ : State}
    (h : State.step u (.tabToTab x b) = some u₁) :
    ∃ a, u.pileHolding x = some a ∧ u.canPlace x b = true ∧
      fromCard x (u.piles a).faceUp ≠ [] ∧
      u₁ = (u.setPile a (Pile.afterRunRemoved (u.piles a) (below x (u.piles a).faceUp))).putRun
        (fromCard x (u.piles a).faceUp) b := by
  simp only [State.step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i _ a hh
    split at h
    · rename_i hcp
      split at h
      · exact absurd h (by simp)
      · rename_i _ hne
        exact ⟨a, hh, hcp, hne, (Option.some.inj h).symm⟩
    · exact absurd h (by simp)

/-! ### The (A) sink — the transfers and the twin replay -/

/-- Shared tails make equal snoc-appendages (the append-injectivity
worked by induction). -/
private theorem snoc_tail_eq {A B : List Card} {x : Card}
    (h : A ++ [x] = B ++ [x]) : A = B := by
  induction A generalizing B with
  | nil =>
      cases B with
      | nil => rfl
      | cons b bs =>
          rw [List.nil_append, List.cons_append] at h
          exact absurd h (by simp)
  | cons a as ih =>
      cases B with
      | nil =>
          rw [List.cons_append, List.nil_append] at h
          exact absurd h (by simp)
      | cons b bs =>
          rw [List.cons_append, List.cons_append] at h
          injection h with hab htl
          rw [hab]
          exact congrArg (b :: ·) (ih htl)

/-- A successful draw keeps the draw step. -/
private theorem stepDraw_keep_drawStep {u u₁ : State} (h : u.stepDraw = some u₁) :
    u₁.drawStep = u.drawStep := by
  obtain ⟨r, hreq, -, hs'⟩ := draw_unfold h
  rw [hs']
  show r.drawStep = u.drawStep
  rw [← hreq]
  cases hs : u.stock <;> cases hw : u.waste <;>
    simp only [State.recycle, hs, hw]

/-- `putCard`, wherever it lands, writes no foundation. -/
private theorem putCard_found_keep {u : State} {c : Card} {b : Base} :
    (u.putCard c b).found = u.found := by
  cases b with
  | inl a => exact putCard_inl_found c a
  | inr z => exact putCard_inr_found c z

/-- `putRun`, wherever it lands, writes no foundation. -/
private theorem putRun_found_keep {u : State} {run : List Card} {b : Base} :
    (u.putRun run b).found = u.found := by
  cases b with
  | inl a => rfl
  | inr z =>
      rw [show u.putRun run (Sum.inr z) =
          (match u.pileOfTop z with
            | some k => u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ run }
            | none => u) from rfl]
      cases u.pileOfTop z with
      | none => rfl
      | some k => rfl

/-- The players' transfer of the `tabToFound` pile write. -/
private theorem piles_afterRunRemoved_transfer {s t : State} {a : Anchor}
    (hp : s.piles = t.piles) :
    (fun a' => if a' = a then
        Pile.afterRunRemoved (s.piles a) (chop (s.piles a).faceUp)
      else s.piles a') =
    (fun a' => if a' = a then
        Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
      else t.piles a') := by
  funext a'
  by_cases ha : a' = a
  · rw [ha, ite_eq_left rfl, ite_eq_left rfl, congrFun hp a]
  · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']

/-- The players' transfer of the `tabToTab` pile write: the located
removal and the placed run agree under piles equality. -/
private theorem piles_setPile_putRun_transfer {s t : State} {c : Card} {a : Anchor}
    {b : Base} (hp : s.piles = t.piles) :
    ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below c (s.piles a).faceUp))).putRun
      (fromCard c (s.piles a).faceUp) b).piles =
    ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below c (t.piles a).faceUp))).putRun
      (fromCard c (t.piles a).faceUp) b).piles := by
  have hpa : s.piles a = t.piles a := congrFun hp a
  have hset : (s.setPile a (Pile.afterRunRemoved (s.piles a) (below c (s.piles a).faceUp))).piles
      = (t.setPile a (Pile.afterRunRemoved (t.piles a) (below c (t.piles a).faceUp))).piles := by
    rw [setPile_piles_eq, setPile_piles_eq]
    funext a'
    by_cases ha : a' = a
    · rw [ha, ite_eq_left rfl, ite_eq_left rfl, hpa]
    · rw [ite_eq_right ha, ite_eq_right ha, congrFun hp a']
  have hrun : fromCard c (s.piles a).faceUp = fromCard c (t.piles a).faceUp := by
    rw [congrArg Pile.faceUp hpa]
  exact putRun_piles_congr hset hrun

/-- **The (A) replay.**  A winning play from `s` is replayed from the
twin `t` (same foundations, same piles, one card per draw, the same
presented cycle) by induction on the play.  Board moves fire verbatim
(their guards read piles and foundations only; the step shapes carry
the writes and the fields in lockstep).  A copied `draw` rotates both
cycles in lockstep (`draw_cycleOf`).  Before a consuming move the twin
either already sits on the same waste top — the top is the cycle's
last card, and the cycles agree — or starts from a full stock, where
draining the whole cycle (`drain_full`) brings the same card to hand
and restores the same cycle minus the consumed card.  The cycle lists
stay equal at every copied move, so the end state's foundations agree
and the twin wins. -/
private theorem draw1_replay : ∀ (π : List Move) (s t : State),
    s.drawStep = 1 → t.drawStep = 1 → s.found = t.found → s.piles = t.piles →
    cycleOf s = cycleOf t → ∀ w, s.run π = some w → w.isWin = true →
    ∃ π' w', t.run π' = some w' ∧ w'.isWin = true := by
  intro π
  induction π with
  | nil =>
      intro s t hds hdt hf hp hcy w hrun hwin
      refine ⟨[], t, rfl, ?_⟩
      have hisW : s.isWin = t.isWin := isWin_congr hf
      have hw : w = s := (Option.some.inj hrun).symm
      rw [hw, hisW] at hwin
      exact hwin
  | cons m rest ih =>
      intro s t hds hdt hf hp hcy w hrun hwin
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
      cases m with
      | draw =>
          have hsd : s.stepDraw = some s₁ := hstep
          have hscy : cycleOf s ≠ [] := draw_ne_of_fires hstep
          have htcy : cycleOf t ≠ [] := by rw [← hcy]; exact hscy
          obtain ⟨t₁, htstep⟩ := draw_step_fires hdt htcy
          have htd : t.stepDraw = some t₁ := htstep
          have hf1 : s₁.found = t₁.found := by
            rw [stepDraw_found hsd, stepDraw_found htd, hf]
          have hp1 : s₁.piles = t₁.piles := by
            rw [stepDraw_piles hsd, stepDraw_piles htd, hp]
          have hc1 : cycleOf s₁ = cycleOf t₁ := by
            rw [draw_cycleOf hds hstep, draw_cycleOf hdt htstep, hcy]
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ t₁ (by rw [stepDraw_keep_drawStep hsd, hds])
              (by rw [stepDraw_keep_drawStep htd, hdt]) hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.draw :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'
      | wasteToFound x =>
          obtain ⟨hg, ws, hwaste, hs1shape⟩ := step_wasteToFound_inv' hstep
          rw [Bool.and_eq_true] at hg
          obtain ⟨-, hnext⟩ := hg
          have hdsn : cycleOf s = (s.stock ++ ws.reverse) ++ [x] :=
            cycleOf_eq_snoc hwaste
          cases htw : t.waste with
          | cons y ys =>
              have hyx : y = x := waste_head_of_cycle hwaste htw hcy
              rw [hyx] at htw
              have hvwi : t.wasteIs x = true := by
                rw [State.wasteIs_cons htw x, decide_eq_true (rfl : x = x)]
              have hvnext : t.nextUp x = true := by
                rw [nextUp_congr x hf] at hnext
                exact hnext
              have htstep : State.step t (Move.wasteToFound x) = some
                  { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys } := by
                show (if t.wasteIs x && t.nextUp x then
                    match t.waste with
                    | _ :: ws₂ => some
                        { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvnext]; rfl), htw]
              have hf1 : s₁.found =
                  { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys }.found := by
                rw [hs1shape]
                exact found_append_transfer hf
              have hp1 : s₁.piles =
                  { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys }.piles := by
                rw [hs1shape]
                show s.piles = t.piles
                exact hp
              have hc1 : cycleOf s₁ =
                  cycleOf { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys } := by
                rw [hs1shape]
                show s.stock ++ ws.reverse = t.stock ++ ys.reverse
                apply snoc_tail_eq (x := x)
                rw [hdsn.symm,
                  show (t.stock ++ ys.reverse) ++ [x] = cycleOf t from
                    (cycleOf_eq_snoc htw).symm, hcy]
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { t.setFound x.suit (t.found x.suit ++ [x]) with waste := ys }
                  (by rw [hs1shape]; exact hds) hdt hf1 hp1 hc1 w hrest hwin
              refine ⟨Move.wasteToFound x :: π', w', ?_, hwin'⟩
              rw [run_step_cons htstep]
              exact hrun'
          | nil =>
              -- the full-stock twin: drain the whole cycle, then consume
              obtain ⟨vt, hvt⟩ : ∃ vt,
                  vt = { t with stock := [], waste := (cycleOf t).reverse } := ⟨_, rfl⟩
              have hdrain : t.run (List.replicate (cycleOf t).length Move.draw)
                  = some vt := by
                have hst : t.stock = cycleOf t := by
                  show t.stock = t.stock ++ t.waste.reverse
                  rw [htw, show ([] : List Card).reverse = [] from rfl, List.append_nil]
                have h0 := drain_full _ t (cycleOf t) hdt rfl hst
                rw [htw, List.take_length, List.append_nil, List.drop_length] at h0
                rw [← hvt] at h0
                exact h0
              have hd : cycleOf t = (s.stock ++ ws.reverse) ++ [x] := by
                rw [← hcy, hdsn]
              have hland : vt.waste = x :: (s.stock ++ ws.reverse).reverse := by
                rw [hvt]
                show (cycleOf t).reverse = _
                rw [hd, List.reverse_append]
                rfl
              have hvwi : vt.wasteIs x = true := by
                rw [State.wasteIs_cons hland x, decide_eq_true (rfl : x = x)]
              have hvtf : vt.found = t.found := by rw [hvt]
              have hvnext : vt.nextUp x = true := by
                rw [nextUp_congr x hvtf, nextUp_congr x hf.symm]
                exact hnext
              have htstep : State.step vt (Move.wasteToFound x) = some
                  { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse } := by
                show (if vt.wasteIs x && vt.nextUp x then
                    match vt.waste with
                    | _ :: ws₂ => some { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvnext]; rfl), hland]
              have hf1 : s₁.found = { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }.found := by
                rw [hs1shape, hvt]
                exact found_append_transfer hf
              have hp1 : s₁.piles = { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }.piles := by
                rw [hs1shape, hvt]
                show s.piles = t.piles
                exact hp
              have hc1 : cycleOf s₁ = cycleOf { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse } := by
                rw [hs1shape, hvt]
                show s.stock ++ ws.reverse
                    = (([] : List Card) ++ (s.stock ++ ws.reverse).reverse).reverse
                rw [List.nil_append, List.reverse_reverse]
              have hdst : { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }.drawStep = 1 := by
                rw [hvt]
                show t.drawStep = 1
                exact hdt
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { vt.setFound x.suit (vt.found x.suit ++ [x]) with waste := (s.stock ++ ws.reverse).reverse }
                  (by rw [hs1shape]; exact hds) hdst hf1 hp1 hc1 w hrest hwin
              refine ⟨List.replicate (cycleOf t).length Move.draw
                  ++ Move.wasteToFound x :: π', w', ?_, hwin'⟩
              rw [run_replicate_append _ t vt (Move.wasteToFound x :: π') hdrain,
                run_step_cons htstep]
              exact hrun'
      | wasteToTab x b =>
          obtain ⟨hg, ws, hwaste, hs1shape⟩ := step_wasteToTab_inv' hstep
          rw [Bool.and_eq_true] at hg
          obtain ⟨-, hcp⟩ := hg
          have hdsn : cycleOf s = (s.stock ++ ws.reverse) ++ [x] :=
            cycleOf_eq_snoc hwaste
          cases htw : t.waste with
          | cons y ys =>
              have hyx : y = x := waste_head_of_cycle hwaste htw hcy
              rw [hyx] at htw
              have hvwi : t.wasteIs x = true := by
                rw [State.wasteIs_cons htw x, decide_eq_true (rfl : x = x)]
              have hvcp : t.canPlace x b = true := by
                rw [canPlace_congr x b hp] at hcp
                exact hcp
              have htstep : State.step t (Move.wasteToTab x b) = some
                  { t.putCard x b with waste := ys } := by
                show (if t.wasteIs x && t.canPlace x b then
                    match t.waste with
                    | _ :: ws₂ => some { t.putCard x b with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvcp]; rfl), htw]
              have hf1 : s₁.found = { t.putCard x b with waste := ys }.found := by
                rw [hs1shape, putCard_found_keep, putCard_found_keep]
                exact hf
              have hp1 : s₁.piles = { t.putCard x b with waste := ys }.piles := by
                rw [hs1shape]
                exact putCard_piles_congr hp
              have hc1 : cycleOf s₁ = cycleOf { t.putCard x b with waste := ys } := by
                rw [hs1shape]
                show (s.putCard x b).stock ++ ws.reverse
                    = (t.putCard x b).stock ++ ys.reverse
                rw [show (s.putCard x b).stock = s.stock from (putCard_keep).2.1,
                    show (t.putCard x b).stock = t.stock from (putCard_keep).2.1]
                apply snoc_tail_eq (x := x)
                rw [hdsn.symm,
                  show (t.stock ++ ys.reverse) ++ [x] = cycleOf t from
                    (cycleOf_eq_snoc htw).symm, hcy]
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { t.putCard x b with waste := ys }
                  (by
                    rw [hs1shape]
                    show (s.putCard x b).drawStep = 1
                    rw [show (s.putCard x b).drawStep = s.drawStep from (putCard_keep).2.2.2]
                    exact hds)
                  (by
                    show (t.putCard x b).drawStep = 1
                    rw [show (t.putCard x b).drawStep = t.drawStep from (putCard_keep).2.2.2]
                    exact hdt) hf1 hp1 hc1 w hrest hwin
              refine ⟨Move.wasteToTab x b :: π', w', ?_, hwin'⟩
              rw [run_step_cons htstep]
              exact hrun'
          | nil =>
              -- the full-stock twin: drain the whole cycle, then consume
              obtain ⟨vt, hvt⟩ : ∃ vt,
                  vt = { t with stock := [], waste := (cycleOf t).reverse } := ⟨_, rfl⟩
              have hdrain : t.run (List.replicate (cycleOf t).length Move.draw)
                  = some vt := by
                have hst : t.stock = cycleOf t := by
                  show t.stock = t.stock ++ t.waste.reverse
                  rw [htw, show ([] : List Card).reverse = [] from rfl, List.append_nil]
                have h0 := drain_full _ t (cycleOf t) hdt rfl hst
                rw [htw, List.take_length, List.append_nil, List.drop_length] at h0
                rw [← hvt] at h0
                exact h0
              have hd : cycleOf t = (s.stock ++ ws.reverse) ++ [x] := by
                rw [← hcy, hdsn]
              have hland : vt.waste = x :: (s.stock ++ ws.reverse).reverse := by
                rw [hvt]
                show (cycleOf t).reverse = _
                rw [hd, List.reverse_append]
                rfl
              have hvwi : vt.wasteIs x = true := by
                rw [State.wasteIs_cons hland x, decide_eq_true (rfl : x = x)]
              have hvcp : vt.canPlace x b = true := by
                rw [canPlace_congr x b hp] at hcp
                rw [← canPlace_congr x b (by rw [hvt] : vt.piles = t.piles)] at hcp
                exact hcp
              have hvtf : vt.found = t.found := by rw [hvt]
              have hvtp : vt.piles = t.piles := by rw [hvt]
              have htstep : State.step vt (Move.wasteToTab x b) = some
                  { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse } := by
                show (if vt.wasteIs x && vt.canPlace x b then
                    match vt.waste with
                    | _ :: ws₂ => some { vt.putCard x b with waste := ws₂ }
                    | [] => none
                  else none) = _
                rw [ite_eq_left (by rw [hvwi, hvcp]; rfl), hland]
              have hf1 : s₁.found = { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }.found := by
                rw [hs1shape, putCard_found_keep, putCard_found_keep, hvtf]
                exact hf
              have hp1 : s₁.piles = { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }.piles := by
                rw [hs1shape]
                exact putCard_piles_congr (hp.trans hvtp.symm)
              have hdst1 : { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }.drawStep = 1 := by
                show (vt.putCard x b).drawStep = 1
                rw [show (vt.putCard x b).drawStep = vt.drawStep from (putCard_keep).2.2.2,
                    show vt.drawStep = t.drawStep from by rw [hvt]]
                exact hdt
              have hc1 : cycleOf s₁ = cycleOf { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse } := by
                rw [hs1shape]
                show (s.putCard x b).stock ++ ws.reverse
                    = (vt.putCard x b).stock ++ ((s.stock ++ ws.reverse).reverse).reverse
                rw [show (s.putCard x b).stock = s.stock from (putCard_keep).2.1,
                    show (vt.putCard x b).stock = vt.stock from (putCard_keep).2.1,
                    show vt.stock = ([] : List Card) from by rw [hvt],
                    List.nil_append, List.reverse_reverse]
              obtain ⟨π', w', hrun', hwin'⟩ :=
                ih s₁ { vt.putCard x b with waste := (s.stock ++ ws.reverse).reverse }
                  (by
                    rw [hs1shape]
                    show (s.putCard x b).drawStep = 1
                    rw [show (s.putCard x b).drawStep = s.drawStep from (putCard_keep).2.2.2]
                    exact hds) hdst1 hf1 hp1 hc1 w hrest hwin
              refine ⟨List.replicate (cycleOf t).length Move.draw
                  ++ Move.wasteToTab x b :: π', w', ?_, hwin'⟩
              rw [run_replicate_append _ t vt (Move.wasteToTab x b :: π') hdrain,
                run_step_cons htstep]
              exact hrun'
      | tabToFound x =>
          obtain ⟨hnext, a, hpa⟩ := tabToFound_fires hstep
          have hs1shape := tabToFound_shape hstep hpa
          have hvnext : t.nextUp x = true := by
            rw [nextUp_congr x hf] at hnext
            exact hnext
          have hvpa : t.pileOfTop x = some a := by
            rw [pileOfTop_congr x hp] at hpa
            exact hpa
          have htstep : State.step t (Move.tabToFound x) = some
              { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' } := by
            show (if t.nextUp x then
                match t.pileOfTop x with
                | none => none
                | some a' => some
                    { t.setFound x.suit (t.found x.suit ++ [x]) with
                      piles := fun a'' => if a'' = a' then
                          Pile.afterRunRemoved (t.piles a') (chop (t.piles a').faceUp)
                        else t.piles a'' }
                else none) = _
            rw [ite_eq_left hvnext, hvpa]
          have hf1 : s₁.found =
              { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' }.found := by
            rw [hs1shape]
            exact found_append_transfer hf
          have hp1 : s₁.piles =
              { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' }.piles := by
            rw [hs1shape]
            exact piles_afterRunRemoved_transfer hp
          have hc1 : cycleOf s₁ =
              cycleOf { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' } := by
            rw [hs1shape]
            show s.stock ++ s.waste.reverse = t.stock ++ t.waste.reverse
            exact hcy
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ { t.setFound x.suit (t.found x.suit ++ [x]) with
                piles := fun a' => if a' = a then
                    Pile.afterRunRemoved (t.piles a) (chop (t.piles a).faceUp)
                  else t.piles a' }
              (by rw [hs1shape]; exact hds) hdt hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.tabToFound x :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'
      | foundToTab x b =>
          obtain ⟨c', htop, hcc, hcp, hs1shape⟩ := step_foundToTab_inv' hstep
          have hvtop : t.foundTop x.suit = some c' := by
            rw [foundTop_congr x.suit hf] at htop
            exact htop
          have hvcp : t.canPlace x b = true := by
            rw [canPlace_congr x b hp] at hcp
            exact hcp
          have htstep : State.step t (Move.foundToTab x b) = some
              ((t.setFound x.suit (chop (t.found x.suit))).putCard x b) := by
            show (match t.foundTop x.suit with
                | some c₂ =>
                    if decide (c₂ = x) && t.canPlace x b then
                      some ((t.setFound x.suit (chop (t.found x.suit))).putCard x b)
                    else none
                | none => none) = _
            rw [hvtop]
            show ((if (decide (c' = x) && t.canPlace x b) = true then
                    some ((t.setFound x.suit (chop (t.found x.suit))).putCard x b)
                  else none)) = _
            rw [ite_eq_left (by rw [decide_eq_true hcc, hvcp]; rfl)]
          have hf1 : s₁.found =
              ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).found := by
            rw [hs1shape, putCard_found_keep, putCard_found_keep]
            exact found_chop_transfer hf
          have hp1 : s₁.piles =
              ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).piles := by
            rw [hs1shape]
            exact putCard_piles_congr hp
          have hc1 : cycleOf s₁ =
              cycleOf ((t.setFound x.suit (chop (t.found x.suit))).putCard x b) := by
            rw [hs1shape]
            show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).stock
                ++ ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).waste.reverse
                = ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).stock
                  ++ ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).waste.reverse
            rw [show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).stock
                    = s.stock from (putCard_keep).2.1,
                show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).waste
                    = s.waste from (putCard_keep).2.2.1,
                show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).stock
                    = t.stock from (putCard_keep).2.1,
                show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).waste
                    = t.waste from (putCard_keep).2.2.1]
            exact hcy
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ ((t.setFound x.suit (chop (t.found x.suit))).putCard x b)
              (by
                rw [hs1shape]
                show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).drawStep = 1
                rw [show ((s.setFound x.suit (chop (s.found x.suit))).putCard x b).drawStep
                        = s.drawStep from (putCard_keep).2.2.2]
                exact hds)
              (by
                show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).drawStep = 1
                rw [show ((t.setFound x.suit (chop (t.found x.suit))).putCard x b).drawStep
                        = t.drawStep from (putCard_keep).2.2.2]
                exact hdt) hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.foundToTab x b :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'
      | tabToTab x b =>
          obtain ⟨a, hhld, hcp, hne, hs1shape⟩ := step_tabToTab_inv' hstep
          have hvhld : t.pileHolding x = some a := by
            rw [pileHolding_congr hp] at hhld
            exact hhld
          have hvcp : t.canPlace x b = true := by
            rw [canPlace_congr x b hp] at hcp
            exact hcp
          have hfr : fromCard x (t.piles a).faceUp ≠ [] := by
            rw [show fromCard x (t.piles a).faceUp = fromCard x (s.piles a).faceUp from by
                rw [congrArg Pile.faceUp (congrFun hp a)]]
            exact hne
          have htstep : State.step t (Move.tabToTab x b) = some
              ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b) := by
            show (match t.pileHolding x with
                | none => none
                | some a' =>
                    if t.canPlace x b then
                      match fromCard x (t.piles a').faceUp with
                      | [] => none
                      | run => some
                          ((t.setPile a' (Pile.afterRunRemoved (t.piles a') (below x (t.piles a').faceUp))).putRun
                            run b)
                    else none) = _
            rw [hvhld]
            show ((if t.canPlace x b = true then
                    match fromCard x (t.piles a).faceUp with
                    | [] => none
                    | run => some
                        ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                          run b)
                  else none)) = _
            rw [ite_eq_left hvcp]
            cases hfx : fromCard x (t.piles a).faceUp with
            | nil =>
                rw [hfx] at hfr
                exact absurd hfr (by simp)
            | cons r1 r2 =>
                rfl
          have hf1 : s₁.found =
              ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b).found := by
            rw [hs1shape, putRun_found_keep, putRun_found_keep]
            exact hf
          have hp1 : s₁.piles =
              ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b).piles := by
            rw [hs1shape]
            exact piles_setPile_putRun_transfer hp
          have hc1 : cycleOf s₁ =
              cycleOf ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                (fromCard x (t.piles a).faceUp) b) := by
            rw [hs1shape]
            show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                    (fromCard x (s.piles a).faceUp) b).stock
                ++ ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                    (fromCard x (s.piles a).faceUp) b).waste.reverse
                = ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                    (fromCard x (t.piles a).faceUp) b).stock
                  ++ ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                    (fromCard x (t.piles a).faceUp) b).waste.reverse
            rw [show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                      (fromCard x (s.piles a).faceUp) b).stock
                    = s.stock from (putRun_keep).2.1,
                show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                      (fromCard x (s.piles a).faceUp) b).waste
                    = s.waste from (putRun_keep).2.2.1,
                show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                      (fromCard x (t.piles a).faceUp) b).stock
                    = t.stock from (putRun_keep).2.1,
                show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                      (fromCard x (t.piles a).faceUp) b).waste
                    = t.waste from (putRun_keep).2.2.1]
            exact hcy
          obtain ⟨π', w', hrun', hwin'⟩ :=
            ih s₁ ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
              (fromCard x (t.piles a).faceUp) b)
              (by
                rw [hs1shape]
                show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                    (fromCard x (s.piles a).faceUp) b).drawStep = 1
                rw [show ((s.setPile a (Pile.afterRunRemoved (s.piles a) (below x (s.piles a).faceUp))).putRun
                      (fromCard x (s.piles a).faceUp) b).drawStep
                        = s.drawStep from (putRun_keep).2.2.2]
                exact hds)
              (by
                show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                    (fromCard x (t.piles a).faceUp) b).drawStep = 1
                rw [show ((t.setPile a (Pile.afterRunRemoved (t.piles a) (below x (t.piles a).faceUp))).putRun
                      (fromCard x (t.piles a).faceUp) b).drawStep
                        = t.drawStep from (putRun_keep).2.2.2]
                exact hdt) hf1 hp1 hc1 w hrest hwin
          refine ⟨Move.tabToTab x b :: π', w', ?_, hwin'⟩
          rw [run_step_cons htstep]
          exact hrun'

/-- **(A) The stock-as-reserve lemma, physical form** (B&G §5.4.1's
exception, draw-1): sameCycle twins are the same verdict.

Route (PROVEN, the replay refinement of the Klondike mirror
`draw1_cursor_solvable`): an induction on the winning play, replayed
from the twin under the four-field invariant (equal foundations,
equal piles, step one, equal `cycleOf` — the sameCycle fields plus the
cycled phase).  Board moves fire verbatim — no move but `draw` and the
waste consumers reads the stock or waste, and the guards are
found/piles reads, so the successors' fields transfer through the step
shapes.  A copied `draw` rotates both cycles in lockstep
(`draw_cycleOf`: the phase, how far the cycle has been dealt, is
invisible to the presentation).  A consuming `wasteTo*` fires
directly whenever the twin's waste is nonempty — the waste top is the
presented cycle's last card, and the cycles agree — and from a
full-stock twin after splicing `drain_full`: draining the whole cycle
deals its last card out to hand and restores the same cycle, after
which the consumption leaves both threads on the same stripped cycle.
Foundation transfers close the invariant at every step; `isWin` reads
found only, so the twin's replayed play wins. -/
theorem draw1_sameCycle_sameFate {st st' : State}
    (h1 : st.drawStep = 1) (h2 : st'.drawStep = 1)
    (hsc : sameCycle st st') : sameFate st st' := by
  obtain ⟨hfd, hpl, hds, hcy⟩ := hsc
  refine ⟨fun hwin => ?_, fun hwin => ?_⟩
  · obtain ⟨π, w, hrun, hisw⟩ := hwin
    exact draw1_replay π st st' h1 h2 hfd hpl hcy w hrun hisw
  · obtain ⟨π, w, hrun, hisw⟩ := hwin
    exact draw1_replay π st' st h2 h1 hfd.symm hpl.symm hcy.symm w hrun hisw

/-! ### (B)'s assembly — the canonical front

The front `FrontOK c u s'` names the CANONICAL front-load (the
deal-out-and-stack the theorem promises): the stock form deals `c`
out of its stock position, the waste form drains, recycles, and
deals `c` back to hand.  Because the front is canonical, its POSITION
data transfers move-by-move through a complying play, and the
replay's squares below exchange each legal head against it. -/

/-- The stock is one census zone.  (Dedup-marked against
`Orig/Encode.lean`'s public `stock_mem_zones` — not in this chapter's
import closure.) -/
private theorem stock_zone (st : State) : st.stock ∈ st.zones := by
  rw [show st.zones = (Suit.all.map st.found
        ++ Anchor.all.map (fun a => (st.piles a).hidden ++ (st.piles a).faceUp))
      ++ [st.stock, st.waste] from rfl]
  simp

/-- The waste is one census zone.  (Dedup-marked against
`Orig/Encode.lean`'s public `waste_mem_zones`.) -/
private theorem waste_zone (st : State) : st.waste ∈ st.zones := by
  rw [show st.zones = (Suit.all.map st.found
        ++ Anchor.all.map (fun a => (st.piles a).hidden ++ (st.piles a).faceUp))
      ++ [st.stock, st.waste] from rfl]
  simp

/-- A `WF` census zone holds every card at most once: any split of
the zone with the card in both halves contradicts the census.  (The
in-zone half of the conservation the cross-zone `mem_*_unique`
family does not cover; rides `count_filter_pos`.) -/
private theorem zone_two_hits_ne {st : State} (hwf : st.WF) {z l₁ l₂ : List Card}
    {c : Card} (hz : z ∈ st.zones)
    (hsplit : z = l₁ ++ l₂) (h1 : c ∈ l₁) (h2 : c ∈ l₂) : False := by
  have htwo : 2 ≤ (z.filter fun x => decide (x = c)).length := by
    rw [hsplit, List.filter_append, List.length_append]
    have ha1 := count_filter_pos (l := l₁) h1
    have ha2 := count_filter_pos (l := l₂) h2
    omega
  obtain ⟨A, B, hzAB⟩ := mem_infix_split st.zones z hz
  have hflat2 : st.zones.flatMap id = A.flatMap id ++ (z ++ B.flatMap id) := by
    rw [hzAB, List.flatMap_append]
    rfl
  have hcap : (z.filter fun x => decide (x = c)).length ≤ st.cardCount c := by
    rw [show st.cardCount c =
          ((st.zones.flatMap id).filter fun x => decide (x = c)).length from rfl,
      hflat2, List.filter_append, List.length_append, List.filter_append,
      List.length_append]
    omega
  have hone : st.cardCount c = 1 := hwf.2.2.1 c (Card.mem_universe c)
  omega

/-- Two cards of one suit cannot share the rung.  (A sibling of the
(C) engine's private `sameRung_eq` below — the (B) block precedes it;
dedup-marked.) -/
private theorem nextUp_pair_eq {st : State} {a b : Card} (ha : st.nextUp a = true)
    (hb : st.nextUp b = true) (hs : a.suit = b.suit) : a = b := by
  have h1 : a.rank.toIdx = st.foundHeight a.suit := of_decide_eq_true ha
  have h2 : b.rank.toIdx = st.foundHeight b.suit := of_decide_eq_true hb
  rcases a with ⟨as, ar⟩
  rcases b with ⟨bs, br⟩
  have hss : as = bs := hs
  have hrr : ar = br := Rank.toIdx_inj (by rw [h1, h2, hss])
  rw [hrr, hss]

/-- The head split: a list that splits at `c` with `c` not below the
prefix splits with the prefix empty when `c` is the head. -/
private theorem split_head {l preW postW : List Card} {c : Card}
    (h : c :: l = preW ++ c :: postW) (hn : c ∉ preW) : preW = [] ∧ postW = l := by
  cases preW with
  | nil =>
      injection h with _ htl
      exact ⟨rfl, htl.symm⟩
  | cons z zs =>
      exfalso
      injection h with hz htl
      rw [← hz] at hn
      exact hn (List.mem_cons_self ..)

/-- The canonical front-load's outcome, the induction's carried form:
the stock form fronts `c` from its stock position (data: `|pre|` cards
above it, the split's first occurrence), the waste form from its
waste position.  Either way the play is pure draws and the one stack,
landing `s'`. -/
private def FrontOK (c : Card) (u s' : State) : Prop :=
  (∃ pre post, u.stock = pre ++ c :: post ∧ c ∉ pre ∧
      u.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) = some s')
    ∨ (∃ preW postW, u.waste = preW ++ c :: postW ∧ c ∉ preW ∧
      u.run (List.replicate (u.stock.length + postW.length + 1) Move.draw
          ++ [Move.wasteToFound c]) = some s')

/-- The nil corner: a winning EMPTY play contradicts the rung — the
win caps every foundation at 13 while the rung pins `c`'s index at
that very height, and no index reaches 13.  WF-free. -/
private theorem front_nil {u : State} {c : Card} {w : State}
    (hrung : u.nextUp c = true) (hrun : u.run ([] : List Move) = some w)
    (hwin : w.isWin = true) : False := by
  have hw : (some u : Option State) = some w := hrun
  injection hw with hwst
  rw [← hwst] at hwin
  have h13 := isWin_len c.suit hwin
  have hidx : c.rank.toIdx = (u.found c.suit).length := of_decide_eq_true hrung
  have hlt : c.rank.toIdx < 13 := Rank.toIdx_lt c.rank
  omega

/-- The `wasteToFound c` exit: `c` sits at the waste top, so the
front's waste form IS pristine — the landing is exactly the successor
the play itself took, and the tail wins verbatim. -/
private theorem front_exit_wtf {u s₁ : State} {c : Card} {w : State}
    {rest : List Move}
    (hds : u.drawStep = 1) (hrung : u.nextUp c = true)
    (hstep : State.step u (Move.wasteToFound c) = some s₁)
    (hrest : s₁.run rest = some w) (hwin : w.isWin = true) :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨-, hng, ws, hwastee, hs₁⟩ := wasteToFound_fires hstep
  have hfront := front_waste (s := u) (c := c) (preW := []) (postW := ws) hds hrung
    (by rw [hwastee]; rfl)
  refine ⟨raisedMid u ws c, Or.inr ⟨[], ws, by rw [hwastee]; rfl, by simp, ?_⟩,
    ⟨rest, w, ?_, hwin⟩⟩
  · -- the front play lands the raised mid by the engine literal
    rw [hfront]
    rfl
  · have hseq : raisedMid u ws c = s₁ := by
      rw [hs₁]
      rfl
    rw [hseq]
    exact hrest

/-- The `wasteToTab c b` exit: the front ends at the raised mid, and
the worry-back identity lowers the park onto the same successor the
play itself took — the tail wins verbatim. -/
private theorem front_exit_wtt {u s₁ : State} {c : Card} {b : Base} {w : State}
    {rest : List Move}
    (hds : u.drawStep = 1) (hrung : u.nextUp c = true)
    (hstep : State.step u (Move.wasteToTab c b) = some s₁)
    (hrest : s₁.run rest = some w) (hwin : w.isWin = true) :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨-, -, ws, hwastee, hs₁⟩ := wasteToTab_fires hstep
  have hfront := front_waste (s := u) (c := c) (preW := []) (postW := ws) hds hrung
    (by rw [hwastee]; rfl)
  have hmid : State.mk (fun s' => if s' = c.suit then u.found c.suit ++ [c] else u.found s')
      u.piles (([] : List Card).reverse ++ u.stock) ws u.drawStep
      = raisedMid u ws c := rfl
  have hlow : State.step (raisedMid u ws c) (Move.foundToTab c b) = some s₁ :=
    lower_foundToTab1 hwastee hstep
  refine ⟨raisedMid u ws c, Or.inr ⟨[], ws, by rw [hwastee]; rfl, by simp, ?_⟩,
    ⟨Move.foundToTab c b :: rest, w, ?_, hwin⟩⟩
  · rw [hfront, hmid]
  · rw [run_step_cons hlow]
    exact hrest

/-! #### The absorb case engine -/

/-- **The draw-absorb engine.**  One drawing head move rides in front
of the canonical front: whatever the draw dealt, the front from `u`
is the front from `s₁` with the one draw prepended (the dealt card
sits above `c` in `u`'s cycle), or — when the draw deals `c` itself —
the pristine front from `s₁` IS `u`'s stock front, one draw and the
stack, and the two landings coincide (the engine's landing literal
is `raisedMid`). -/
private theorem front_draw {u s₁ : State} {c : Card} {s' : State}
    (hwfu : u.WF) (hwf : s₁.WF) (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hstep : State.step u Move.draw = some s₁)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  -- the draw reads no found and keeps the rung
  have hs1f : s₁.found = u.found := stepDraw_found (show u.stepDraw = some s₁ from hstep)
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hs1f]
    exact hrungU
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  cases hus : u.stock with
  | cons a cs =>
      -- the plain deal
      have hs1shape : s₁ = { u with stock := cs, waste := a :: u.waste } := by
        have hsh := draw_shape_plain hds hus
        exact (Option.some.inj (hsh.symm.trans hstep)).symm
      by_cases hac : a = c
      · rw [hac] at hus hs1shape
        -- the dealt card IS c: the stock front at s₁ would double-book
        -- c against the waste head; the waste front is pristine
        rcases hfront₁ with ⟨pre₁, post₁, hs1stock, hcpre, hplay⟩ | ⟨preW₁, postW₁, hs1waste, hcpre, hplay⟩
        · exfalso
          have hmem1 : c ∈ s₁.stock := by
            rw [hs1stock]
            exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
          have hmem2 : c ∈ s₁.waste := by rw [hs1shape]; exact List.mem_cons_self ..
          exact (mem_stock_unique hwf hmem1).2.1 hmem2
        · -- pristine forced: c is the waste top
          have hs1w2 : s₁.waste = c :: u.waste := by rw [hs1shape]; try rfl
          obtain ⟨-, hpostW⟩ := split_head (hs1w2.symm.trans hs1waste) hcpre
          rw [hpostW] at hplay
          -- the engine at s₁ pins s' to the raised mid
          have heng := front_waste (s := s₁) (c := c) (preW := ([] : List Card))
            (postW := u.waste) hds1 hn1 (by rw [hs1w2]; rfl)
          have hs'lit : s' = State.mk (fun s' => if s' = c.suit then s₁.found c.suit ++ [c] else s₁.found s')
              s₁.piles (([] : List Card).reverse ++ s₁.stock) u.waste s₁.drawStep :=
            Option.some.inj (hplay.symm.trans heng)
          have hs'M : raisedMid s₁ u.waste c = s' := by rw [hs'lit]; rfl
          refine ⟨raisedMid s₁ u.waste c,
            Or.inl ⟨[], cs, by rw [hus]; rfl, by simp, ?_⟩, ?_⟩
          · rw [show List.replicate (([] : List Card).length + 1) Move.draw
                ++ [Move.wasteToFound c] = Move.draw :: [Move.wasteToFound c] from rfl,
              run_draw_cons1 hstep,
              run_one1 (wtf_step_raised (show s₁.waste = c :: u.waste from hs1w2) hn1)]
          · rw [hs'M]
            exact hwin₁
      · -- a ≠ c: both fronts prepend the dealt card above c
        rcases hfront₁ with ⟨pre₁, post₁, hs1stock, hcpre, hplay⟩ | ⟨preW₁, postW₁, hs1waste, hcpre, hplay⟩
        · -- the stock data rides the dealt a above it
          have hdata : (a :: pre₁) ++ c :: post₁ = u.stock := by
            rw [hus]
            show (a :: pre₁) ++ c :: post₁ = a :: cs
            rw [show cs = s₁.stock from by rw [hs1shape], hs1stock]
            exact List.cons_append
          have hcpreu : c ∉ a :: pre₁ := by
            intro hcon
            rcases List.mem_cons.1 hcon with heq | hmem
            · exact hac heq.symm
            · exact hcpre hmem
          have hpreend : u.run
              (List.replicate ((a :: pre₁).length + 1) Move.draw ++ [Move.wasteToFound c])
              = s₁.run (List.replicate (pre₁.length + 1) Move.draw ++ [Move.wasteToFound c]) := by
            rw [show (a :: pre₁).length + 1 = (pre₁.length + 1) + 1 from rfl,
              show List.replicate ((pre₁.length + 1) + 1) Move.draw
                  ++ [Move.wasteToFound c]
                  = Move.draw :: (List.replicate (pre₁.length + 1) Move.draw
                      ++ [Move.wasteToFound c]) from rfl,
              run_draw_cons1 hstep]
          refine ⟨s', Or.inl ⟨a :: pre₁, post₁, hdata.symm, hcpreu, ?_⟩, hwin₁⟩
          · rw [hpreend]
            exact hplay
        · -- the waste data: the dealt a rode above c in s₁'s waste
          have hs1w2 : s₁.waste = a :: u.waste := by rw [hs1shape]; try rfl
          cases hpre : preW₁ with
          | nil =>
              exfalso
              rw [hpre] at hs1waste
              rw [hs1waste] at hs1w2
              injection hs1w2 with hhead _
              exact hac hhead.symm
          | cons z zs =>
              -- the head IS the dealt card; the tail IS u.waste
              have hz : z = a := by
                have h6 := hs1w2
                rw [hs1waste, hpre, List.cons_append] at h6
                injection h6 with hhead htl
                try exact hhead
              have huw0 : u.waste = zs ++ c :: postW₁ := by
                have h6 := hs1w2
                rw [hs1waste, hpre, List.cons_append, ← hz] at h6
                injection h6 with hhead htl
                try exact htl.symm
              rw [hpre] at hcpre
              have hcprew : c ∉ zs := by
                intro hcon
                exact hcpre (List.mem_cons.2 (Or.inr hcon))
              have hsl : u.stock.length = s₁.stock.length + 1 := by
                rw [hus]
                show (a :: cs).length = s₁.stock.length + 1
                rw [show s₁.stock = cs from by rw [hs1shape]]
                rfl
              have hpreend2 : u.run
                  (List.replicate (u.stock.length + postW₁.length + 1) Move.draw
                    ++ [Move.wasteToFound c])
                  = s₁.run (List.replicate (s₁.stock.length + postW₁.length + 1) Move.draw
                    ++ [Move.wasteToFound c]) := by
                rw [hsl,
                  show s₁.stock.length + 1 + postW₁.length + 1
                      = (s₁.stock.length + postW₁.length + 1) + 1 from by omega,
                  show List.replicate ((s₁.stock.length + postW₁.length + 1) + 1) Move.draw
                    ++ [Move.wasteToFound c]
                    = Move.draw :: (List.replicate (s₁.stock.length + postW₁.length + 1) Move.draw
                        ++ [Move.wasteToFound c]) from rfl,
                  run_draw_cons1 hstep]
              refine ⟨s', Or.inr ⟨zs, postW₁, huw0, hcprew, ?_⟩, hwin₁⟩
              · rw [hpreend2]
                exact hplay
  | nil =>
      -- the pass-end recycle-deal
      cases hwr : u.waste.reverse with
      | nil =>
          exfalso
          have hcy := draw_ne_of_fires hstep
          rw [show cycleOf u = u.stock ++ u.waste.reverse from rfl, hus, hwr] at hcy
          exact hcy (by rfl)
      | cons b bs =>
          have hs1shapeB : s₁ = { u with stock := bs, waste := [b] } := by
            have hsh := draw_shape_base hds hus hwr
            exact (Option.some.inj (hsh.symm.trans hstep)).symm
          -- u.waste, spine-restored
          have huwr : u.waste = bs.reverse ++ [b] := by
            rw [show u.waste = (u.waste.reverse).reverse from (List.reverse_reverse u.waste).symm,
              hwr, List.reverse_cons]
          by_cases hbc : b = c
          · rw [hbc] at hs1shapeB huwr
            -- the recycled card IS c: stock front double-books; waste front pristine
            rcases hfront₁ with ⟨pre₁, post₁, hs1stock, hcpre, hplay⟩ | ⟨preW₁, postW₁, hs1waste, hcpre, hplay⟩
            · exfalso
              have hmem1 : c ∈ s₁.stock := by
                rw [hs1stock]
                exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
              have hmem2 : c ∈ s₁.waste := by rw [hs1shapeB]; exact List.mem_cons_self ..
              exact (mem_stock_unique hwf hmem1).2.1 hmem2
            · -- pristine forced: c is the whole waste
              have hs1w2 : s₁.waste = [c] := by rw [hs1shapeB]; try rfl
              obtain ⟨hpre0, hpostW0⟩ := split_head (hs1w2.symm.trans hs1waste) hcpre
              rw [hpre0] at hs1waste
              rw [hpostW0] at hs1waste
              rw [hpostW0] at hplay
              -- c ∉ bs.reverse: twice-in-waste would breach the census
              have hcbr : c ∉ bs.reverse := by
                intro hcon
                have h1 : c ∈ bs.reverse := hcon
                have h2 : c ∈ [c] := List.mem_cons_self ..
                exact zone_two_hits_ne hwfu (waste_zone u) huwr h1 h2
              have heng := front_waste (s := s₁) (c := c) (preW := ([] : List Card))
                (postW := ([] : List Card)) hds1 hn1
                (show s₁.waste = [] ++ c :: ([] : List Card) from hs1waste)
              have hs'lit : s' = State.mk (fun s' => if s' = c.suit then s₁.found c.suit ++ [c] else s₁.found s')
                  s₁.piles (([] : List Card).reverse ++ s₁.stock)
                  ([] : List Card) s₁.drawStep :=
                Option.some.inj (hplay.symm.trans heng)
              have hs'M : raisedMid s₁ ([] : List Card) c = s' := by rw [hs'lit]; rfl
              refine ⟨raisedMid s₁ ([] : List Card) c,
                Or.inr ⟨bs.reverse, ([] : List Card), huwr, hcbr, ?_⟩, ?_⟩
              · rw [hus,
                  show List.replicate (([] : List Card).length + ([] : List Card).length + 1) Move.draw
                    ++ [Move.wasteToFound c] = Move.draw :: [Move.wasteToFound c] from rfl,
                  run_draw_cons1 hstep,
                  run_one1 (wtf_step_raised (show s₁.waste = c :: ([] : List Card) from hs1w2) hn1)]
              · rw [hs'M]
                exact hwin₁
          · -- b ≠ c: the recycled card rides its own spine; both arms prepend
            rcases hfront₁ with ⟨pre₁, post₁, hs1stock, hcpre, hplay⟩ | ⟨preW₁, postW₁, hs1waste, hcpre, hplay⟩
            · -- the stock front's split, reversed onto the treated spine
              have hbs : bs = pre₁ ++ c :: post₁ := by
                rw [show bs = s₁.stock from by rw [hs1shapeB], hs1stock]
              have hbsr : bs.reverse = post₁.reverse ++ c :: pre₁.reverse := by
                rw [hbs]
                show (pre₁ ++ c :: post₁).reverse = post₁.reverse ++ c :: pre₁.reverse
                rw [List.reverse_append, List.reverse_cons, List.append_assoc]
                try rfl
              -- u.waste on the reversed spine
              have huw2 : u.waste = post₁.reverse ++ c :: (pre₁.reverse ++ [b]) := by
                rw [huwr, hbsr, List.append_assoc]
                try rfl
              -- c ∉ post₁: twice-in-stock at s₁ would breach the census
              have hcno : c ∉ post₁ := by
                intro hcon
                exact zone_two_hits_ne hwf (stock_zone s₁)
                  (show s₁.stock = (pre₁ ++ [c]) ++ post₁ from by
                    rw [hs1stock, List.append_assoc]
                    try rfl)
                  (List.mem_append.2 (Or.inr (List.mem_cons_self ..))) hcon
              have hcnor : c ∉ post₁.reverse := by
                intro hcon
                rw [List.mem_reverse] at hcon
                exact hcno hcon
              have hccl : u.stock.length + (pre₁.reverse ++ [b]).length + 1
                    = (pre₁.length + 1) + 1 := by
                  rw [hus, List.length_append, List.length_reverse,
                    show ([] : List Card).length = 0 from rfl,
                    show [b].length = 1 from rfl]
                  omega
              have hpreend3 : u.run
                  (List.replicate (u.stock.length + (pre₁.reverse ++ [b]).length + 1) Move.draw
                    ++ [Move.wasteToFound c])
                  = s₁.run (List.replicate (pre₁.length + 1) Move.draw ++ [Move.wasteToFound c]) := by
                rw [hccl,
                  show List.replicate ((pre₁.length + 1) + 1) Move.draw
                    ++ [Move.wasteToFound c]
                    = Move.draw :: (List.replicate (pre₁.length + 1) Move.draw
                        ++ [Move.wasteToFound c]) from rfl,
                  run_draw_cons1 hstep]
              refine ⟨s', Or.inr ⟨post₁.reverse, pre₁.reverse ++ [b], huw2, hcnor, ?_⟩, hwin₁⟩
              · rw [hpreend3]
                exact hplay
            · -- the waste front at s₁ would park c on [b] with b ≠ c
              exfalso
              have hmem1 : c ∈ s₁.waste := by
                rw [hs1waste]
                exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
              rw [hs1shapeB] at hmem1
              rcases List.mem_cons.1 hmem1 with heq | hmem
              · exact hbc heq.symm
              · exact absurd hmem (by simp)

/-! #### The board-move squares -/

/-- A `setFound` write's found field depends only on the base's found
and the written list. -/
private theorem setFound_found_congr {A B : State} {σ : Suit} {l₁ l₂ : List Card}
    (hf : A.found = B.found) (hl : l₁ = l₂) :
    (A.setFound σ l₁).found = (B.setFound σ l₂).found := by
  rw [setFound_found_eq, setFound_found_eq]
  funext s'
  by_cases hs : s' = σ
  · rw [ite_eq_left hs, ite_eq_left hs, hl]
  · rw [ite_eq_right hs, ite_eq_right hs, congrFun hf s']

/-- Double bumps commute at the found field (the record-level
restatement of `bump2_comm`, so the squares can transport through
composed `setFound`s). -/
private theorem double_bump_comm {B : State} {x c : Card}
    (hne : x.suit ≠ c.suit) :
    ((B.setFound c.suit (B.found c.suit ++ [c])).setFound x.suit
        ((B.setFound c.suit (B.found c.suit ++ [c])).found x.suit ++ [x])).found
    = ((B.setFound x.suit (B.found x.suit ++ [x])).setFound c.suit
        ((B.setFound x.suit (B.found x.suit ++ [x])).found c.suit ++ [c])).found := by
  have h1 : ((B.setFound c.suit (B.found c.suit ++ [c])).found) x.suit
      = B.found x.suit := by
    show (if x.suit = c.suit then B.found c.suit ++ [c] else B.found x.suit) = B.found x.suit
    rw [ite_eq_right hne]
  have h2 : ((B.setFound x.suit (B.found x.suit ++ [x])).found) c.suit
      = B.found c.suit := by
    show (if c.suit = x.suit then B.found x.suit ++ [x] else B.found c.suit) = B.found c.suit
    rw [ite_eq_right (Ne.symm hne)]
  rw [h1, h2]
  exact congrArg State.found (setFound_comm (Ne.symm hne))

/-- The stock front's landing, field by field. -/
private theorem front_stock_shape {s : State} {c : Card} {pre post : List Card}
    (hd : s.drawStep = 1) (hng : s.nextUp c = true)
    (hs : s.stock = pre ++ c :: post) (s' : State)
    (h : s.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) = some s') :
    s'.found = (fun σ => if σ = c.suit then s.found c.suit ++ [c] else s.found σ) ∧
      s'.piles = s.piles ∧ s'.stock = post ∧
      s'.waste = pre.reverse ++ s.waste ∧ s'.drawStep = s.drawStep := by
  have hlit := front_stock hd hng hs
  have he : s' = State.mk (fun s' => if s' = c.suit then s.found c.suit ++ [c] else s.found s')
      s.piles post (pre.reverse ++ s.waste) s.drawStep :=
    Option.some.inj (h.symm.trans hlit)
  rw [he]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The waste front's landing, field by field. -/
private theorem front_waste_shape {s : State} {c : Card} {preW postW : List Card}
    (hd : s.drawStep = 1) (hng : s.nextUp c = true)
    (hw : s.waste = preW ++ c :: postW) (s' : State)
    (h : s.run (List.replicate (s.stock.length + postW.length + 1) Move.draw
        ++ [Move.wasteToFound c]) = some s') :
    s'.found = (fun σ => if σ = c.suit then s.found c.suit ++ [c] else s.found σ) ∧
      s'.piles = s.piles ∧ s'.stock = preW.reverse ++ s.stock ∧
      s'.waste = postW ∧ s'.drawStep = s.drawStep := by
  have hlit := front_waste hd hng hw
  have he : s' = State.mk (fun s' => if s' = c.suit then s.found c.suit ++ [c] else s.found s')
      s.piles (preW.reverse ++ s.stock) postW s.drawStep :=
    Option.some.inj (h.symm.trans hlit)
  rw [he]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The firing equation of a live `tabToFound` (a derived wrapper over
Play's raw `step_tabToFound_eq`, the wave-3b public home — the card's
original private firing dialect, dedup-marked for the census; hosted
here, before the engine strip that speaks it). -/
private theorem tabToFound_fires_eq {st : State} {y : Card} {ky : Anchor}
    (hny : st.nextUp y = true)
    (hstky : st.pileOfTop y = some ky) :
    State.step st (Move.tabToFound y) =
      some { st.setFound y.suit (st.found y.suit ++ [y]) with
        piles := fun a' => if a' = ky then
            Pile.afterRunRemoved (st.piles ky) (chop (st.piles ky).faceUp)
          else st.piles a' } := by
  rw [step_tabToFound_eq, hny, hstky]
  rfl

/-- The firing equation of a live `foundToTab` (a derived wrapper over
Play's raw `step_foundToTab_eq` — same story, same home). -/
private theorem foundToTab_fires_eq {st : State} {c : Card} {b : Base}
    (htopr : st.foundTop c.suit = some c)
    (hcpr : st.canPlace c b = true) :
    State.step st (Move.foundToTab c b) =
      some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) := by
  rw [step_foundToTab_eq, htopr]
  simp only [hcpr]
  rfl

/-- **The `tabToFound` square.**  A raise of a foreign-suit card rides
across the front: the move is cycle-blind (the front's data is
verbatim), the front from `u` lands the twin whose OWN raise is
exactly the `s₁`-side front's landing (the double bumps commute, the
pile write transfers), and the moved play wins from `u`'s landing. -/
private theorem front_board_tf {u s₁ : State} {c x : Card} {s' : State}
    (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hxs : x.suit ≠ c.suit)
    (hstep : State.step u (Move.tabToFound x) = some s₁)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨hnext, a, hpo⟩ := tabToFound_fires hstep
  have hs₁ := tabToFound_shape hstep hpo
  -- the move is cycle-blind: stock and waste ride verbatim
  have hstock : s₁.stock = u.stock := by rw [hs₁]; rfl
  have hwaste : s₁.waste = u.waste := by rw [hs₁]; rfl
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hs₁]
    show decide (c.rank.toIdx =
        ((u.setFound x.suit (u.found x.suit ++ [x])).found c.suit).length) = true
    rw [setFound_found_ne (Ne.symm hxs)]
    exact hrungU
  obtain ⟨ρ, w₂, hrunρ, hwinρ⟩ := hwin₁
  rcases hfront₁ with ⟨pre, post, hs1stock, hcpre, hplay⟩ | ⟨preW, postW, hs1waste, hcpre, hplay⟩
  · -- the stock form at both ends
    obtain ⟨V, hVrun⟩ : ∃ V,
        u.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_stock hds hrungU (hstock.symm.trans hs1stock)⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_stock_shape hds hrungU (hstock.symm.trans hs1stock) V hVrun
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_stock_shape hds1 hn1 hs1stock s' hplay
    refine ⟨V, Or.inl ⟨pre, post, hstock.symm.trans hs1stock, hcpre, hVrun⟩, ?_⟩
    refine ⟨Move.tabToFound x :: ρ, w₂, ?_, hwinρ⟩
    -- the raise fires at the u-side landing by the readers
    have hnextV : V.nextUp x = true := by
      show decide (x.rank.toIdx = (V.found x.suit).length) = true
      rw [hVf]
      show decide (x.rank.toIdx =
          (if x.suit = c.suit then u.found c.suit ++ [c] else u.found x.suit).length) = true
      rw [ite_eq_right hxs]
      exact hnext
    have hpoV : V.pileOfTop x = some a := by
      rw [pileOfTop_congr x hVp]
      exact hpo
    have hstepV := tabToFound_fires_eq hnextV hpoV
    -- found-field facts
    have hVfc : V.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hVf]; try rfl
    have hVfx : V.found x.suit
        = (u.setFound c.suit (u.found c.suit ++ [c])).found x.suit := by
      rw [hVf]; try rfl
    have hs1fc : s₁.found = (u.setFound x.suit (u.found x.suit ++ [x])).found := by
      rw [hs₁]; try rfl
    have hsfcx : s₁.found c.suit
        = (u.setFound x.suit (u.found x.suit ++ [x])).found c.suit := by
      rw [hs₁]; try rfl
    -- the raise's landing is the s₁-side front's landing
    have hLand : {V.setFound x.suit (V.found x.suit ++ [x])
        with
        piles := fun a' => if a' = a then
            Pile.afterRunRemoved (V.piles a) (chop (V.piles a).faceUp)
          else V.piles a' } = s' := by
      apply State.ext
      · -- found: the double bumps commute across the two bases
        show (V.setFound x.suit (V.found x.suit ++ [x])).found = s'.found
        have hfL : (V.setFound x.suit (V.found x.suit ++ [x])).found
            = ((u.setFound c.suit (u.found c.suit ++ [c])).setFound x.suit
                ((u.setFound c.suit (u.found c.suit ++ [c])).found x.suit ++ [x])).found :=
          setFound_found_congr hVfc (congrArg (fun l => l ++ [x]) hVfx)
        have hfR : (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found
            = ((u.setFound x.suit (u.found x.suit ++ [x])).setFound c.suit
                ((u.setFound x.suit (u.found x.suit ++ [x])).found c.suit ++ [c])).found :=
          setFound_found_congr hs1fc (congrArg (fun l => l ++ [c]) hsfcx)
        have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
          rw [hSf]; try rfl
        exact hfL.trans ((double_bump_comm hxs).trans (hfR.symm.trans hsF.symm))
      · -- piles: the write transfers through the equal piles
        show (fun a' => if a' = a then
            Pile.afterRunRemoved (V.piles a) (chop (V.piles a).faceUp)
          else V.piles a') = s'.piles
        rw [hVp, hSp]
        rw [hs₁]
        try rfl
      · show V.stock = s'.stock
        rw [hVs, hSs]
      · show V.waste = s'.waste
        rw [hVw, hSw, hwaste]
      · show V.drawStep = s'.drawStep
        rw [hVds, hSds, hds1, hds]
    rw [run_step_cons hstepV, hLand]
    exact hrunρ
  · -- the waste form: the same exchange through the waste engine
    obtain ⟨V, hVrun⟩ : ∃ V,
        u.run (List.replicate (u.stock.length + postW.length + 1) Move.draw
          ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_waste hds hrungU (hwaste.symm.trans hs1waste)⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_waste_shape hds hrungU (hwaste.symm.trans hs1waste) V hVrun
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_waste_shape hds1 hn1 hs1waste s' hplay
    refine ⟨V, Or.inr ⟨preW, postW, hwaste.symm.trans hs1waste, hcpre, hVrun⟩, ?_⟩
    refine ⟨Move.tabToFound x :: ρ, w₂, ?_, hwinρ⟩
    -- the raise fires at the u-side landing by the readers
    have hnextV : V.nextUp x = true := by
      show decide (x.rank.toIdx = (V.found x.suit).length) = true
      rw [hVf]
      show decide (x.rank.toIdx =
          (if x.suit = c.suit then u.found c.suit ++ [c] else u.found x.suit).length) = true
      rw [ite_eq_right hxs]
      exact hnext
    have hpoV : V.pileOfTop x = some a := by
      rw [pileOfTop_congr x hVp]
      exact hpo
    have hstepV := tabToFound_fires_eq hnextV hpoV
    -- found-field facts
    have hVfc : V.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hVf]; try rfl
    have hVfx : V.found x.suit
        = (u.setFound c.suit (u.found c.suit ++ [c])).found x.suit := by
      rw [hVf]; try rfl
    have hs1fc : s₁.found = (u.setFound x.suit (u.found x.suit ++ [x])).found := by
      rw [hs₁]; try rfl
    have hsfcx : s₁.found c.suit
        = (u.setFound x.suit (u.found x.suit ++ [x])).found c.suit := by
      rw [hs₁]; try rfl
    -- the raise's landing is the s₁-side front's landing
    have hLand : {V.setFound x.suit (V.found x.suit ++ [x])
        with
        piles := fun a' => if a' = a then
            Pile.afterRunRemoved (V.piles a) (chop (V.piles a).faceUp)
          else V.piles a' } = s' := by
      apply State.ext
      · -- found: the double bumps commute across the two bases
        show (V.setFound x.suit (V.found x.suit ++ [x])).found = s'.found
        have hfL : (V.setFound x.suit (V.found x.suit ++ [x])).found
            = ((u.setFound c.suit (u.found c.suit ++ [c])).setFound x.suit
                ((u.setFound c.suit (u.found c.suit ++ [c])).found x.suit ++ [x])).found :=
          setFound_found_congr hVfc (congrArg (fun l => l ++ [x]) hVfx)
        have hfR : (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found
            = ((u.setFound x.suit (u.found x.suit ++ [x])).setFound c.suit
                ((u.setFound x.suit (u.found x.suit ++ [x])).found c.suit ++ [c])).found :=
          setFound_found_congr hs1fc (congrArg (fun l => l ++ [c]) hsfcx)
        have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
          rw [hSf]; try rfl
        exact hfL.trans ((double_bump_comm hxs).trans (hfR.symm.trans hsF.symm))
      · -- piles: the write transfers through the equal piles
        show (fun a' => if a' = a then
            Pile.afterRunRemoved (V.piles a) (chop (V.piles a).faceUp)
          else V.piles a') = s'.piles
        rw [hVp, hSp]
        rw [hs₁]
        try rfl
      · show V.stock = s'.stock
        rw [hVs, hSs, hstock]
      · show V.waste = s'.waste
        rw [hVw, hSw]
      · show V.drawStep = s'.drawStep
        rw [hVds, hSds, hds1, hds]
    rw [run_step_cons hstepV, hLand]
    exact hrunρ

/-- **The `tabToTab` square.**  A pure pile move rides across the
front verbatim: `tabToTab` writes no foundation, so the two front
landings differ only by the pile write, which transfers. -/
private theorem front_board_tt {u s₁ : State} {c x : Card} {b : Base} {s' : State}
    (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hstep : State.step u (Move.tabToTab x b) = some s₁)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨a, hhld, hcp, hne, hs₁⟩ := step_tabToTab_inv' hstep
  -- the move is cycle-blind and foundation-blind
  have hstock : s₁.stock = u.stock := by rw [hs₁]; exact (putRun_keep).2.1
  have hwaste : s₁.waste = u.waste := by rw [hs₁]; exact (putRun_keep).2.2.1
  have hfound : s₁.found = u.found := by rw [hs₁]; exact putRun_found_keep
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hfound]
    exact hrungU
  obtain ⟨ρ, w₂, hrunρ, hwinρ⟩ := hwin₁
  rcases hfront₁ with ⟨pre, post, hs1stock, hcpre, hplay⟩ | ⟨preW, postW, hs1waste, hcpre, hplay⟩
  · -- the stock form at both ends
    obtain ⟨V, hVrun⟩ : ∃ V,
        u.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_stock hds hrungU (hstock.symm.trans hs1stock)⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_stock_shape hds hrungU (hstock.symm.trans hs1stock) V hVrun
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_stock_shape hds1 hn1 hs1stock s' hplay
    refine ⟨V, Or.inl ⟨pre, post, hstock.symm.trans hs1stock, hcpre, hVrun⟩, ?_⟩
    refine ⟨Move.tabToTab x b :: ρ, w₂, ?_, hwinρ⟩
    -- the move fires at the u-side landing by the readers
    have hhldV : V.pileHolding x = some a := by
      rw [pileHolding_congr hVp]
      exact hhld
    have hcpV : V.canPlace x b = true := by
      rw [canPlace_congr x b hVp]
      exact hcp
    have hfx : fromCard x (V.piles a).faceUp ≠ [] := by
      rw [congrArg Pile.faceUp (congrFun hVp a)]
      exact hne
    have hstepV : State.step V (Move.tabToTab x b) = some
        ((V.setPile a (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).putRun
          (fromCard x (V.piles a).faceUp) b) := by
      show (match V.pileHolding x with
          | none => none
          | some a' =>
              if V.canPlace x b then
                match fromCard x (V.piles a').faceUp with
                | [] => none
                | run => some
                    ((V.setPile a' (Pile.afterRunRemoved (V.piles a')
                        (below x (V.piles a').faceUp))).putRun run b)
              else none) = _
      rw [hhldV]
      show ((if V.canPlace x b = true then
              match fromCard x (V.piles a).faceUp with
              | [] => none
              | run => some
                  ((V.setPile a (Pile.afterRunRemoved (V.piles a)
                      (below x (V.piles a).faceUp))).putRun run b)
            else none)) = _
      rw [ite_eq_left hcpV]
      cases hfxV : fromCard x (V.piles a).faceUp with
      | nil =>
          rw [hfxV] at hfx
          exact absurd hfx (by simp)
      | cons r1 r2 => rfl
    -- the landing is the s₁-side front's landing
    have hLand : ((V.setPile a
          (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).putRun
          (fromCard x (V.piles a).faceUp) b) = s' := by
      apply State.ext
      · have hVF : V.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
          rw [hVf]; try rfl
        have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
          rw [hSf]; try rfl
        have hMid : (u.setFound c.suit (u.found c.suit ++ [c])).found
            = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found :=
          setFound_found_congr hfound.symm
            ((congrArg (fun l => l ++ [c]) (congrFun hfound c.suit)).symm)
        show ((V.setPile a (Pile.afterRunRemoved (V.piles a)
            (below x (V.piles a).faceUp))).putRun (fromCard x (V.piles a).faceUp) b).found
            = s'.found
        rw [putRun_found_keep, setPile_found]
        exact hVF.trans (hMid.trans hsF.symm)
      · show ((V.setPile a (Pile.afterRunRemoved (V.piles a)
            (below x (V.piles a).faceUp))).putRun (fromCard x (V.piles a).faceUp) b).piles
            = s'.piles
        rw [hSp, hs₁]
        exact piles_setPile_putRun_transfer hVp
      · have hk := putRun_keep (st := V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp)))
            (run := fromCard x (V.piles a).faceUp) (b := b)
        rw [hk.2.1, show (V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).stock
            = V.stock from rfl]
        rw [hVs, hSs]
      · have hk := putRun_keep (st := V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp)))
            (run := fromCard x (V.piles a).faceUp) (b := b)
        rw [hk.2.2.1, show (V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).waste
            = V.waste from rfl]
        rw [hVw, hSw, hwaste]
      · have hk := putRun_keep (st := V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp)))
            (run := fromCard x (V.piles a).faceUp) (b := b)
        rw [hk.2.2.2, show (V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).drawStep
            = V.drawStep from rfl]
        rw [hVds, hSds, hds1, hds]
    rw [run_step_cons hstepV, hLand]
    exact hrunρ
  · -- the waste form: the same verbatim ride through the waste engine
    obtain ⟨V, hVrun⟩ : ∃ V,
        u.run (List.replicate (u.stock.length + postW.length + 1) Move.draw
          ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_waste hds hrungU (hwaste.symm.trans hs1waste)⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_waste_shape hds hrungU (hwaste.symm.trans hs1waste) V hVrun
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_waste_shape hds1 hn1 hs1waste s' hplay
    refine ⟨V, Or.inr ⟨preW, postW, hwaste.symm.trans hs1waste, hcpre, hVrun⟩, ?_⟩
    refine ⟨Move.tabToTab x b :: ρ, w₂, ?_, hwinρ⟩
    have hhldV : V.pileHolding x = some a := by
      rw [pileHolding_congr hVp]
      exact hhld
    have hcpV : V.canPlace x b = true := by
      rw [canPlace_congr x b hVp]
      exact hcp
    have hfx : fromCard x (V.piles a).faceUp ≠ [] := by
      rw [congrArg Pile.faceUp (congrFun hVp a)]
      exact hne
    have hstepV : State.step V (Move.tabToTab x b) = some
        ((V.setPile a (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).putRun
          (fromCard x (V.piles a).faceUp) b) := by
      show (match V.pileHolding x with
          | none => none
          | some a' =>
              if V.canPlace x b then
                match fromCard x (V.piles a').faceUp with
                | [] => none
                | run => some
                    ((V.setPile a' (Pile.afterRunRemoved (V.piles a')
                        (below x (V.piles a').faceUp))).putRun run b)
              else none) = _
      rw [hhldV]
      show ((if V.canPlace x b = true then
              match fromCard x (V.piles a).faceUp with
              | [] => none
              | run => some
                  ((V.setPile a (Pile.afterRunRemoved (V.piles a)
                      (below x (V.piles a).faceUp))).putRun run b)
            else none)) = _
      rw [ite_eq_left hcpV]
      cases hfxV : fromCard x (V.piles a).faceUp with
      | nil =>
          rw [hfxV] at hfx
          exact absurd hfx (by simp)
      | cons r1 r2 => rfl
    have hLand : ((V.setPile a
          (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).putRun
          (fromCard x (V.piles a).faceUp) b) = s' := by
      apply State.ext
      · have hVF : V.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
          rw [hVf]; try rfl
        have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
          rw [hSf]; try rfl
        have hMid : (u.setFound c.suit (u.found c.suit ++ [c])).found
            = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found :=
          setFound_found_congr hfound.symm
            ((congrArg (fun l => l ++ [c]) (congrFun hfound c.suit)).symm)
        show ((V.setPile a (Pile.afterRunRemoved (V.piles a)
            (below x (V.piles a).faceUp))).putRun (fromCard x (V.piles a).faceUp) b).found
            = s'.found
        rw [putRun_found_keep, setPile_found]
        exact hVF.trans (hMid.trans hsF.symm)
      · show ((V.setPile a (Pile.afterRunRemoved (V.piles a)
            (below x (V.piles a).faceUp))).putRun (fromCard x (V.piles a).faceUp) b).piles
            = s'.piles
        rw [hSp, hs₁]
        exact piles_setPile_putRun_transfer hVp
      · have hk := putRun_keep (st := V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp)))
            (run := fromCard x (V.piles a).faceUp) (b := b)
        rw [hk.2.1, show (V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).stock
            = V.stock from rfl]
        rw [hVs, hSs, hstock]
      · have hk := putRun_keep (st := V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp)))
            (run := fromCard x (V.piles a).faceUp) (b := b)
        rw [hk.2.2.1, show (V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).waste
            = V.waste from rfl]
        rw [hVw, hSw]
      · have hk := putRun_keep (st := V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp)))
            (run := fromCard x (V.piles a).faceUp) (b := b)
        rw [hk.2.2.2, show (V.setPile a
            (Pile.afterRunRemoved (V.piles a) (below x (V.piles a).faceUp))).drawStep
            = V.drawStep from rfl]
        rw [hVds, hSds, hds1, hds]
    rw [run_step_cons hstepV, hLand]
    exact hrunρ

/-- A chop and a bump commute at the found field (foreign suits) —
the worry-back's slot drop against the front's raise. -/
private theorem chop_bump_comm {B : State} {x c : Card}
    (hne : x.suit ≠ c.suit) :
    ((B.setFound c.suit (B.found c.suit ++ [c])).setFound x.suit
        (chop ((B.setFound c.suit (B.found c.suit ++ [c])).found x.suit))).found
    = ((B.setFound x.suit (chop (B.found x.suit))).setFound c.suit
        ((B.setFound x.suit (chop (B.found x.suit))).found c.suit ++ [c])).found := by
  have h1 : ((B.setFound c.suit (B.found c.suit ++ [c])).found) x.suit
      = B.found x.suit := by
    show (if x.suit = c.suit then B.found c.suit ++ [c] else B.found x.suit) = B.found x.suit
    rw [ite_eq_right hne]
  have h2 : ((B.setFound x.suit (chop (B.found x.suit))).found) c.suit
      = B.found c.suit := by
    show (if c.suit = x.suit then chop (B.found x.suit) else B.found c.suit) = B.found c.suit
    rw [ite_eq_right (Ne.symm hne)]
  rw [h1, h2]
  exact congrArg State.found (setFound_comm (Ne.symm hne))

/-- **The `foundToTab` square.**  A foreign-suit worry-back rides
across the front: the slot drop and the fronting bump commute at
distinct suits, the placement transfers, so the front-first play
lands the same state the worry-first play fronts. -/
private theorem front_board_ft {u s₁ : State} {c x : Card} {b : Base} {s' : State}
    (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hxs : x.suit ≠ c.suit)
    (hstep : State.step u (Move.foundToTab x b) = some s₁)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨htop, hcp, hs₁⟩ := foundToTab_fires hstep
  -- the move is cycle-blind
  have hstock : s₁.stock = u.stock := by rw [hs₁]; exact (putCard_keep).2.1
  have hwaste : s₁.waste = u.waste := by rw [hs₁]; exact (putCard_keep).2.2.1
  have hfound : s₁.found = (u.setFound x.suit (chop (u.found x.suit))).found := by
    rw [hs₁, putCard_found_keep]
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hfound, setFound_found_ne (Ne.symm hxs)]
    exact hrungU
  obtain ⟨ρ, w₂, hrunρ, hwinρ⟩ := hwin₁
  rcases hfront₁ with ⟨pre, post, hs1stock, hcpre, hplay⟩ | ⟨preW, postW, hs1waste, hcpre, hplay⟩
  · -- the stock form at both ends
    obtain ⟨V, hVrun⟩ : ∃ V,
        u.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_stock hds hrungU (hstock.symm.trans hs1stock)⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_stock_shape hds hrungU (hstock.symm.trans hs1stock) V hVrun
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_stock_shape hds1 hn1 hs1stock s' hplay
    refine ⟨V, Or.inl ⟨pre, post, hstock.symm.trans hs1stock, hcpre, hVrun⟩, ?_⟩
    refine ⟨Move.foundToTab x b :: ρ, w₂, ?_, hwinρ⟩
    -- the worry fires at the u-side landing by the readers
    have htopV : V.foundTop x.suit = some x := by
      show lastOf (V.found x.suit) = some x
      rw [hVf]
      show lastOf (if x.suit = c.suit then u.found c.suit ++ [c] else u.found x.suit)
          = some x
      rw [ite_eq_right hxs]
      exact htop
    have hcpV : V.canPlace x b = true := by
      rw [canPlace_congr x b hVp]
      exact hcp
    have hstepV := foundToTab_fires_eq htopV hcpV
    -- found-field facts
    have hVfc : V.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hVf]; try rfl
    have hVx : V.found x.suit
        = (u.setFound c.suit (u.found c.suit ++ [c])).found x.suit := by
      rw [hVf]; try rfl
    have hs1fc : s₁.found
        = (u.setFound x.suit (chop (u.found x.suit))).found := by
      rw [hfound]
    have hsfcx : s₁.found c.suit
        = (u.setFound x.suit (chop (u.found x.suit))).found c.suit := by
      rw [hfound]; try rfl
    -- the worry's landing is the s₁-side front's landing
    have hLand : ((V.setFound x.suit (chop (V.found x.suit))).putCard x b) = s' := by
      apply State.ext
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).found
            = (V.setFound x.suit (chop (V.found x.suit))).found from putCard_found_keep]
        show (V.setFound x.suit (chop (V.found x.suit))).found = s'.found
        have hL : (V.setFound x.suit (chop (V.found x.suit))).found
            = ((u.setFound c.suit (u.found c.suit ++ [c])).setFound x.suit
                (chop ((u.setFound c.suit (u.found c.suit ++ [c])).found x.suit))).found :=
          setFound_found_congr hVfc (congrArg chop hVx)
        have hR : (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found
            = ((u.setFound x.suit (chop (u.found x.suit))).setFound c.suit
                ((u.setFound x.suit (chop (u.found x.suit))).found c.suit ++ [c])).found :=
          setFound_found_congr hs1fc (congrArg (fun l => l ++ [c]) hsfcx)
        have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
          rw [hSf]; try rfl
        exact hL.trans ((chop_bump_comm hxs).trans (hR.symm.trans hsF.symm))
      · have hpc' : (V.setFound x.suit (chop (V.found x.suit))).piles
            = (u.setFound x.suit (chop (u.found x.suit))).piles := by
          show V.piles = u.piles
          rw [hVp]
        rw [putCard_piles_congr hpc', hSp, hs₁]
        try rfl
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).stock
            = (V.setFound x.suit (chop (V.found x.suit))).stock from (putCard_keep).2.1]
        show V.stock = s'.stock
        rw [hVs, hSs]
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).waste
            = (V.setFound x.suit (chop (V.found x.suit))).waste from (putCard_keep).2.2.1]
        show V.waste = s'.waste
        rw [hVw, hSw, hwaste]
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).drawStep
            = (V.setFound x.suit (chop (V.found x.suit))).drawStep from (putCard_keep).2.2.2]
        show V.drawStep = s'.drawStep
        rw [hVds, hSds, hds1, hds]
    rw [run_step_cons hstepV, hLand]
    exact hrunρ
  · -- the waste form: the same exchange through the waste engine
    obtain ⟨V, hVrun⟩ : ∃ V,
        u.run (List.replicate (u.stock.length + postW.length + 1) Move.draw
          ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_waste hds hrungU (hwaste.symm.trans hs1waste)⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_waste_shape hds hrungU (hwaste.symm.trans hs1waste) V hVrun
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_waste_shape hds1 hn1 hs1waste s' hplay
    refine ⟨V, Or.inr ⟨preW, postW, hwaste.symm.trans hs1waste, hcpre, hVrun⟩, ?_⟩
    refine ⟨Move.foundToTab x b :: ρ, w₂, ?_, hwinρ⟩
    have htopV : V.foundTop x.suit = some x := by
      show lastOf (V.found x.suit) = some x
      rw [hVf]
      show lastOf (if x.suit = c.suit then u.found c.suit ++ [c] else u.found x.suit)
          = some x
      rw [ite_eq_right hxs]
      exact htop
    have hcpV : V.canPlace x b = true := by
      rw [canPlace_congr x b hVp]
      exact hcp
    have hstepV := foundToTab_fires_eq htopV hcpV
    have hVfc : V.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hVf]; try rfl
    have hVx : V.found x.suit
        = (u.setFound c.suit (u.found c.suit ++ [c])).found x.suit := by
      rw [hVf]; try rfl
    have hs1fc : s₁.found
        = (u.setFound x.suit (chop (u.found x.suit))).found := by
      rw [hfound]
    have hsfcx : s₁.found c.suit
        = (u.setFound x.suit (chop (u.found x.suit))).found c.suit := by
      rw [hfound]; try rfl
    have hLand : ((V.setFound x.suit (chop (V.found x.suit))).putCard x b) = s' := by
      apply State.ext
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).found
            = (V.setFound x.suit (chop (V.found x.suit))).found from putCard_found_keep]
        show (V.setFound x.suit (chop (V.found x.suit))).found = s'.found
        have hL : (V.setFound x.suit (chop (V.found x.suit))).found
            = ((u.setFound c.suit (u.found c.suit ++ [c])).setFound x.suit
                (chop ((u.setFound c.suit (u.found c.suit ++ [c])).found x.suit))).found :=
          setFound_found_congr hVfc (congrArg chop hVx)
        have hR : (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found
            = ((u.setFound x.suit (chop (u.found x.suit))).setFound c.suit
                ((u.setFound x.suit (chop (u.found x.suit))).found c.suit ++ [c])).found :=
          setFound_found_congr hs1fc (congrArg (fun l => l ++ [c]) hsfcx)
        have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
          rw [hSf]; try rfl
        exact hL.trans ((chop_bump_comm hxs).trans (hR.symm.trans hsF.symm))
      · have hpc' : (V.setFound x.suit (chop (V.found x.suit))).piles
            = (u.setFound x.suit (chop (u.found x.suit))).piles := by
          show V.piles = u.piles
          rw [hVp]
        rw [putCard_piles_congr hpc', hSp, hs₁]
        try rfl
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).stock
            = (V.setFound x.suit (chop (V.found x.suit))).stock from (putCard_keep).2.1]
        show V.stock = s'.stock
        rw [hVs, hSs, hstock]
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).waste
            = (V.setFound x.suit (chop (V.found x.suit))).waste from (putCard_keep).2.2.1]
        show V.waste = s'.waste
        rw [hVw, hSw]
      · rw [show ((V.setFound x.suit (chop (V.found x.suit))).putCard x b).drawStep
            = (V.setFound x.suit (chop (V.found x.suit))).drawStep from (putCard_keep).2.2.2]
        show V.drawStep = s'.drawStep
        rw [hVds, hSds, hds1, hds]
    rw [run_step_cons hstepV, hLand]
    exact hrunρ

/-! #### The consuming squares — the rotation resyncs -/

/-- **The consuming `wasteToFound` square, stock form.**  The head
spends a foreign card `x` (≠ c) from the waste into the foundation.
The front from `u` deals `c` out while `x` keeps riding the cycle,
so the win lifts by resyncing: draw round until `x` is back at hand
(drain the stock remainder, recycle, deal the whole waste above
`x`), re-spend it — the double bumps commute at the distinct suits —
then deal on past the remainder: the end state is the `s₁`-side
front's landing exactly, all position literals from the composites. -/
private theorem front_consume_wtf_stock {u s₁ : State} {c x : Card} {s' : State}
    (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hnextX : u.nextUp x = true) (hxc : x ≠ c)
    (hstep : State.step u (Move.wasteToFound x) = some s₁)
    (hcycu : c ∈ u.stock) (hwf₁ : s₁.WF)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨hwis, hnx, ws, hwastee, hs₁⟩ := wasteToFound_fires hstep
  have hxsu : x.suit ≠ c.suit := fun hcon => hxc (nextUp_pair_eq hnx hrungU hcon)
  have hstock : s₁.stock = u.stock := by rw [hs₁]; rfl
  have hs1found : s₁.found = (u.setFound x.suit (u.found x.suit ++ [x])).found := by
    rw [hs₁]; try rfl
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hs1found, setFound_found_ne (Ne.symm hxsu)]
    exact hrungU
  obtain ⟨ρ, w₂, hrunρ, hwinρ⟩ := hwin₁
  rcases hfront₁ with ⟨pre, post, hs1stock, hcpre, hplay⟩ | ⟨preW, postW, hs1waste, hcpre, hplay⟩
  · -- the stock front at both ends; the cycle data is shared
    have hustock : u.stock = pre ++ c :: post := hstock.symm.trans hs1stock
    obtain ⟨V₀, hV₀run⟩ : ∃ V,
        u.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_stock hds hrungU hustock⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_stock_shape hds hrungU hustock V₀ hV₀run
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_stock_shape hds1 hn1 hs1stock s' hplay
    refine ⟨V₀, Or.inl ⟨pre, post, hustock, hcpre, hV₀run⟩, ?_⟩
    refine ⟨List.replicate post.length Move.draw
        ++ (List.replicate (ws.length + 1) Move.draw
          ++ (Move.wasteToFound x :: (List.replicate pre.length Move.draw ++ ρ))),
        w₂, ?_, hwinρ⟩
    -- segment A, part one: drain the stock remainder
    obtain ⟨B, hBr, hBst, hBw, hBf, hBp, hBds⟩ : ∃ B,
        (V₀.run (List.replicate post.length Move.draw) = some B
          ∧ B.stock = ([] : List Card)
          ∧ B.waste = post.reverse ++ (pre.reverse ++ x :: ws)
          ∧ B.found = V₀.found ∧ B.piles = V₀.piles ∧ B.drawStep = V₀.drawStep) := by
      have hd := drain_run1 post.length (show V₀.drawStep = 1 by rw [hVds, hds])
        (show post.length ≤ V₀.stock.length by rw [hVs]; exact Nat.le_refl _)
      have htp : post.take post.length = post := by
        have := table_take_pre post ([] : List Card)
        rw [show post ++ ([] : List Card) = post from List.append_nil post] at this
        exact this
      refine ⟨State.mk V₀.found V₀.piles ([] : List Card)
          (post.reverse ++ (pre.reverse ++ x :: ws)) V₀.drawStep, ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hd, hVs, hVw, hwastee]
      refine congrArg some (State.ext rfl rfl
        (table_drop_ge post post.length (Nat.le_refl _)) ?_ rfl)
      rw [htp]
    -- segment A, part two: recycle and deal the waste above x
    have hBne : B.waste = [] → False := by
      intro hcon
      have hxw : x ∈ B.waste := by
        rw [hBw]
        exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr (List.mem_cons_self ..))))
      rw [hcon] at hxw
      exact absurd hxw (by simp)
    have hBle : ws.length + 1 ≤ B.waste.length := by
      rw [hBw, List.length_append, List.length_append, List.length_reverse,
        List.length_reverse, List.length_cons]
      omega
    obtain ⟨G, hGr, hGst, hGw, hGf, hGp, hGds⟩ : ∃ G,
        (B.run (List.replicate (ws.length + 1) Move.draw) = some G
          ∧ G.stock = pre ++ post ∧ G.waste = x :: ws
          ∧ G.found = B.found ∧ G.piles = B.piles ∧ G.drawStep = B.drawStep) := by
      have hBds1 : B.drawStep = 1 := by rw [hBds, hVds, hds]
      have hrd := redeal_run1 ws.length hBds1 hBst hBne hBle
      -- the recycled order, left-deep
      have hrev : (post.reverse ++ (pre.reverse ++ x :: ws)).reverse
          = ((ws.reverse ++ [x]) ++ pre) ++ post := by
        rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
          List.reverse_reverse, List.reverse_cons]
      have hlen : (ws.reverse ++ [x]).length = ws.length + 1 := by
        rw [List.length_append, List.length_reverse]
        rfl
      have hlX : ws.length + 1 ≤ ((ws.reverse ++ [x]) ++ pre).length := by
        rw [List.length_append, hlen]
        omega
      have hdro : (post.reverse ++ (pre.reverse ++ x :: ws)).reverse.drop (ws.length + 1)
          = pre ++ post := by
        rw [hrev,
          table_drop_app_le ((ws.reverse ++ [x]) ++ pre) post (ws.length + 1) hlX,
          table_drop_app_le (ws.reverse ++ [x]) pre (ws.length + 1)
            (show ws.length + 1 ≤ (ws.reverse ++ [x]).length by
              rw [hlen]; exact Nat.le_refl _),
          table_drop_ge (ws.reverse ++ [x]) (ws.length + 1)
            (by rw [hlen]; exact Nat.le_refl _),
          List.nil_append]
      have htak : (post.reverse ++ (pre.reverse ++ x :: ws)).reverse.take (ws.length + 1)
          = ws.reverse ++ [x] := by
        rw [hrev,
          table_take_app_le ((ws.reverse ++ [x]) ++ pre) post (ws.length + 1) hlX,
          table_take_app_le (ws.reverse ++ [x]) pre (ws.length + 1)
            (show ws.length + 1 ≤ (ws.reverse ++ [x]).length by
              rw [hlen]; exact Nat.le_refl _),
          table_take_ge (ws.reverse ++ [x]) (ws.length + 1)
            (by rw [hlen]; exact Nat.le_refl _)]
      refine ⟨State.mk B.found B.piles (pre ++ post) (x :: ws) B.drawStep,
        ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hrd, hBw]
      refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
      · show (post.reverse ++ (pre.reverse ++ x :: ws)).reverse.drop (ws.length + 1) = _
        rw [hdro]
      · show ((post.reverse ++ (pre.reverse ++ x :: ws)).reverse.take (ws.length + 1)).reverse
            ++ ([] : List Card) = x :: ws
        rw [htak, List.reverse_append, List.reverse_reverse, List.reverse_cons]
        simp
    -- the x-spend at G
    have hGnxt : G.nextUp x = true := by
      show decide (x.rank.toIdx = (G.found x.suit).length) = true
      rw [hGf, hBf, hVf]
      show decide (x.rank.toIdx =
          (if x.suit = c.suit then u.found c.suit ++ [c] else u.found x.suit).length) = true
      rw [ite_eq_right hxsu]
      exact hnextX
    have hstepG := wtf_step_raised (s := G) (c := x) (ws := ws) hGw hGnxt
    -- segment C: deal on past the pre segment
    have hG'st : (raisedMid G ws x).stock = pre ++ post := hGst
    obtain ⟨L, hLr, hLs, hLw, hLf, hLp, hLds⟩ : ∃ L,
        ((raisedMid G ws x).run (List.replicate pre.length Move.draw) = some L
          ∧ L.stock = post ∧ L.waste = pre.reverse ++ ws
          ∧ L.found = (raisedMid G ws x).found
          ∧ L.piles = (raisedMid G ws x).piles
          ∧ L.drawStep = (raisedMid G ws x).drawStep) := by
      have hd := drain_run1 pre.length
          (show (raisedMid G ws x).drawStep = 1 by
            show G.drawStep = 1
            rw [hGds, hBds, hVds, hds])
          (show pre.length ≤ (raisedMid G ws x).stock.length by
            rw [hG'st, List.length_append]
            omega)
      refine ⟨State.mk (raisedMid G ws x).found (raisedMid G ws x).piles post
          (pre.reverse ++ ws) (raisedMid G ws x).drawStep,
        ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hd, hG'st]
      refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
      · rw [table_drop_pre pre post]
      · rw [show (pre ++ post).take pre.length = pre from table_take_pre pre post]
        rfl
    -- the resynced landing L equals the s₁-side front's landing s'
    have hGfc : G.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hGf, hBf, hVf]
      rfl
    have hGfx : G.found x.suit
        = (u.setFound c.suit (u.found c.suit ++ [c])).found x.suit := by
      rw [hGf, hBf, hVf]
      rfl
    have hsfcx : s₁.found c.suit
        = (u.setFound x.suit (u.found x.suit ++ [x])).found c.suit := by
      rw [hs1found]
      try rfl
    have hs1w : s₁.waste = ws := by rw [hs₁]; try rfl
    have hLand : L = s' := by
      apply State.ext
      · rw [hLf]
        have hfL : (G.setFound x.suit (G.found x.suit ++ [x])).found
            = ((u.setFound c.suit (u.found c.suit ++ [c])).setFound x.suit
                ((u.setFound c.suit (u.found c.suit ++ [c])).found x.suit ++ [x])).found :=
          setFound_found_congr hGfc (congrArg (fun l => l ++ [x]) hGfx)
        have hfR : (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found
            = ((u.setFound x.suit (u.found x.suit ++ [x])).setFound c.suit
                ((u.setFound x.suit (u.found x.suit ++ [x])).found c.suit ++ [c])).found :=
          setFound_found_congr hs1found (congrArg (fun l => l ++ [c]) hsfcx)
        have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
          rw [hSf]
          try rfl
        show (G.setFound x.suit (G.found x.suit ++ [x])).found = s'.found
        exact hfL.trans ((double_bump_comm hxsu).trans (hfR.symm.trans hsF.symm))
      · rw [hLp, show (raisedMid G ws x).piles = G.piles from rfl, hGp, hBp, hVp, hSp, hs₁]
        rfl
      · rw [hLs, hSs]
      · rw [hLw, hSw, hs1w]
      · rw [hLds, show (raisedMid G ws x).drawStep = G.drawStep from rfl, hGds, hBds, hVds, hds,
        hSds, hds1]
    -- the win assembly: the resync play runs to s', then the tail wins
    have hglue : V₀.run (List.replicate post.length Move.draw
        ++ (List.replicate (ws.length + 1) Move.draw
          ++ (Move.wasteToFound x :: (List.replicate pre.length Move.draw ++ ρ))))
        = some w₂ := by
      rw [run_replicate_append post.length V₀ B _ hBr,
        run_replicate_append (ws.length + 1) B G _ hGr,
        run_step_cons hstepG,
        run_replicate_append pre.length (raisedMid G ws x) L ρ hLr,
        hLand]
      exact hrunρ
    exact hglue
  · -- the waste front at s₁ would double-book c against the census
    exfalso
    have hcs1 : c ∈ s₁.stock := by rw [hstock]; exact hcycu
    have hcw1 : c ∈ s₁.waste := by
      rw [hs1waste]
      exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
    exact (mem_stock_unique hwf₁ hcs1).2.1 hcw1

/-- **The consuming `wasteToTab` square, stock form.**  The head
parks a foreign card `x` (≠ c) from the waste onto a seat.  The
front from `u` delivers `c` with `x` riding the cycle; the same
resync draws `x` back to hand, re-parks it (a pure pile write — no
foundation is touched, so the founds agree without any bump
commutation), and deals on to the `s₁`-side front's landing. -/
private theorem front_consume_wtt_stock {u s₁ : State} {c x : Card} {b : Base} {s' : State}
    (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hstep : State.step u (Move.wasteToTab x b) = some s₁)
    (hcycu : c ∈ u.stock) (hwf₁ : s₁.WF)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨hwis, hcp, ws, hwastee, hs₁⟩ := wasteToTab_fires hstep
  -- the park writes no foundation and touches no cycle field
  have hstock : s₁.stock = u.stock := by rw [hs₁]; exact (putCard_keep).2.1
  have hs1found : s₁.found = u.found := by rw [hs₁]; exact putCard_found_keep
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hs1found]
    exact hrungU
  obtain ⟨ρ, w₂, hrunρ, hwinρ⟩ := hwin₁
  rcases hfront₁ with ⟨pre, post, hs1stock, hcpre, hplay⟩ | ⟨preW, postW, hs1waste, hcpre, hplay⟩
  · -- the stock front at both ends; the cycle data is shared
    have hustock : u.stock = pre ++ c :: post := hstock.symm.trans hs1stock
    obtain ⟨V₀, hV₀run⟩ : ∃ V,
        u.run (List.replicate (pre.length + 1) Move.draw ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_stock hds hrungU hustock⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ :=
      front_stock_shape hds hrungU hustock V₀ hV₀run
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ :=
      front_stock_shape hds1 hn1 hs1stock s' hplay
    refine ⟨V₀, Or.inl ⟨pre, post, hustock, hcpre, hV₀run⟩, ?_⟩
    refine ⟨List.replicate post.length Move.draw
        ++ (List.replicate (ws.length + 1) Move.draw
          ++ (Move.wasteToTab x b :: (List.replicate pre.length Move.draw ++ ρ))),
        w₂, ?_, hwinρ⟩
    -- segment A, part one: drain the stock remainder
    obtain ⟨B, hBr, hBst, hBw, hBf, hBp, hBds⟩ : ∃ B,
        (V₀.run (List.replicate post.length Move.draw) = some B
          ∧ B.stock = ([] : List Card)
          ∧ B.waste = post.reverse ++ (pre.reverse ++ x :: ws)
          ∧ B.found = V₀.found ∧ B.piles = V₀.piles ∧ B.drawStep = V₀.drawStep) := by
      have hd := drain_run1 post.length (show V₀.drawStep = 1 by rw [hVds, hds])
        (show post.length ≤ V₀.stock.length by rw [hVs]; exact Nat.le_refl _)
      have htp : post.take post.length = post := by
        have := table_take_pre post ([] : List Card)
        rw [show post ++ ([] : List Card) = post from List.append_nil post] at this
        exact this
      refine ⟨State.mk V₀.found V₀.piles ([] : List Card)
          (post.reverse ++ (pre.reverse ++ x :: ws)) V₀.drawStep, ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hd, hVs, hVw, hwastee]
      refine congrArg some (State.ext rfl rfl
        (table_drop_ge post post.length (Nat.le_refl _)) ?_ rfl)
      rw [htp]
    -- segment A, part two: recycle and deal the waste above x
    have hBne : B.waste = [] → False := by
      intro hcon
      have hxw : x ∈ B.waste := by
        rw [hBw]
        exact List.mem_append.2 (Or.inr (List.mem_append.2 (Or.inr (List.mem_cons_self ..))))
      rw [hcon] at hxw
      exact absurd hxw (by simp)
    have hBle : ws.length + 1 ≤ B.waste.length := by
      rw [hBw, List.length_append, List.length_append, List.length_reverse,
        List.length_reverse, List.length_cons]
      omega
    obtain ⟨G, hGr, hGst, hGw, hGf, hGp, hGds⟩ : ∃ G,
        (B.run (List.replicate (ws.length + 1) Move.draw) = some G
          ∧ G.stock = pre ++ post ∧ G.waste = x :: ws
          ∧ G.found = B.found ∧ G.piles = B.piles ∧ G.drawStep = B.drawStep) := by
      have hBds1 : B.drawStep = 1 := by rw [hBds, hVds, hds]
      have hrd := redeal_run1 ws.length hBds1 hBst hBne hBle
      have hrev : (post.reverse ++ (pre.reverse ++ x :: ws)).reverse
          = ((ws.reverse ++ [x]) ++ pre) ++ post := by
        rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
          List.reverse_reverse, List.reverse_cons]
      have hlen : (ws.reverse ++ [x]).length = ws.length + 1 := by
        rw [List.length_append, List.length_reverse]
        rfl
      have hlX : ws.length + 1 ≤ ((ws.reverse ++ [x]) ++ pre).length := by
        rw [List.length_append, hlen]
        omega
      have hdro : (post.reverse ++ (pre.reverse ++ x :: ws)).reverse.drop (ws.length + 1)
          = pre ++ post := by
        rw [hrev,
          table_drop_app_le ((ws.reverse ++ [x]) ++ pre) post (ws.length + 1) hlX,
          table_drop_app_le (ws.reverse ++ [x]) pre (ws.length + 1)
            (show ws.length + 1 ≤ (ws.reverse ++ [x]).length by
              rw [hlen]; exact Nat.le_refl _),
          table_drop_ge (ws.reverse ++ [x]) (ws.length + 1)
            (by rw [hlen]; exact Nat.le_refl _),
          List.nil_append]
      have htak : (post.reverse ++ (pre.reverse ++ x :: ws)).reverse.take (ws.length + 1)
          = ws.reverse ++ [x] := by
        rw [hrev,
          table_take_app_le ((ws.reverse ++ [x]) ++ pre) post (ws.length + 1) hlX,
          table_take_app_le (ws.reverse ++ [x]) pre (ws.length + 1)
            (show ws.length + 1 ≤ (ws.reverse ++ [x]).length by
              rw [hlen]; exact Nat.le_refl _),
          table_take_ge (ws.reverse ++ [x]) (ws.length + 1)
            (by rw [hlen]; exact Nat.le_refl _)]
      refine ⟨State.mk B.found B.piles (pre ++ post) (x :: ws) B.drawStep,
        ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hrd, hBw]
      refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
      · show (post.reverse ++ (pre.reverse ++ x :: ws)).reverse.drop (ws.length + 1) = _
        rw [hdro]
      · show ((post.reverse ++ (pre.reverse ++ x :: ws)).reverse.take (ws.length + 1)).reverse
            ++ ([] : List Card) = x :: ws
        rw [htak, List.reverse_append, List.reverse_reverse, List.reverse_cons]
        simp
    -- the park at G
    have hGcp : G.canPlace x b = true := by
      rw [canPlace_congr x b
        (show G.piles = u.piles from (hGp.trans hBp).trans hVp)]
      exact hcp
    have hcond : (G.wasteIs x && G.canPlace x b) = true := by
      rw [State.wasteIs_cons hGw x, hGcp, show decide (x = x) = true from decide_eq_true rfl]
      rfl
    have hstepG : State.step G (Move.wasteToTab x b)
        = some { G.putCard x b with waste := ws } := by
      show (if G.wasteIs x && G.canPlace x b then
          match G.waste with
          | _ :: lw => some ({ G.putCard x b with waste := lw })
          | [] => none
          else none) = _
      rw [hcond, hGw]
      rfl
    obtain ⟨G', hG'r, hG'f, hG'p, hG'st, hG'w, hG'ds⟩ : ∃ G',
        (State.step G (Move.wasteToTab x b) = some G'
          ∧ G'.found = G.found ∧ G'.piles = (G.putCard x b).piles
          ∧ G'.stock = G.stock ∧ G'.waste = ws ∧ G'.drawStep = G.drawStep) := by
      refine ⟨{ G.putCard x b with waste := ws }, hstepG,
        putCard_found_keep, rfl, (putCard_keep).2.1, rfl, (putCard_keep).2.2.2⟩
    -- segment C: deal on past the pre segment
    have hG'ne : pre.length ≤ G'.stock.length := by
      rw [hG'st, hGst]
      rw [List.length_append]
      omega
    obtain ⟨L, hLr, hLs, hLw, hLf, hLp, hLds⟩ : ∃ L,
        (G'.run (List.replicate pre.length Move.draw) = some L
          ∧ L.stock = post ∧ L.waste = pre.reverse ++ ws
          ∧ L.found = G'.found ∧ L.piles = G'.piles ∧ L.drawStep = G'.drawStep) := by
      have hd := drain_run1 pre.length
          (show G'.drawStep = 1 by rw [hG'ds, hGds, hBds, hVds, hds]) hG'ne
      refine ⟨State.mk G'.found G'.piles post (pre.reverse ++ ws) G'.drawStep,
        ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hd, hG'st, hGst]
      refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
      · rw [table_drop_pre pre post]
      · rw [show (pre ++ post).take pre.length = pre from table_take_pre pre post, hG'w]
        try rfl
    -- the found identities: both sides are the same c-bump over u.found
    have hGfulit : G.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hGf, hBf, hVf]
      try rfl
    have hLlit : L.found
        = (fun σ => if σ = c.suit then u.found c.suit ++ [c] else u.found σ) := by
      rw [hLf, hG'f, hGfulit]
      try rfl
    have hs1w : s₁.waste = ws := by rw [hs₁]; try rfl
    have hslit : s'.found
        = (fun σ => if σ = c.suit then u.found c.suit ++ [c] else u.found σ) := by
      rw [hSf, hs1found]
      try rfl
    -- the resynced landing L equals the s₁-side front's landing s'
    have hLand : L = s' := by
      apply State.ext
      · rw [hLlit, hslit]
      · rw [hLp, hG'p, putCard_piles_eq_of_eq
          (show G.piles = u.piles from (hGp.trans hBp).trans hVp) x b, hSp, hs₁]
        try rfl
      · rw [hLs, hSs]
      · rw [hLw, hSw, hs1w]
      · rw [hLds, hG'ds, hGds, hBds, hVds, hSds, hds1, hds]
    -- the win assembly
    have hglue : V₀.run (List.replicate post.length Move.draw
        ++ (List.replicate (ws.length + 1) Move.draw
          ++ (Move.wasteToTab x b :: (List.replicate pre.length Move.draw ++ ρ))))
        = some w₂ := by
      rw [run_replicate_append post.length V₀ B _ hBr,
        run_replicate_append (ws.length + 1) B G _ hGr,
        run_step_cons hG'r,
        run_replicate_append pre.length G' L ρ hLr,
        hLand]
      exact hrunρ
    exact hglue
  · -- the waste front at s₁ would double-book c against the census
    exfalso
    have hcs1 : c ∈ s₁.stock := by rw [hstock]; exact hcycu
    have hcw1 : c ∈ s₁.waste := by
      rw [hs1waste]
      exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
    exact (mem_stock_unique hwf₁ hcs1).2.1 hcw1

/-- **The consuming `wasteToTab` square, waste form.**  The head
parks a foreign card `x` (≠ c) from the waste onto a seat while `c`
rides the waste below it.  The front from `u` (data `x :: preW`,
`postW`) delivers `c` with `x` still above it; segment A is a plain
drain to `x`'s hand, the park re-fires with no foundation write,
and the closing leg is crossing (drain, then redeal down to `s'`'s
position split) or PRISTINE (`postW = []`), where the drained twin
is `sameCycle`-adjacent to `s'` and (A) transports the win — the
ONE genuine (A) cite of the replay. -/
private theorem front_consume_wtt_waste {u s₁ : State} {c x : Card} {b : Base} {s' : State}
    (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hxc : x ≠ c)
    (hstep : State.step u (Move.wasteToTab x b) = some s₁)
    (hcycw : c ∈ u.waste) (hwf₁ : s₁.WF)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨hwis, hcp, ws, hwastee, hs₁⟩ := wasteToTab_fires hstep
  -- the park is cycle-blind and foundation-blind
  have hstock : s₁.stock = u.stock := by rw [hs₁]; exact (putCard_keep).2.1
  have hs1found : s₁.found = u.found := by rw [hs₁]; exact putCard_found_keep
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hs1found]
    exact hrungU
  -- c sits below the parked head
  have hcws : c ∈ ws := by
    rw [hwastee] at hcycw
    rcases List.mem_cons.1 hcycw with heq | hmem
    · exact absurd heq (Ne.symm hxc)
    · exact hmem
  have hs1w : s₁.waste = ws := by rw [hs₁]; try rfl
  rcases hfront₁ with ⟨pre, post, hs1stock, hcpre, hplay⟩ | ⟨preW, postW, hs1waste, hcpre, hplay⟩
  · -- the stock front at s₁ would double-book c against the census
    exfalso
    have hcs1 : c ∈ s₁.stock := by
      rw [hs1stock]
      exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
    have hcw1 : c ∈ s₁.waste := by rw [hs1w]; exact hcws
    exact (mem_stock_unique hwf₁ hcs1).2.1 hcw1
  · -- the u-front rides x above c in the waste split verbatim
    have hcpreu : c ∉ x :: preW := by
      intro hcon
      rcases List.mem_cons.1 hcon with heq | hmem
      · exact hxc heq.symm
      · exact hcpre hmem
    have huw : u.waste = (x :: preW) ++ c :: postW := by
      rw [hwastee, ← hs1w, hs1waste]
      rfl
    obtain ⟨V₀, hV₀run⟩ : ∃ V,
        u.run (List.replicate (u.stock.length + postW.length + 1) Move.draw
          ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_waste hds hrungU huw⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ := front_waste_shape hds hrungU huw V₀ hV₀run
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ := front_waste_shape hds1 hn1 hs1waste s' hplay
    refine ⟨V₀, Or.inr ⟨x :: preW, postW, huw, hcpreu, hV₀run⟩, ?_⟩
    -- segment A: a plain drain to x's hand (the stock holds x above pre)
    have hrev : (x :: preW).reverse = preW.reverse ++ [x] := List.reverse_cons
    have hlenA : (preW.reverse ++ [x]).length = preW.length + 1 := by
      rw [List.length_append, List.length_reverse]
      rfl
    obtain ⟨G, hGr, hGst, hGw, hGf, hGp, hGds⟩ : ∃ G,
        (V₀.run (List.replicate (preW.length + 1) Move.draw) = some G
          ∧ G.stock = u.stock ∧ G.waste = x :: (preW ++ postW)
          ∧ G.found = V₀.found ∧ G.piles = V₀.piles ∧ G.drawStep = V₀.drawStep) := by
      have hd := drain_run1 (preW.length + 1) (show V₀.drawStep = 1 by rw [hVds, hds])
        (show preW.length + 1 ≤ V₀.stock.length by
          rw [hVs, hrev, List.length_append, hlenA]
          omega)
      refine ⟨State.mk V₀.found V₀.piles u.stock (x :: (preW ++ postW)) V₀.drawStep,
        ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hd, hVs, hVw, hrev]
      refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
      · rw [table_drop_app_le (preW.reverse ++ [x]) u.stock (preW.length + 1)
          (show preW.length + 1 ≤ (preW.reverse ++ [x]).length by
            rw [hlenA]; exact Nat.le_refl _),
          table_drop_ge (preW.reverse ++ [x]) (preW.length + 1)
            (show (preW.reverse ++ [x]).length ≤ preW.length + 1 by
              rw [hlenA]; exact Nat.le_refl _),
          List.nil_append]
      · rw [table_take_app_le (preW.reverse ++ [x]) u.stock (preW.length + 1)
          (show preW.length + 1 ≤ (preW.reverse ++ [x]).length by
            rw [hlenA]; exact Nat.le_refl _),
          table_take_ge (preW.reverse ++ [x]) (preW.length + 1)
            (show (preW.reverse ++ [x]).length ≤ preW.length + 1 by
              rw [hlenA]; exact Nat.le_refl _),
          List.reverse_append, List.reverse_reverse, List.reverse_cons]
        simp
    -- the park at G (no foundation write)
    have hGcp : G.canPlace x b = true := by
      rw [canPlace_congr x b (show G.piles = u.piles from hGp.trans hVp)]
      exact hcp
    have hcond : (G.wasteIs x && G.canPlace x b) = true := by
      rw [State.wasteIs_cons hGw x, hGcp, show decide (x = x) = true from decide_eq_true rfl]
      rfl
    have hstepG : State.step G (Move.wasteToTab x b)
        = some { G.putCard x b with waste := preW ++ postW } := by
      show (if G.wasteIs x && G.canPlace x b then
          match G.waste with
          | _ :: lw => some ({ G.putCard x b with waste := lw })
          | [] => none
          else none) = _
      rw [hcond, hGw]
      rfl
    obtain ⟨G', hG'r, hG'f, hG'p, hG'st, hG'w, hG'ds⟩ : ∃ G',
        (State.step G (Move.wasteToTab x b) = some G'
          ∧ G'.found = G.found ∧ G'.piles = (G.putCard x b).piles
          ∧ G'.stock = G.stock ∧ G'.waste = preW ++ postW
          ∧ G'.drawStep = G.drawStep) := by
      refine ⟨{ G.putCard x b with waste := preW ++ postW }, hstepG,
        putCard_found_keep, rfl, (putCard_keep).2.1, rfl, (putCard_keep).2.2.2⟩
    -- the found identities: both sides the same c-lit over u.found
    have hGulit : G.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hGf, hVf]
      rfl
    have hs1fu : s₁.found = u.found := hs1found
    by_cases hpw : postW = ([] : List Card)
    · -- PRISTINE: the drained twin is sameCycle-adjacent to s'
      subst hpw
      obtain ⟨R, hRr, hRs, hRw, hRf, hRp, hRds⟩ : ∃ R,
          (G'.run (List.replicate u.stock.length Move.draw) = some R
            ∧ R.stock = ([] : List Card) ∧ R.waste = u.stock.reverse ++ preW
            ∧ R.found = G'.found ∧ R.piles = G'.piles ∧ R.drawStep = G'.drawStep) := by
        have hd := drain_run1 u.stock.length
            (show G'.drawStep = 1 by rw [hG'ds, hGds, hVds, hds])
            (show u.stock.length ≤ G'.stock.length by rw [hG'st, hGst]; exact Nat.le_refl _)
        refine ⟨State.mk G'.found G'.piles ([] : List Card)
            (u.stock.reverse ++ preW) G'.drawStep, ?_, rfl, rfl, rfl, rfl, rfl⟩
        rw [hd, hG'st, hGst]
        refine congrArg some (State.ext rfl rfl
          (table_drop_ge u.stock u.stock.length (Nat.le_refl _)) ?_ rfl)
        rw [table_take_ge u.stock u.stock.length (Nat.le_refl _), hG'w,
          show preW ++ ([] : List Card) = preW from List.append_nil preW]
      -- R is sameCycle-adjacent to s'
      have hRlit : R.found
          = (fun σ => if σ = c.suit then u.found c.suit ++ [c] else u.found σ) := by
        rw [hRf, hG'f, hGulit]
        rfl
      have hslit : s'.found
          = (fun σ => if σ = c.suit then s₁.found c.suit ++ [c] else s₁.found σ) := hSf
      have hRpiles : R.piles = s'.piles := by
        rw [hRp, hG'p, putCard_piles_eq_of_eq
            (show G.piles = u.piles from hGp.trans hVp) x b, hSp, hs₁]
        try rfl
      have hRfnd : R.found = s'.found := by rw [hRlit, hslit, hs1fu]
      have hRcycle : cycleOf R = cycleOf s' := by
        rw [show cycleOf R = R.stock ++ R.waste.reverse from rfl,
            show cycleOf s' = s'.stock ++ s'.waste.reverse from rfl,
            hRs, hRw, hSs, hSw, hstock]
        rw [List.reverse_append, List.reverse_reverse, List.nil_append,
            show ([] : List Card).reverse = ([] : List Card) from rfl,
            List.append_nil]
      have hR1 : R.drawStep = 1 := by rw [hRds, hG'ds, hGds, hVds, hds]
      have hS1 : s'.drawStep = 1 := by rw [hSds, hds1]
      have hsc : sameCycle R s' := ⟨hRfnd, hRpiles, by rw [hR1, hS1], hRcycle⟩
      obtain ⟨πR, wR, hrunR, hwinR⟩ :=
        (draw1_sameCycle_sameFate hR1 hS1 hsc).mpr hwin₁
      refine ⟨List.replicate (preW.length + 1) Move.draw
          ++ (Move.wasteToTab x b :: (List.replicate u.stock.length Move.draw ++ πR)),
        wR, ?_, hwinR⟩
      rw [run_replicate_append (preW.length + 1) V₀ G _ hGr,
        run_step_cons hG'r,
        run_replicate_append u.stock.length G' R πR hRr]
      exact hrunR
    · -- CROSSING: drain the stock, redeal |postW| down to s' itself
      obtain ⟨z, zs, hzzs⟩ : ∃ z zs, postW = z :: zs := by
        cases postW with
        | nil => exact absurd rfl hpw
        | cons a as => exact ⟨a, as, rfl⟩
      obtain ⟨ρ, w₂, hrunρ, hwinρ⟩ := hwin₁
      obtain ⟨B2, hB2r, hB2s, hB2w, hB2f, hB2p, hB2ds⟩ : ∃ B2,
          (G'.run (List.replicate u.stock.length Move.draw) = some B2
            ∧ B2.stock = ([] : List Card)
            ∧ B2.waste = u.stock.reverse ++ (preW ++ postW)
            ∧ B2.found = G'.found ∧ B2.piles = G'.piles ∧ B2.drawStep = G'.drawStep) := by
        have hd := drain_run1 u.stock.length
            (show G'.drawStep = 1 by rw [hG'ds, hGds, hVds, hds])
            (show u.stock.length ≤ G'.stock.length by rw [hG'st, hGst]; exact Nat.le_refl _)
        refine ⟨State.mk G'.found G'.piles ([] : List Card)
            (u.stock.reverse ++ (preW ++ postW)) G'.drawStep,
          ?_, rfl, rfl, rfl, rfl, rfl⟩
        rw [hd, hG'st, hGst]
        refine congrArg some (State.ext rfl rfl
          (table_drop_ge u.stock u.stock.length (Nat.le_refl _)) ?_ rfl)
        rw [table_take_ge u.stock u.stock.length (Nat.le_refl _), hG'w]
      have hB2ne : B2.waste = ([] : List Card) → False := by
        intro hcon
        have hz : z ∈ B2.waste := by
          rw [hB2w]
          have hzpw : z ∈ preW ++ postW := by
            rw [hzzs]
            exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
          exact List.mem_append.2 (Or.inr hzpw)
        rw [hcon] at hz
        exact absurd hz (by simp)
      have hB2le : zs.length + 1 ≤ B2.waste.length := by
        rw [hB2w, List.length_append, List.length_append]
        have hzl : postW.length = zs.length + 1 := by rw [hzzs]; rfl
        omega
      have hcnt : zs.length + 1 = postW.length := by rw [hzzs]; rfl
      -- the recycled order, left-deep
      obtain ⟨L, hLr, hLs, hLw, hLf, hLp, hLds⟩ : ∃ L,
          (B2.run (List.replicate postW.length Move.draw) = some L
            ∧ L.stock = preW.reverse ++ u.stock ∧ L.waste = postW
            ∧ L.found = G'.found ∧ L.piles = G'.piles ∧ L.drawStep = G'.drawStep) := by
        have hrev2 : (u.stock.reverse ++ (preW ++ postW)).reverse
            = ((postW.reverse ++ preW.reverse) ++ u.stock) := by
          rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
            List.append_assoc]
        have hlenT : postW.length ≤ (postW.reverse ++ preW.reverse).length := by
          rw [List.length_append, List.length_reverse]
          omega
        have hlenT2 : postW.length ≤ postW.reverse.length := by
          rw [List.length_reverse]
          omega
        have hrd := redeal_run1 zs.length (show B2.drawStep = 1 by
            rw [hB2ds, hG'ds, hGds, hVds, hds]) hB2s hB2ne hB2le
        rw [hcnt] at hrd
        refine ⟨State.mk G'.found G'.piles (preW.reverse ++ u.stock) postW G'.drawStep,
          ?_, rfl, rfl, rfl, rfl, rfl⟩
        rw [hrd, hB2w, hrev2, hB2f, hB2p, hB2ds]
        refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
        · rw [table_drop_app_le (postW.reverse ++ preW.reverse) u.stock postW.length hlenT,
            table_drop_app_le postW.reverse preW.reverse postW.length hlenT2,
            table_drop_ge postW.reverse postW.length
              (show postW.reverse.length ≤ postW.length by
                rw [List.length_reverse]; exact Nat.le_refl _),
            List.nil_append]
        · rw [table_take_app_le (postW.reverse ++ preW.reverse) u.stock postW.length hlenT,
            table_take_app_le postW.reverse preW.reverse postW.length hlenT2,
            table_take_ge postW.reverse postW.length
              (show postW.reverse.length ≤ postW.length by
                rw [List.length_reverse]; exact Nat.le_refl _),
            List.reverse_reverse, List.append_nil]
      -- the resynced landing L equals the s₁-side front's landing s'
      have hLlit : L.found
          = (fun σ => if σ = c.suit then u.found c.suit ++ [c] else u.found σ) := by
        rw [hLf, hG'f, hGulit]
        rfl
      have hslit : s'.found
          = (fun σ => if σ = c.suit then s₁.found c.suit ++ [c] else s₁.found σ) := hSf
      have hLand : L = s' := by
        apply State.ext
        · rw [hLlit, hslit, hs1fu]
        · rw [hLp, hG'p, putCard_piles_eq_of_eq
            (show G.piles = u.piles from hGp.trans hVp) x b, hSp, hs₁]
          try rfl
        · rw [hLs, hSs, hstock]
        · rw [hLw, hSw]
        · rw [hLds, hG'ds, hGds, hVds, hSds, hds1, hds]
      refine ⟨List.replicate (preW.length + 1) Move.draw
          ++ (Move.wasteToTab x b
            :: (List.replicate u.stock.length Move.draw
                ++ (List.replicate postW.length Move.draw ++ ρ))),
        w₂, ?_, hwinρ⟩
      rw [run_replicate_append (preW.length + 1) V₀ G _ hGr,
        run_step_cons hG'r,
        run_replicate_append u.stock.length G' B2 _ hB2r,
        run_replicate_append postW.length B2 L ρ hLr,
        hLand]
      exact hrunρ

/-- **The consuming `wasteToFound` square, waste form.**  The head
raises a foreign card `x` (≠ c) from the waste into the foundation
while `c` rides the waste below it.  Segment A drains to `x`'s
hand, the raise re-fires with the double bumps commuting at the
distinct suits (`double_bump_comm`), and the closing leg is
crossing or PRISTINE exactly as in the park version — the win rides
(A) there. -/
private theorem front_consume_wtf_waste {u s₁ : State} {c x : Card} {s' : State}
    (hds : u.drawStep = 1) (hrungU : u.nextUp c = true)
    (hxc : x ≠ c)
    (hstep : State.step u (Move.wasteToFound x) = some s₁)
    (hcycw : c ∈ u.waste) (hwf₁ : s₁.WF)
    (hfront₁ : FrontOK c s₁ s') (hwin₁ : WinFrom s') :
    ∃ s'', FrontOK c u s'' ∧ WinFrom s'' := by
  obtain ⟨hwis, hnx, ws, hwastee, hs₁⟩ := wasteToFound_fires hstep
  have hxsu : x.suit ≠ c.suit := fun hcon => hxc (nextUp_pair_eq hnx hrungU hcon)
  have hstock : s₁.stock = u.stock := by rw [hs₁]; rfl
  have hs1found : s₁.found = (u.setFound x.suit (u.found x.suit ++ [x])).found := by
    rw [hs₁]; try rfl
  have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
  have hn1 : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hs1found, setFound_found_ne (Ne.symm hxsu)]
    exact hrungU
  -- c sits below the raised head
  have hcws : c ∈ ws := by
    rw [hwastee] at hcycw
    rcases List.mem_cons.1 hcycw with heq | hmem
    · exact absurd heq (Ne.symm hxc)
    · exact hmem
  have hs1w : s₁.waste = ws := by rw [hs₁]; try rfl
  rcases hfront₁ with ⟨pre, post, hs1stock, hcpre, hplay⟩ | ⟨preW, postW, hs1waste, hcpre, hplay⟩
  · -- the stock front at s₁ would double-book c against the census
    exfalso
    have hcs1 : c ∈ s₁.stock := by
      rw [hs1stock]
      exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
    have hcw1 : c ∈ s₁.waste := by rw [hs1w]; exact hcws
    exact (mem_stock_unique hwf₁ hcs1).2.1 hcw1
  · -- the u-front rides x above c in the waste split verbatim
    have hcpreu : c ∉ x :: preW := by
      intro hcon
      rcases List.mem_cons.1 hcon with heq | hmem
      · exact hxc heq.symm
      · exact hcpre hmem
    have huw : u.waste = (x :: preW) ++ c :: postW := by
      rw [hwastee, ← hs1w, hs1waste]
      rfl
    obtain ⟨V₀, hV₀run⟩ : ∃ V,
        u.run (List.replicate (u.stock.length + postW.length + 1) Move.draw
          ++ [Move.wasteToFound c]) = some V :=
      ⟨_, front_waste hds hrungU huw⟩
    obtain ⟨hVf, hVp, hVs, hVw, hVds⟩ := front_waste_shape hds hrungU huw V₀ hV₀run
    obtain ⟨hSf, hSp, hSs, hSw, hSds⟩ := front_waste_shape hds1 hn1 hs1waste s' hplay
    refine ⟨V₀, Or.inr ⟨x :: preW, postW, huw, hcpreu, hV₀run⟩, ?_⟩
    -- segment A: a plain drain to x's hand (the stock holds x above pre)
    have hrev : (x :: preW).reverse = preW.reverse ++ [x] := List.reverse_cons
    have hlenA : (preW.reverse ++ [x]).length = preW.length + 1 := by
      rw [List.length_append, List.length_reverse]
      rfl
    obtain ⟨G, hGr, hGst, hGw, hGf, hGp, hGds⟩ : ∃ G,
        (V₀.run (List.replicate (preW.length + 1) Move.draw) = some G
          ∧ G.stock = u.stock ∧ G.waste = x :: (preW ++ postW)
          ∧ G.found = V₀.found ∧ G.piles = V₀.piles ∧ G.drawStep = V₀.drawStep) := by
      have hd := drain_run1 (preW.length + 1) (show V₀.drawStep = 1 by rw [hVds, hds])
        (show preW.length + 1 ≤ V₀.stock.length by
          rw [hVs, hrev, List.length_append, hlenA]
          omega)
      refine ⟨State.mk V₀.found V₀.piles u.stock (x :: (preW ++ postW)) V₀.drawStep,
        ?_, rfl, rfl, rfl, rfl, rfl⟩
      rw [hd, hVs, hVw, hrev]
      refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
      · rw [table_drop_app_le (preW.reverse ++ [x]) u.stock (preW.length + 1)
          (show preW.length + 1 ≤ (preW.reverse ++ [x]).length by
            rw [hlenA]; exact Nat.le_refl _),
          table_drop_ge (preW.reverse ++ [x]) (preW.length + 1)
            (show (preW.reverse ++ [x]).length ≤ preW.length + 1 by
              rw [hlenA]; exact Nat.le_refl _),
          List.nil_append]
      · rw [table_take_app_le (preW.reverse ++ [x]) u.stock (preW.length + 1)
          (show preW.length + 1 ≤ (preW.reverse ++ [x]).length by
            rw [hlenA]; exact Nat.le_refl _),
          table_take_ge (preW.reverse ++ [x]) (preW.length + 1)
            (show (preW.reverse ++ [x]).length ≤ preW.length + 1 by
              rw [hlenA]; exact Nat.le_refl _),
          List.reverse_append, List.reverse_reverse, List.reverse_cons]
        simp
    -- the raise at G
    have hGnxt : G.nextUp x = true := by
      show decide (x.rank.toIdx = (G.found x.suit).length) = true
      rw [hGf, hVf]
      show decide (x.rank.toIdx =
          (if x.suit = c.suit then u.found c.suit ++ [c] else u.found x.suit).length) = true
      rw [ite_eq_right hxsu]
      exact hnx
    have hstepG := wtf_step_raised (s := G) (c := x) (ws := preW ++ postW) hGw hGnxt
    obtain ⟨G', hG'r, hG'f, hG'p, hG'st, hG'w, hG'ds⟩ : ∃ G',
        (State.step G (Move.wasteToFound x) = some G'
          ∧ G'.found = (fun σ => if σ = x.suit then G.found x.suit ++ [x] else G.found σ)
          ∧ G'.piles = G.piles ∧ G'.stock = G.stock
          ∧ G'.waste = preW ++ postW ∧ G'.drawStep = G.drawStep) := by
      refine ⟨raisedMid G (preW ++ postW) x, hstepG, rfl, rfl, rfl, rfl, rfl⟩
    -- the found identities: the double bumps commute at hxsu
    have hGfc : G.found = (u.setFound c.suit (u.found c.suit ++ [c])).found := by
      rw [hGf, hVf]
      rfl
    have hGfx : G.found x.suit
        = (u.setFound c.suit (u.found c.suit ++ [c])).found x.suit := by
      rw [hGf, hVf]
      rfl
    have hsfcx : s₁.found c.suit
        = (u.setFound x.suit (u.found x.suit ++ [x])).found c.suit := by
      rw [hs1found]
      try rfl
    have hfL : (G.setFound x.suit (G.found x.suit ++ [x])).found
        = ((u.setFound c.suit (u.found c.suit ++ [c])).setFound x.suit
            ((u.setFound c.suit (u.found c.suit ++ [c])).found x.suit ++ [x])).found :=
      setFound_found_congr hGfc (congrArg (fun l => l ++ [x]) hGfx)
    have hfR : (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found
        = ((u.setFound x.suit (u.found x.suit ++ [x])).setFound c.suit
            ((u.setFound x.suit (u.found x.suit ++ [x])).found c.suit ++ [c])).found :=
      setFound_found_congr hs1found (congrArg (fun l => l ++ [c]) hsfcx)
    have hsF : s'.found = (s₁.setFound c.suit (s₁.found c.suit ++ [c])).found := by
      rw [hSf]
      try rfl
    have hG'fLit : G'.found = (G.setFound x.suit (G.found x.suit ++ [x])).found := by
      rw [hG'f]
      rfl
    by_cases hpw : postW = ([] : List Card)
    · -- PRISTINE: the drained twin is sameCycle-adjacent to s'
      subst hpw
      obtain ⟨R, hRr, hRs, hRw, hRf, hRp, hRds⟩ : ∃ R,
          (G'.run (List.replicate u.stock.length Move.draw) = some R
            ∧ R.stock = ([] : List Card) ∧ R.waste = u.stock.reverse ++ preW
            ∧ R.found = G'.found ∧ R.piles = G'.piles ∧ R.drawStep = G'.drawStep) := by
        have hd := drain_run1 u.stock.length
            (show G'.drawStep = 1 by rw [hG'ds, hGds, hVds, hds])
            (show u.stock.length ≤ G'.stock.length by rw [hG'st, hGst]; exact Nat.le_refl _)
        refine ⟨State.mk G'.found G'.piles ([] : List Card)
            (u.stock.reverse ++ preW) G'.drawStep, ?_, rfl, rfl, rfl, rfl, rfl⟩
        rw [hd, hG'st, hGst]
        refine congrArg some (State.ext rfl rfl
          (table_drop_ge u.stock u.stock.length (Nat.le_refl _)) ?_ rfl)
        rw [table_take_ge u.stock u.stock.length (Nat.le_refl _), hG'w,
          show preW ++ ([] : List Card) = preW from List.append_nil preW]
      -- R is sameCycle-adjacent to s'
      have hRpiles : R.piles = s'.piles := by
        rw [hRp, hG'p, hGp, hVp, hSp, hs₁]
        try rfl
      have hRfnd : R.found = s'.found := by
        rw [hRf, hG'fLit]
        exact hfL.trans ((double_bump_comm hxsu).trans (hfR.symm.trans hsF.symm))
      have hRcycle : cycleOf R = cycleOf s' := by
        rw [show cycleOf R = R.stock ++ R.waste.reverse from rfl,
            show cycleOf s' = s'.stock ++ s'.waste.reverse from rfl,
            hRs, hRw, hSs, hSw, hstock]
        rw [List.reverse_append, List.reverse_reverse, List.nil_append,
            show ([] : List Card).reverse = ([] : List Card) from rfl,
            List.append_nil]
      have hR1 : R.drawStep = 1 := by rw [hRds, hG'ds, hGds, hVds, hds]
      have hS1 : s'.drawStep = 1 := by rw [hSds, hds1]
      have hsc : sameCycle R s' := ⟨hRfnd, hRpiles, by rw [hR1, hS1], hRcycle⟩
      obtain ⟨πR, wR, hrunR, hwinR⟩ :=
        (draw1_sameCycle_sameFate hR1 hS1 hsc).mpr hwin₁
      refine ⟨List.replicate (preW.length + 1) Move.draw
          ++ (Move.wasteToFound x :: (List.replicate u.stock.length Move.draw ++ πR)),
        wR, ?_, hwinR⟩
      rw [run_replicate_append (preW.length + 1) V₀ G _ hGr,
        run_step_cons hG'r,
        run_replicate_append u.stock.length G' R πR hRr]
      exact hrunR
    · -- CROSSING: drain the stock, redeal |postW| down to s' itself
      obtain ⟨z, zs, hzzs⟩ : ∃ z zs, postW = z :: zs := by
        cases postW with
        | nil => exact absurd rfl hpw
        | cons a as => exact ⟨a, as, rfl⟩
      obtain ⟨ρ, w₂, hrunρ, hwinρ⟩ := hwin₁
      obtain ⟨B2, hB2r, hB2s, hB2w, hB2f, hB2p, hB2ds⟩ : ∃ B2,
          (G'.run (List.replicate u.stock.length Move.draw) = some B2
            ∧ B2.stock = ([] : List Card)
            ∧ B2.waste = u.stock.reverse ++ (preW ++ postW)
            ∧ B2.found = G'.found ∧ B2.piles = G'.piles ∧ B2.drawStep = G'.drawStep) := by
        have hd := drain_run1 u.stock.length
            (show G'.drawStep = 1 by rw [hG'ds, hGds, hVds, hds])
            (show u.stock.length ≤ G'.stock.length by rw [hG'st, hGst]; exact Nat.le_refl _)
        refine ⟨State.mk G'.found G'.piles ([] : List Card)
            (u.stock.reverse ++ (preW ++ postW)) G'.drawStep,
          ?_, rfl, rfl, rfl, rfl, rfl⟩
        rw [hd, hG'st, hGst]
        refine congrArg some (State.ext rfl rfl
          (table_drop_ge u.stock u.stock.length (Nat.le_refl _)) ?_ rfl)
        rw [table_take_ge u.stock u.stock.length (Nat.le_refl _), hG'w]
      have hB2ne : B2.waste = ([] : List Card) → False := by
        intro hcon
        have hz : z ∈ B2.waste := by
          rw [hB2w]
          have hzpw : z ∈ preW ++ postW := by
            rw [hzzs]
            exact List.mem_append.2 (Or.inr (List.mem_cons_self ..))
          exact List.mem_append.2 (Or.inr hzpw)
        rw [hcon] at hz
        exact absurd hz (by simp)
      have hB2le : zs.length + 1 ≤ B2.waste.length := by
        rw [hB2w, List.length_append, List.length_append]
        have hzl : postW.length = zs.length + 1 := by rw [hzzs]; rfl
        omega
      have hcnt : zs.length + 1 = postW.length := by rw [hzzs]; rfl
      -- the recycled order, left-deep
      obtain ⟨L, hLr, hLs, hLw, hLf, hLp, hLds⟩ : ∃ L,
          (B2.run (List.replicate postW.length Move.draw) = some L
            ∧ L.stock = preW.reverse ++ u.stock ∧ L.waste = postW
            ∧ L.found = G'.found ∧ L.piles = G'.piles ∧ L.drawStep = G'.drawStep) := by
        have hrev2 : (u.stock.reverse ++ (preW ++ postW)).reverse
            = ((postW.reverse ++ preW.reverse) ++ u.stock) := by
          rw [List.reverse_append, List.reverse_append, List.reverse_reverse,
            List.append_assoc]
        have hlenT : postW.length ≤ (postW.reverse ++ preW.reverse).length := by
          rw [List.length_append, List.length_reverse]
          omega
        have hlenT2 : postW.length ≤ postW.reverse.length := by
          rw [List.length_reverse]
          omega
        have hrd := redeal_run1 zs.length (show B2.drawStep = 1 by
            rw [hB2ds, hG'ds, hGds, hVds, hds]) hB2s hB2ne hB2le
        rw [hcnt] at hrd
        refine ⟨State.mk G'.found G'.piles (preW.reverse ++ u.stock) postW G'.drawStep,
          ?_, rfl, rfl, rfl, rfl, rfl⟩
        rw [hrd, hB2w, hrev2, hB2f, hB2p, hB2ds]
        refine congrArg some (State.ext rfl rfl ?_ ?_ rfl)
        · rw [table_drop_app_le (postW.reverse ++ preW.reverse) u.stock postW.length hlenT,
            table_drop_app_le postW.reverse preW.reverse postW.length hlenT2,
            table_drop_ge postW.reverse postW.length
              (show postW.reverse.length ≤ postW.length by
                rw [List.length_reverse]; exact Nat.le_refl _),
            List.nil_append]
        · rw [table_take_app_le (postW.reverse ++ preW.reverse) u.stock postW.length hlenT,
            table_take_app_le postW.reverse preW.reverse postW.length hlenT2,
            table_take_ge postW.reverse postW.length
              (show postW.reverse.length ≤ postW.length by
                rw [List.length_reverse]; exact Nat.le_refl _),
            List.reverse_reverse, List.append_nil]
      -- the resynced landing L equals the s₁-side front's landing s'
      have hLand : L = s' := by
        apply State.ext
        · rw [hLf, hG'fLit]
          exact hfL.trans ((double_bump_comm hxsu).trans (hfR.symm.trans hsF.symm))
        · rw [hLp, hG'p, hGp, hVp, hSp, hs₁]
          try rfl
        · rw [hLs, hSs, hstock]
        · rw [hLw, hSw]
        · rw [hLds, hG'ds, hGds, hVds, hSds, hds1, hds]
      refine ⟨List.replicate (preW.length + 1) Move.draw
          ++ (Move.wasteToFound x
            :: (List.replicate u.stock.length Move.draw
                ++ (List.replicate postW.length Move.draw ++ ρ))),
        w₂, ?_, hwinρ⟩
      rw [run_replicate_append (preW.length + 1) V₀ G _ hGr,
        run_step_cons hG'r,
        run_replicate_append u.stock.length G' B2 _ hB2r,
        run_replicate_append postW.length B2 L ρ hLr,
        hLand]
      exact hrunρ

/- **(B) The compliant replay**: with `c` stocked next for its
foundation, a compliant winning play front-loads as a win after
dealing `c` out and stacking it.  Safety is not a premise — no case
reads it; the c-bundle passes to each successor on the compliance
alone.  The case ledger, one exchange per first move (an equality
square, or a `sameCycle` transport via (A)):

* `draw` — absorbed: one fewer fronting draw, same landing;
* `tabToFound` / `tabToTab` — equality squares (stock- and
  waste-blind, and the fronted card is elsewhere);
* `foundToTab x b`, x.suit ≠ c.suit — equality square (the slot
  drop and the fronting bump are at distinct suits);
* `wasteToFound x` / `wasteToTab x b`, x ≠ c — the consuming moves:
  the squares land up to `sameCycle` and (A) transports the win;
* the c-exits close without recursion: `wasteToFound c` — the
  fronting IS the play prefix's k+1 deal, so the tail wins verbatim;
  `wasteToTab c b` — the worry-back identity `[fronting,
  foundToTab c b] ≡ [wasteToTab c b]` (the raise-bump is undone by
  the lower; `shuttle_join`'s legs are the pieces).

STATUS (W5: PROVEN — see `replay_front_aux` and the theorem
below).  The landed private strip:

* the list surgery + the `drawStep = 1` deal composites
  (`drain_positions1`/`base_positions1`/`drain_run1`/`redeal_run1`,
  dedup-marked ports of `Phase`'s orbit strip);
* the two **fronting engines `front_stock`/`front_waste`** — the
  k-existence arithmetic made explicit: with `c` stocked at depth
  `|pre|`, `|pre|+1` drains land
  `⟨bump c, stock := suffix past c, waste := pre.reverse ++ old⟩`;
  with `c` wasted (`preW` above, `postW` below), the composite is
  drain-to-pass-base + one recycle-deal + `|postW|` deals, landing
  `⟨bump c, stock := preW.reverse ++ old stock, waste := postW⟩`;
* the spend step in raised form (`wtf_step_raised`,
  `step_wtf_inv1`) and `lower_foundToTab1` — the worry-back
  identity's leg ported from `Shuttle` (the `[wasteToFound c,
  foundToTab c b] ≡ [wasteToTab c b]` closing shape for the
  `wasteToTab c b` exit);
* `bump2_comm` — the two foundation bumps commute at distinct suits
  (the found half of every equality square at `x ≠ c`).

Route corrections for the assembly (probed, refute-first): the `\pi
= []` corner is WF-FREE — `isWin` caps every foundation at 13
while `nextUp c` pins `c.rank.toIdx < 13` against that very height,
so no step-preserved WF is needed anywhere in the induction; the
board-move squares are `draw`-pair syncs (equal stock/waste/drawStep
pairs stay synchronized through any number of draws, then the
bumps commute); the consuming-move square does NOT land up to
`sameCycle` — the two landings differ by a pure-draw ROTATION of
the same cycle (mutually reachable, so the win lifts without any
transport), and a genuine `sameCycle`-vs-(A) transport survives
only in the pristine corner of the waste-form fronting
(`postW = []`: the fronted card's slot is dealt back at the last
recycle, so the twin's cut never re-closes — THIS is the one place
(B) really cites (A)). -/
/-- **The dispatcher — the nine-case assembly over the `FrontOK`
motive.**  Strong induction on the play's length; every case is a
call into the landed engines above: nil and absorb, the three
board squares, the four consuming rotation-syncs, and the two
exits.  The compliance's first disjunct routes the c-leaving heads
to the exit engines; its second carries `lowersRung = false` and
the tail's compliance to the recursion. -/
private theorem replay_front_aux : ∀ (n : Nat) (c : Card) (u : State),
    u.WF → u.drawStep = 1 → u.nextUp c = true → (c ∈ u.stock ∨ c ∈ u.waste) →
    ∀ π w, π.length ≤ n → rungHeldUntilExit c π → u.run π = some w → w.isWin = true →
    ∃ s', FrontOK c u s' ∧ WinFrom s' := by
  intro n
  induction n with
  | zero =>
      intro c u hwfu hds hrung hcyc π w hlen hcomp hrun hwin
      cases π with
      | nil => exact (front_nil hrung hrun hwin).elim
      | cons m rest =>
          exfalso
          rw [List.length_cons] at hlen
          omega
  | succ n ih =>
      intro c u hwfu hds hrung hcyc π w hlen hcomp hrun hwin
      cases π with
      | nil => exact (front_nil hrung hrun hwin).elim
      | cons m rest =>
          obtain ⟨s₁, hstep, hrest⟩ := State.run_cons hrun
          have hlen2 : rest.length ≤ n := by
            rw [List.length_cons] at hlen
            omega
          have hwf₁ : s₁.WF := step_wf hwfu hstep
          have hds1 : s₁.drawStep = 1 := by rw [step_drawStep_keep hstep, hds]
          rcases hcomp with hex | ⟨hlr, hcrest⟩
          · -- the c-exit arms: leavesWaste c m = true
            cases m with
            | draw =>
                exfalso
                rw [show Move.leavesWaste c Move.draw = false from rfl] at hex
                exact absurd hex (by simp)
            | tabToFound y =>
                exfalso
                rw [show Move.leavesWaste c (Move.tabToFound y) = false from rfl] at hex
                exact absurd hex (by simp)
            | tabToTab y y2 =>
                exfalso
                rw [show Move.leavesWaste c (Move.tabToTab y y2) = false from rfl] at hex
                exact absurd hex (by simp)
            | foundToTab y y2 =>
                exfalso
                rw [show Move.leavesWaste c (Move.foundToTab y y2) = false from rfl] at hex
                exact absurd hex (by simp)
            | wasteToFound y =>
                by_cases hyc : y = c
                · rw [hyc] at hstep
                  exact front_exit_wtf hds hrung hstep hrest hwin
                · exfalso
                  rw [show Move.leavesWaste c (Move.wasteToFound y) = decide (y = c) from rfl,
                    decide_eq_false hyc] at hex
                  exact absurd hex (by simp)
            | wasteToTab y y2 =>
                by_cases hyc : y = c
                · rw [hyc] at hstep
                  exact front_exit_wtt hds hrung hstep hrest hwin
                · exfalso
                  rw [show Move.leavesWaste c (Move.wasteToTab y y2) = decide (y = c) from rfl,
                    decide_eq_false hyc] at hex
                  exact absurd hex (by simp)
          · -- the clean arms: lowersRung c m = false, tail compliant
            cases m with
            | draw =>
                have hn1 : s₁.nextUp c = true := by
                  show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                  rw [stepDraw_found (show u.stepDraw = some s₁ from hstep)]
                  exact hrung
                obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1
                  (draw_inCycle hstep hcyc) rest w hlen2 hcrest hrest hwin
                exact front_draw hwfu hwf₁ hds hrung hstep hfront₁ hwin₁
            | tabToFound y =>
                obtain ⟨hny, a, hpo⟩ := tabToFound_fires hstep
                have hs1shape := tabToFound_shape hstep hpo
                by_cases hys : y.suit = c.suit
                · exfalso
                  rw [nextUp_pair_eq hny hrung hys] at hpo
                  have hmem : c ∈ (u.piles a).faceUp := lastOf_mem (pileOfTop_top hpo).2
                  rcases hcyc with hcs | hcw
                  · exact ((mem_stock_unique hwfu hcs).1 a).2 hmem
                  · exact ((mem_waste_unique hwfu hcw).1 a).2 hmem
                · have hn1 : s₁.nextUp c = true := by
                    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                    rw [hs1shape]
                    show decide (c.rank.toIdx =
                        ((u.setFound y.suit (u.found y.suit ++ [y])).found c.suit).length) = true
                    rw [setFound_found_ne (Ne.symm hys)]
                    exact hrung
                  have hcy1 : c ∈ s₁.stock ∨ c ∈ s₁.waste := by rw [hs1shape]; exact hcyc
                  obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1 hcy1
                    rest w hlen2 hcrest hrest hwin
                  exact front_board_tf hds hrung hys hstep hfront₁ hwin₁
            | tabToTab y y2 =>
                obtain ⟨a, hhld, hcp, hne, hs1shape⟩ := step_tabToTab_inv' hstep
                have hfound : s₁.found = u.found := by
                  rw [hs1shape]
                  exact putRun_found_keep
                have hstock1 : s₁.stock = u.stock := by
                  rw [hs1shape]
                  exact (putRun_keep).2.1
                have hwaste1 : s₁.waste = u.waste := by
                  rw [hs1shape]
                  exact (putRun_keep).2.2.1
                have hn1 : s₁.nextUp c = true := by
                  show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                  rw [hfound]
                  exact hrung
                have hcy1 : c ∈ s₁.stock ∨ c ∈ s₁.waste := by
                  rcases hcyc with hcs | hcw
                  · exact Or.inl (by rw [hstock1]; exact hcs)
                  · exact Or.inr (by rw [hwaste1]; exact hcw)
                obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1 hcy1
                  rest w hlen2 hcrest hrest hwin
                exact front_board_tt hds hrung hstep hfront₁ hwin₁
            | foundToTab y y2 =>
                have hys : y.suit ≠ c.suit := by
                  intro hcon
                  rw [show Move.lowersRung c (Move.foundToTab y y2)
                      = decide (y.suit = c.suit) from rfl,
                    decide_eq_true hcon] at hlr
                  exact absurd hlr (by simp)
                obtain ⟨htop, hcp, hs1shape⟩ := foundToTab_fires hstep
                have hfound : s₁.found
                    = (u.setFound y.suit (chop (u.found y.suit))).found := by
                  rw [hs1shape]
                  exact putCard_found_keep
                have hstock1 : s₁.stock = u.stock := by
                  rw [hs1shape]
                  exact (putCard_keep).2.1
                have hwaste1 : s₁.waste = u.waste := by
                  rw [hs1shape]
                  exact (putCard_keep).2.2.1
                have hn1 : s₁.nextUp c = true := by
                  show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                  rw [hfound, setFound_found_ne (Ne.symm hys)]
                  exact hrung
                have hcy1 : c ∈ s₁.stock ∨ c ∈ s₁.waste := by
                  rcases hcyc with hcs | hcw
                  · exact Or.inl (by rw [hstock1]; exact hcs)
                  · exact Or.inr (by rw [hwaste1]; exact hcw)
                obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1 hcy1
                  rest w hlen2 hcrest hrest hwin
                exact front_board_ft hds hrung hys hstep hfront₁ hwin₁
            | wasteToFound y =>
                by_cases hyc : y = c
                · rw [hyc] at hstep
                  exact front_exit_wtf hds hrung hstep hrest hwin
                · obtain ⟨hwis, hny, ws, hwastee, hs1shape⟩ := wasteToFound_fires hstep
                  have hys : y.suit ≠ c.suit :=
                    fun hcon => hyc (nextUp_pair_eq hny hrung hcon)
                  have hs1found : s₁.found
                      = (u.setFound y.suit (u.found y.suit ++ [y])).found := by
                    rw [hs1shape]; try rfl
                  have hn1 : s₁.nextUp c = true := by
                    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                    rw [hs1found, setFound_found_ne (Ne.symm hys)]
                    exact hrung
                  rcases hcyc with hcs | hcw
                  · obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1
                      (Or.inl (by rw [hs1shape]; exact hcs)) rest w hlen2 hcrest hrest hwin
                    exact front_consume_wtf_stock hds hrung hny hyc hstep hcs
                      hwf₁ hfront₁ hwin₁
                  · have hwcs : c ∈ ws := by
                      rw [hwastee] at hcw
                      rcases List.mem_cons.1 hcw with heq | hmem
                      · exact absurd heq (Ne.symm hyc)
                      · exact hmem
                    obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1
                      (Or.inr (by rw [hs1shape]; exact hwcs)) rest w hlen2 hcrest hrest hwin
                    exact front_consume_wtf_waste hds hrung hyc hstep hcw
                      hwf₁ hfront₁ hwin₁
            | wasteToTab y y2 =>
                by_cases hyc : y = c
                · rw [hyc] at hstep
                  exact front_exit_wtt hds hrung hstep hrest hwin
                · obtain ⟨hwis, hcp, ws, hwastee, hs1shape⟩ := wasteToTab_fires hstep
                  have hn1 : s₁.nextUp c = true := by
                    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                    rw [show s₁.found = u.found from by
                        rw [hs1shape]; exact putCard_found_keep]
                    exact hrung
                  have hstock1 : s₁.stock = u.stock := by
                    rw [hs1shape]
                    exact (putCard_keep).2.1
                  rcases hcyc with hcs | hcw
                  · obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1
                      (Or.inl (by rw [hstock1]; exact hcs)) rest w hlen2 hcrest hrest hwin
                    exact front_consume_wtt_stock hds hrung hstep hcs
                      hwf₁ hfront₁ hwin₁
                  · have hwcs : c ∈ ws := by
                      rw [hwastee] at hcw
                      rcases List.mem_cons.1 hcw with heq | hmem
                      · exact absurd heq (Ne.symm hyc)
                      · exact hmem
                    obtain ⟨s', hfront₁, hwin₁⟩ := ih c s₁ hwf₁ hds1 hn1
                      (Or.inr (by rw [hs1shape]; exact hwcs)) rest w hlen2 hcrest hrest hwin
                    exact front_consume_wtt_waste hds hrung hyc hstep hcw
                      hwf₁ hfront₁ hwin₁

theorem draw1_compliant_replay {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock) :
    ∀ π w, rungHeldUntilExit c π → st.run π = some w → w.isWin = true →
      ∃ k s', st.run (List.replicate k Move.draw ++ [Move.wasteToFound c]) = some s' ∧
        WinFrom s' := by
  intro π w hcomp hrun hwin
  obtain ⟨s', hfront, hwin'⟩ := replay_front_aux π.length c st hwf hstep hrung
    (Or.inl hstock) π w (Nat.le_refl _) hcomp hrun hwin
  rcases hfront with ⟨pre, post, hdata, -, hplay⟩ | ⟨preW, postW, hdata, -, hplay⟩
  · exact ⟨pre.length + 1, s', hplay, hwin'⟩
  · exact ⟨st.stock.length + postW.length + 1, s', hplay, hwin'⟩

/-! #### (B) LANDED (W5).

The RESUME route banked here is complete: every engine named below
was rebuilt and proven sorry-free on this branch before the landing
commit, and the audit landed `draw1_compliant_replay` at
[propext, Quot.sound] with `stock_dominance_draw1` at
[propext, sorryAx, Quot.sound] whose sorryAx flows ONLY through the
(C)-premise engine `draw1_compliant_normalForm` into the named
residue `draw1_worry_spread_residue`.  The banked route notes and
trap list [plays with a cons island parse left-assoc; `(p && q) = true`
needs parens; `try rfl` after rw chains; tuple-style existential
witnesses; never `cases` a variable whose name must survive; never
inline restated redeal/putCard landings in `have :` types; commit
after every green engine] stay valid for the (C) and [GAP] rows. -/

/-- **(C) The normal form**: a winning play exists that keeps the
c-rung until `c` leaves the waste — B&G's safemoves discipline.  Any
pre-exit worry of `c`'s suit is the suit's foundation-top card; its
restack (`tabToFound`) must fire before the suit climbs again, and
the pair is either adjacent (cancel through the foundation round
trip — `tabToFound_undo_under` at the top, or `_bare`) or closes by
the same exchanges as (B)'s squares; the storage shape (a placement
onto the vacated seat) is the bare-floor residue's own assembly at
the worry-created seat — the shared [GAP] family.  TODO(proof). -/
private theorem sameRung_eq {st : State} {a b : Card}
    (ha : st.nextUp a = true) (hb : st.nextUp b = true) (hs : a.suit = b.suit) :
    a = b := by
  have hla : a.rank.toIdx = st.foundHeight a.suit := of_decide_eq_true ha
  have hlb : b.rank.toIdx = st.foundHeight b.suit := of_decide_eq_true hb
  rcases a with ⟨as, ar⟩
  rcases b with ⟨bs, br⟩
  have hss : as = bs := hs
  have hrr : ar = br := Rank.toIdx_inj (by rw [hla, hlb, hss])
  rw [hrr, hss]

/-- **(C)'s window-spread residue** — the row's ONE named stub.

The normal-form engine below reduces the compliant-play search to
this shape: a winning play whose FIRST c-suit worry-back — `x` is the
suit's foundation top; the rung bookkeeping pins the whole window to
it — is followed by something OTHER than its own restack.  The stub
owes a compliant winning play from `st` itself.

ROUTE (the whole (ii)+(iii) ledger, staged for the next pass):

* **The window accounting.**  The win founds `c` (`inCycle_notisWin`
  blocks every earlier end state), so `c` leaves the cycle inside
  the remaining play; the only raiser of a dropped c-suit rung is the
  dropped card itself (WF conservation: one card per suit and rank),
  so the restack `tabToFound x` exists in the window — possibly
  AFTER a c-park (`wasteToTab c`) that reads no rung: the straddle
  shape.  A first-passage extraction (the §12.1 `climb_firstPassage`
  family, NOT yet ported to Orig — the recorded gap) locates the
  restack while the window is open.
* **The spread exchanges** (each single square; the worry bubbles
  forward, or dually the restack backward, one move at a time): the
  `wasteToFound y` square (y.suit ≠ x.suit) is LANDED privately in
  this file (`foundToTab_wasteToFound_square`, composite-equal, its
  `putCard_piles_eq_of_eq` channel is the pattern-kernel for the
  rest); the remaining kinds have their no-interference corners,
  not new statements: `draw` reduces to the recycle-triple lemma
  (the draw reads only the stock/waste pair, the worry writes only
  foundations and piles — `draw_unfold` at both states plus the
  three `recycle` readers; the only guarded step is the `dealStock`
  shape); `wasteToTab y b'` / `foundToTab y b'` interfere exactly
  when the segment places onto the worry-created seat (a base
  reading `x`, or a landing pile shadowing the `pileOfTop` search) —
  the storage family below; `tabToFound y` is order-locked when the
  worry's own base is `inr y` (the raise consumed the worry's target
  card); `tabToTab` is cornered when the moved run passes through
  `x`; worry-worry pairs (`foundToTab` of the suit's next card down)
  never square — the second reads the POST-first foundation top
  (LIFO), so a bubble must jump the nested window as a unit, not
  through it.
* **The storage shape — the shared [GAP] family.**  When the segment
  stores onto the worry-created seat, the repair is a reshape, not a
  reordering: the placement re-homes through the foundations.
  `tabToFound_dominant_of_ground` (the (N) stub) is cited BY NAME as
  the bare-floor win-lift the storage prong consumes.  Its slack
  premise — the worried `x` is `safeToFound` at the window, by
  slack one under `safeToFound st c`, the (C) premise — is NOT
  carried here: the engine's clean prefix may spend the slack (an
  other-suit worry-back drops a height bound; `safeToFound` does not
  pass the bundle invariant, which is why (C)'s own statement keeps
  it at the root).  The storage prong must re-derive the slack at
  the window, or this residue earns a recorded premise repair.  As
  stated (no safety premise) the stub's truth rides on the classical
  B&G route; the wave-24 gate for (C) ("a compliant-less corner")
  doubles as this stub's refute gate — see the witness file.
-/
theorem draw1_worry_spread_residue {st : State} {c : Card} {x : Card} {b : Base}
    {s₁ : State} {m₂ : Move} {rest : List Move} {w : State}
    (hwf : st.WF) (hds : st.drawStep = 1) (hrung : st.nextUp c = true)
    (hcyc : c ∈ st.stock ∨ c ∈ st.waste)
    (hx : x.suit = c.suit)
    (hf : State.step st (Move.foundToTab x b) = some s₁)
    (hne : m₂ ≠ Move.tabToFound x)
    (hrun : s₁.run (m₂ :: rest) = some w) (hwin : w.isWin = true) :
    ∃ π v, st.run π = some v ∧ v.isWin = true ∧ rungHeldUntilExit c π := sorry

/-- **The (C) engine.**  Strong induction on the washing play's
length, with the engine bundle `{WF, drawStep = 1, nextUp c, c in
the cycle}` (the public statement's `c ∈ st.stock` is the root
instance; the invariant weakens to the cycle because a draw may deal
`c` into the waste before it is spent — the pre-exit regime).  The
case ledger: the empty play and the one-move worry both die on
`inCycle_notisWin` (an un-exited rung card blocks every win); an
exit head is compliant verbatim; a rung-clean head recurses at the
successor on the transferred bundle; an adjacent worry window
`[foundToTab x b; tabToFound x]` cancels through `foundToTab_return`
and recurses on the two-moves-shorter play; every spread window
routes to `draw1_worry_spread_residue`. -/
private theorem normform_aux : ∀ n : Nat, ∀ (st : State) (c : Card),
    st.WF → st.drawStep = 1 → st.nextUp c = true → (c ∈ st.stock ∨ c ∈ st.waste) →
    ∀ π w, π.length ≤ n → st.run π = some w → w.isWin = true →
      ∃ π' v, st.run π' = some v ∧ v.isWin = true ∧ rungHeldUntilExit c π' := by
  intro n
  induction n with
  | zero =>
      intro st c hwf hds hrung hcyc π w hlen hrun hwin
      cases π with
      | nil =>
          exfalso
          have hr : st.run ([] : List Move) = some st := rfl
          rw [hr] at hrun
          injection hrun with hwst
          rw [← hwst] at hwin
          rw [inCycle_notisWin hwf hcyc] at hwin
          exact Bool.noConfusion hwin
      | cons m rest =>
          exfalso
          simp at hlen
  | succ n ih =>
      intro st c hwf hds hrung hcyc π w hlen hrun hwin
      cases π with
      | nil =>
          exfalso
          have hr : st.run ([] : List Move) = some st := rfl
          rw [hr] at hrun
          injection hrun with hwst
          rw [← hwst] at hwin
          rw [inCycle_notisWin hwf hcyc] at hwin
          exact Bool.noConfusion hwin
      | cons m rest =>
          obtain ⟨s₁, hstep, hrunrest⟩ := State.run_cons hrun
          by_cases hex : m.leavesWaste c = true
          · exact ⟨m :: rest, w, hrun, hwin, Or.inl hex⟩
          · by_cases hrn : m.lowersRung c = true
            · -- the worry sector
              cases m with
              | draw => exact Bool.noConfusion hrn
              | wasteToFound y => exact Bool.noConfusion hrn
              | wasteToTab y b' => exact Bool.noConfusion hrn
              | tabToFound y => exact Bool.noConfusion hrn
              | tabToTab y b' => exact Bool.noConfusion hrn
              | foundToTab x b =>
                  have hx : x.suit = c.suit := of_decide_eq_true hrn
                  cases rest with
                  | nil =>
                      exfalso
                      have hr : s₁.run ([] : List Move) = some s₁ := rfl
                      rw [hr] at hrunrest
                      injection hrunrest with hws
                      rw [← hws] at hwin
                      obtain ⟨-, -, hs₁⟩ := foundToTab_fires hstep
                      have hcyc₁ : c ∈ s₁.stock ∨ c ∈ s₁.waste := by
                        rcases hcyc with hcs | hcw
                        · left
                          rw [hs₁]
                          show c ∈ ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).stock
                          rw [putCard_stock, setFound_stock]
                          exact hcs
                        · right
                          rw [hs₁]
                          show c ∈ ((st.setFound x.suit (chop (st.found x.suit))).putCard x b).waste
                          rw [putCard_waste, setFound_waste]
                          exact hcw
                      rw [inCycle_notisWin (step_wf hwf hstep) hcyc₁] at hwin
                      exact Bool.noConfusion hwin
                  | cons m₂ rest' =>
                      by_cases hrestack : m₂ = Move.tabToFound x
                      · -- the adjacent window cancels; recurse two
                        -- moves shorter at the SAME state
                        subst hrestack
                        obtain ⟨s₂, hstep₂, hrunrest'⟩ := State.run_cons hrunrest
                        have hrtn : State.step s₁ (Move.tabToFound x) = some st :=
                          foundToTab_return hwf hstep
                        rw [hrtn] at hstep₂
                        injection hstep₂ with hs₂st
                        rw [← hs₂st] at hrunrest'
                        have hlen' : rest'.length ≤ n := by
                          simp at hlen
                          omega
                        exact ih st c hwf hds hrung hcyc rest' w hlen' hrunrest' hwin
                      · -- the spread window: the residue
                        exact draw1_worry_spread_residue hwf hds hrung hcyc hx hstep
                          hrestack hrunrest hwin
            · -- the clean sector: transfer the bundle, prepend the head
              have hfalse : m.lowersRung c = false := by
                cases hlb : m.lowersRung c with
                | true => exact absurd hlb hrn
                | false => rfl
              have hwf₁ : s₁.WF := step_wf hwf hstep
              have hds₁ : s₁.drawStep = 1 := by
                rw [step_drawStep_keep hstep, hds]
              -- the per-kind bundle transfers
              have bundle : s₁.nextUp c = true ∧ (c ∈ s₁.stock ∨ c ∈ s₁.waste) := by
                cases m with
                | draw =>
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [stepDraw_found hstep]
                    refine ⟨?_, draw_inCycle hstep hcyc⟩
                    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                    rw [hfc]
                    exact hrung
                | wasteToFound y =>
                    obtain ⟨-, hny, w', hw, hs⟩ := wasteToFound_fires hstep
                    -- y ≠ c, or the head would have been the exit
                    have hne : y ≠ c := by
                      intro hcon
                      apply hex
                      show Move.leavesWaste c (Move.wasteToFound y) = true
                      rw [show Move.leavesWaste c (Move.wasteToFound y) = decide (y = c) from rfl,
                        hcon]
                      exact decide_eq_true rfl
                    -- y's suit cannot be c's (the rung pins it), so
                    -- the raise does not touch c's foundation slot
                    have hys : y.suit ≠ c.suit := by
                      intro hcon
                      exact hne (sameRung_eq hny hrung hcon)
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show (st.setFound y.suit (st.found y.suit ++ [y])).found c.suit = _
                      exact setFound_found_ne (Ne.symm hys)
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ (st.setFound y.suit (st.found y.suit ++ [y])).stock
                        rw [setFound_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ w'
                        rw [hw] at hcw
                        rcases List.mem_cons.mp hcw with he | hm
                        · exact absurd he.symm hne
                        · exact hm
                | wasteToTab y b' =>
                    obtain ⟨-, -, w', hw, hs⟩ := wasteToTab_fires hstep
                    have hne : y ≠ c := by
                      intro hcon
                      apply hex
                      show Move.leavesWaste c (Move.wasteToTab y b') = true
                      rw [show Move.leavesWaste c (Move.wasteToTab y b') = decide (y = c) from rfl,
                        hcon]
                      exact decide_eq_true rfl
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show (st.putCard y b').found c.suit = _
                      rw [putCard_found]
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ (st.putCard y b').stock
                        rw [putCard_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ w'
                        rw [hw] at hcw
                        rcases List.mem_cons.mp hcw with he | hm
                        · exact absurd he.symm hne
                        · exact hm
                | tabToFound y =>
                    obtain ⟨hny, a, ha⟩ := tabToFound_fires hstep
                    have hs := tabToFound_shape hstep ha
                    rcases Decidable.em (y.suit = c.suit) with hcon | hcon
                    · exfalso
                      have hyc : y = c := sameRung_eq hny hrung hcon
                      rw [hyc] at ha
                      obtain ⟨-, hlast⟩ := pileOfTop_top ha
                      have hmem : c ∈ (st.piles a).faceUp := lastOf_mem hlast
                      rcases hcyc with hcs | hcw
                      · exact ((mem_stock_unique hwf hcs).1 a).2 hmem
                      · exact ((mem_waste_unique hwf hcw).1 a).2 hmem
                    · have hfc : s₁.found c.suit = st.found c.suit := by
                        rw [hs]
                        show (st.setFound y.suit (st.found y.suit ++ [y])).found c.suit = _
                        exact setFound_found_ne (Ne.symm hcon)
                      constructor
                      · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                        rw [hfc]
                        exact hrung
                      · rcases hcyc with hcs | hcw
                        · left
                          rw [hs]
                          show c ∈ (st.setFound y.suit (st.found y.suit ++ [y])).stock
                          rw [setFound_stock]
                          exact hcs
                        · right
                          rw [hs]
                          show c ∈ (st.setFound y.suit (st.found y.suit ++ [y])).waste
                          rw [setFound_waste]
                          exact hcw
                | foundToTab y b' =>
                    obtain ⟨-, hcp, hs⟩ := foundToTab_fires hstep
                    -- clean means the rung fact: y's suit is not c's
                    have hys : y.suit ≠ c.suit := by
                      intro hcon
                      rw [show Move.lowersRung c (Move.foundToTab y b') =
                        decide (y.suit = c.suit) from rfl, hcon] at hfalse
                      exact Bool.noConfusion (hfalse.symm.trans (decide_eq_true rfl))
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show ((st.setFound y.suit (chop (st.found y.suit))).putCard y b').found c.suit = _
                      rw [putCard_found, setFound_found_ne (Ne.symm hys)]
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ ((st.setFound y.suit (chop (st.found y.suit))).putCard y b').stock
                        rw [putCard_stock, setFound_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ ((st.setFound y.suit (chop (st.found y.suit))).putCard y b').waste
                        rw [putCard_waste, setFound_waste]
                        exact hcw
                | tabToTab y b' =>
                    obtain ⟨a, -, -, hs⟩ := tabToTab_fires hstep
                    have hfc : s₁.found c.suit = st.found c.suit := by
                      rw [hs]
                      show ((st.setPile a
                          (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
                          (fromCard y (st.piles a).faceUp) b').found c.suit = _
                      rw [putRun_found, setPile_found]
                    constructor
                    · show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
                      rw [hfc]
                      exact hrung
                    · rcases hcyc with hcs | hcw
                      · left
                        rw [hs]
                        show c ∈ ((st.setPile a
                            (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
                            (fromCard y (st.piles a).faceUp) b').stock
                        rw [putRun_stock, setPile_stock]
                        exact hcs
                      · right
                        rw [hs]
                        show c ∈ ((st.setPile a
                            (Pile.afterRunRemoved (st.piles a) (below y (st.piles a).faceUp))).putRun
                            (fromCard y (st.piles a).faceUp) b').waste
                        rw [putRun_waste, setPile_waste]
                        exact hcw
              obtain ⟨hrung₁, hcyc₁⟩ := bundle
              have hlen' : rest.length ≤ n := by
                simp at hlen
                omega
              obtain ⟨π', v, hrun', hwin', hcomp'⟩ :=
                ih s₁ c hwf₁ hds₁ hrung₁ hcyc₁ rest w hlen' hrunrest hwin
              refine ⟨m :: π', v, ?_, hwin', Or.inr ⟨hfalse, hcomp'⟩⟩
              show (match State.step st m with
                | some st' => State.run st' π'
                | none => none) = some v
              rw [hstep]
              exact hrun'

set_option linter.unusedVariables false in
/-- **(C) The normal form**: a winning play exists that keeps the
c-rung until `c` leaves the waste — B&G's safemoves discipline.  Any
pre-exit worry of `c`'s suit is the suit's foundation-top card; its
restack (`tabToFound`) must fire before the suit climbs again, and
the pair is either adjacent (cancel through the foundation round
trip — `tabToFound_undo_under` at the top, or `_bare`) or closes by
the same exchanges as (B)'s squares; the storage shape (a placement
onto the vacated seat) is the bare-floor residue's own assembly at
the worry-created seat — the shared [GAP] family.

PROVEN SKELETON (the (C) farm row, 2026-10-10): the case split is
`normform_aux`'s — the empty play and the lone worry die on the
cycle's win-blockade (`inCycle_notisWin`), an exit head is compliant
verbatim, a clean head recurses on the transferred bundle, and the
adjacent window `[foundToTab x b; tabToFound x]` cancels through the
proven `foundToTab_return` (the two-step worry-undo — the undo
family's round-trip identity at WF), recursing two moves shorter at
the same state.  Every spread window — worry first, a non-restack
second — routes to the ONE named residue `draw1_worry_spread_residue`
above: the residue's route note owns the window accounting (the §12.1
first-passage gap), the window squares (the landed `draw` /
`wasteToFound` privates and the corner-shaped remainder), and the
storage prong's `tabToFound_dominant_of_ground` citation (the (N)
stub — that taint is expected and named).  `hsafe` is consumed by
the residue's storage prong, not by the proven skeleton:
`safeToFound` does not survive an arbitrary clean prefix (an
other-suit worry-back can tighten a height bound), which is why the
engine's invariant carries only the rung-cycle bundle.  (The linter
is silenced below: `hsafe` is a FINAL premise of the statement — the
residue's storage prong consumes it; the proven skeleton does not.)
-/
theorem draw1_compliant_normalForm {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hsafe : safeToFound st c = true)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock)
    (hsolv : WinFrom st) :
    ∃ π w, st.run π = some w ∧ w.isWin = true ∧ rungHeldUntilExit c π := by
  obtain ⟨π, w, hrun, hwin⟩ := hsolv
  exact normform_aux π.length st c hwf hstep hrung (Or.inl hstock) π w (Nat.le_refl _)
    hrun hwin

/-- **§5.3, physical form (draw-1)**: with one card per draw, the safe
stack of a stocked rung card can be front-loaded as a plain deal-out
and stack — no play loses by it.  PROVEN given the named stubs (C)
then (B) (with the reserve lemma (A) inside (B)'s transports). -/
theorem stock_dominance_draw1 {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hsafe : safeToFound st c = true)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock)
    (hsolv : WinFrom st) :
    ∃ k s', st.run (List.replicate k Move.draw ++ [Move.wasteToFound c]) = some s' ∧
      WinFrom s' := by
  obtain ⟨π, w, hrun, hwin, hcomp⟩ :=
    draw1_compliant_normalForm hwf hstep hsafe hrung hstock hsolv
  exact draw1_compliant_replay hwf hstep hrung hstock π w hcomp hrun hwin

/-! ## §5.2 — The suit-grade worry gate (the worry-preference dominance)

method.md §5.4's worry gate, the SUIT-GRADE half, formalized as the
`prunableAt` theorem on the physical model.  The gate being certified
is `src/state.rs gen_moves`'s `suit_filter` cascade (state.rs:250-318):
at a node whose tableau carries pending stackable work, the worry
moves `stack_pile` (the Rust stack→pile move — THIS model's
`Move.foundToTab c b`, the foundation-top worry-back — see the header
table above) are offered ONLY for the suits `s` whose TWIN suit is not
live:

```
extra        = redundant_stack | (vis & sm & (least << 4))
suit_unstack[s] := extra & SUIT_MASK[s] == 0        // per suit
suit_filter  = ⋃_{suit_unstack[t]} SUIT_MASK[twin t] // twin's channel
stack_pile   = stack_pile & suit_filter & ...        // the offer
```

Per suit, `extra` reads content that is committable NOW
(`redundant_stack`: a tableau top that is foundation-ready and whose
raise reveals nothing) or committable AT A PENDING MOMENT
(`vis & sm & (least << 4)`: the suit's next card sits exposed face-up
exactly one rank above a zero-reveal pending commit of the twin suit —
after that commit lands, the suit's own channel opens).  Both
readings are defined below (`suitCommitNow`, `suitExposesNext`) and
composed as `suitLive` — the two readings do not differ as competing
translations; they are the two disjuncts of the ONE Rust formula, and
each is separately decide-probed at the craft states of the probe
battery below.

**SUIT-GRADE, not rank-graded** — a deliberate session decision: the
solver's gate is the stateless whole-suit reading (`extra`-per-suit),
not the rank-indexed variant (rejected this session); accordingly
`suitLive` drops the cascade's which-card specificity (`least_stack`,
the lex-least pending commit) — ANY same-shape pending commit
witnesses liveness statelessly.

**Out of scope, documented, NOT certified here** (the cascade is
interaction-tuned; this card certifies the suit-grade gate in
isolation): the `paired_stack` lex-least restriction
(state.rs:255-268 — no twin-pair of equal-rank stackable cards may
co-fire; the lower siblings collapse), the both-colors-unstack
opening condition (state.rs:278), the `triple_stackable` guard, and
the `(least_stack - 1)` rank cap (state.rs:305 — a worry move is also
rank-fenced to strictly below the pending least stack).  Those rows
are the cascade's own dominances; the theorem below is the gate
CERTIFICATION: whenever the twin suit is live, the worry the gate
suppresses is prunable — the pruning the production Rust solver
already performs never costs a win.

**The theorem shape.**  `prunableAt st m` here is the strong,
whole-play reading — SOME winning play from `st` avoids `m` ENTIRELY
(the Klondike twin chapter's `prunableAt` reads head-avoidance only;
naming mirrors, shape is this chapter's own, per the card).  The
premises are `WF` and the gate premise alone; the move's own legality
at `st` is NOT assumed (the engine treats every occurrence).

**The route (the staged ledger).**

* Part (i) — the commit-first sequentialization — is LANDED as
  PROVEN content at both grades: the mechanical square
  `raise_worry_square` (a twin-anchored `tabToFound` raise and a
  `foundToTab` worry at distinct suits are COMPOSITE-EQUAL under the
  one order-lock corner `b ≠ inr y`), and its play-level corollary
  `stackPile_worry_sequence`: an adjacent worry-then-raise window in
  a winning play replays as raise-then-worry — accommodate the live
  suit first; it is no longer stackable; then the gate itself opens
  the twin worry.  The both-constructions case SEQUENCES; it does not
  violate the gate.
* Part (ii) — the single-pad twin exchange and part (iii) — the
  interference squares — are the spread residue's OWN route: after
  the engine has settled everything mechanical, a surviving worry
  occurrence is a spread window, and the residue owes the twin-equal
  rewrite through `twin_fate`
  (`Orig/Twin.lean`) at the exposure moment — the worried card's
  downstream uses carried by the twin-twin conjugation
  (`Move.twinMove`/`State.twinMap`, the `TwinExchangeBoth` local
  exchange grades) — with the C-session's composite-equal squares
  (`foundToTab_wasteToFound_square`, `bump2_comm`,
  `lower_foundToTab1`, the fires-readers) as the bubbling legs, LIFO
  per the banked square inventory (worry-worry pairs never square;
  the storage corner — a segment parking onto the worry-created seat —
  is the genuine hard core, decide-exhibited below).

**The engine (`worry_elim`, private).**  Strong induction on the
play length at the FIRST worry occurrence:

* no occurrence — the play verbatim;
* the worry is the play's LAST move — impossible: the raised-away
  foundation leaves its suit short of thirteen against `isWin`
  (`wf_found_chop_toIdx` against `isWin_len`), a PROVEN corner;
* the occurrence is an adjacent worry/restack window
  `[foundToTab c b; tabToFound c]` — the window composites to the
  identity (`foundToTab_return`), the pair is excised, and the
  induction continues TWO MOVES SHORTER;
* the occurrence is a spread window (the follow-move is not the
  restack) — the residue's instance, delivered with the gated root
  and the reached window state.

The capstone assembles: `stackPile_worry_prunableAt`. -/

/-! ### The framework transplant (the Klondike mirror, naming verbatim) -/

/-- Playing `m` at `st` never hurts: the verdict survives the move.
`Klondike/Dominance.lean`'s `dominantAt`, mirrored at the physical
game (`WinFrom` for `solvableFrom`, `State.step` for `apply`). -/
def dominantAt (st : State) (m : Move) : Prop :=
  WinFrom st → ∃ s₁, State.step st m = some s₁ ∧ WinFrom s₁

/-- SOME winning play from `st` avoids `m` ENTIRELY — the
whole-play, suit-grade reading of prunability (the Klondike twin
chapter reads head-avoidance; the stateless whole-suit gate the
solver runs demands the whole-play form). -/
def prunableAt (st : State) (m : Move) : Prop :=
  WinFrom st → ∃ play w, st.run play = some w ∧ w.isWin = true ∧
    ∀ m' ∈ play, m' ≠ m

/-- `m` dominates `m'` at `st`: prune `m'`, prefer `m`. -/
def dominates (st : State) (m m' : Move) : Prop :=
  prunableAt st m' ∧ dominantAt st m

/-! ### The suit readings (the `extra`-per-suit formula) -/

/-- **Reading one — committable now** (`redundant_stack` per suit,
faithful): the suit `s` has a tableau-top card that is
foundation-ready (`nextUp`) and whose raise reveals nothing (the
below-run is nonempty or the hidden boundary is already empty —
`Pile.afterRunRemoved` flips no card). -/
def suitCommitNow (s : Suit) (st : State) : Bool :=
  Anchor.all.any fun a =>
    match (st.piles a).top with
    | some x => decide (x.suit = s) && st.nextUp x &&
        (decide (chop (st.piles a).faceUp ≠ []) || decide ((st.piles a).hidden = []))
    | none => false

/-- **Reading two — committable at the pending moment**
(`vis & sm & (least << 4)` per suit, faithful): the suit's NEXT card
(one rank above a zero-reveal pending commit of the TWIN suit,
exposed face-up somewhere on the board) — after the pending commit
lands the suit's own channel opens; the lex-least WHICH-pending
specificity of the cascade is dropped, statelessly. -/
def suitExposesNext (s : Suit) (st : State) : Bool :=
  Anchor.all.any fun a =>
    (st.piles a).faceUp.any fun x =>
      decide (x.suit = s) && st.nextUp x &&
        Anchor.all.any fun a' =>
          match (st.piles a').top with
          | some y => decide (y.suit.twin = s) &&
              decide (y.rank.toIdx + 1 = x.rank.toIdx) && st.nextUp y &&
                (decide (chop (st.piles a').faceUp ≠ []) ||
                  decide ((st.piles a').hidden = []))
          | none => false

/-- **The suit-grade liveness the gate reads** (the whole `extra`
formula, stateless and whole-suit by the session's decision):
`s` has committable-now or committable-at-the-pending-moment content.
The Rust gate offers a suit-`s` worry ONLY when `suitLive s.twin` is
false; the capstone below certifies the complementary direction:
when the twin IS live, the worry is prunable. -/
def suitLive (s : Suit) (st : State) : Bool :=
  suitCommitNow s st || suitExposesNext s st

/-! ### The mechanical kit (the engine's private strip) -/

/-- The first-occurrence surgery: a play either avoids `m`
throughout, or splits at its first occurrence with a clean prefix. -/
private theorem mem_avoid_or_first {m : Move} : ∀ (π : List Move),
    (∀ m' ∈ π, m' ≠ m) ∨ ∃ A B, π = A ++ m :: B ∧ ∀ m' ∈ A, m' ≠ m := by
  intro π
  induction π with
  | nil => exact Or.inl (by simp)
  | cons x t ih =>
      by_cases hx : x = m
      · refine Or.inr ⟨[], t, ?_, by simp⟩
        rw [hx]
        rfl
      · rcases ih with hclean | ⟨A, B, hπ, hA⟩
        · refine Or.inl ?_
          intro m' hm'
          rcases List.mem_cons.mp hm' with heq | hmem
          · rw [heq]; exact hx
          · exact hclean m' hmem
        · refine Or.inr ⟨x :: A, B, ?_, ?_⟩
          · rw [hπ]
            rfl
          · intro m' hm'
            rcases List.mem_cons.mp hm' with heq | hmem
            · rw [heq]; exact hx
            · exact hA m' hmem

/-- The run-prefix WF chain. -/
private theorem run_wf (A : List Move) :
    ∀ {st u : State}, st.run A = some u → st.WF → u.WF := by
  induction A with
  | nil =>
      intro st u h hwf
      have hx : (some st : Option State) = some u := h
      have hsu : st = u := Option.some.inj hx
      rw [hsu] at hwf
      exact hwf
  | cons m rest ih =>
      intro st u h hwf
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      exact ih hrest (step_wf hwf hstep)

/-- The prefix/tail split of a run. -/
private theorem run_app_split : ∀ (A : List Move) (st : State) (B : List Move) (w : State),
    st.run (A ++ B) = some w → ∃ u, st.run A = some u ∧ u.run B = some w := by
  intro A
  induction A with
  | nil =>
      intro st B w h
      exact ⟨st, rfl, h⟩
  | cons m rest ih =>
      intro st B w h
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h
      obtain ⟨u, hu₁, hu₂⟩ := ih s₁ B w hrest
      refine ⟨u, ?_, hu₂⟩
      show (match State.step st m with
        | some st' => State.run st' rest
        | none => none) = _
      rw [hstep]
      exact hu₁

/-- The prefix/tail glue of a run. -/
private theorem run_app_glue : ∀ (A : List Move) (st u w : State) (B : List Move),
    st.run A = some u → u.run B = some w → st.run (A ++ B) = some w := by
  intro A
  induction A with
  | nil =>
      intro st u w B h1 h2
      have hx : (some st : Option State) = some u := h1
      have hsu : st = u := Option.some.inj hx
      rw [hsu]
      exact h2
  | cons m rest ih =>
      intro st u w B h1 h2
      obtain ⟨s₁, hstep, hrest⟩ := State.run_cons h1
      show st.run ((m :: rest) ++ B) = _
      rw [show (m :: rest) ++ B = m :: (rest ++ B) from rfl]
      show (match State.step st m with
        | some st' => State.run st' (rest ++ B)
        | none => none) = _
      rw [hstep]
      exact ih s₁ u w B hrest h2

/-! ### Part (i) — the sequencing square

The composite-equal square for the raise-vs-worry pair — the (iii)
bank's `tabToFound` slot (the C-session squares covered the waste
entries; this is the twin-anchored raise): at DISTINCT suits with the
one order-lock corner barred (`b = inr y` — the raise consumes the
worry's own base card; decide-exhibited in the probe battery), both
orders land at the SAME composite.  The proof promotes the raise's
guards and seat to the pre-worry state through the readers
(`setFound`/`putCard`/`firstWhere_congr`), the worry's guards to the
post-raise state, and closes the composite by `State.ext` — the same
channel as `foundToTab_wasteToFound_square`'s pattern-kernel. -/

/-- The mechanical square: a `tabToFound y` raise and a
`foundToTab c b` worry at distinct suits, no inter-suite corner in the
worry's base, compose the same successor state in both orders. -/
private theorem raise_worry_square {st : State} {c y : Card} {b : Base} {s₁ t : State}
    (hwf : st.WF) (hsy : y.suit ≠ c.suit) (hcorn : b ≠ Sum.inr y)
    (hf : State.step st (Move.foundToTab c b) = some s₁)
    (hm : State.step s₁ (Move.tabToFound y) = some t) :
    ∃ r, State.step st (Move.tabToFound y) = some r ∧
      State.step r (Move.foundToTab c b) = some t := by
  obtain ⟨htop, hcp, hs₁⟩ := foundToTab_fires hf
  obtain ⟨hny, ky, hky⟩ := tabToFound_fires hm
  have hcy : y ≠ c := by
    intro h
    exact hsy (by rw [h])
  have hsc : c.suit ≠ y.suit := by
    intro h
    exact hsy h.symm
  have hsf : ∀ σ, s₁.found σ =
      (if σ = c.suit then chop (st.found c.suit) else st.found σ) := by
    intro σ
    rw [hs₁, putCard_found]
    by_cases hσ : σ = c.suit
    · rw [ite_eq_left hσ, hσ, setFound_found_self]
    · rw [ite_eq_right hσ, setFound_found_ne hσ]
  have hs₁y : s₁.found y.suit = st.found y.suit := by
    rw [hsf y.suit, ite_eq_right hsy]
  have hny' : st.nextUp y = true := by
    show (decide (y.rank.toIdx = (st.found y.suit).length)) = true
    have h : (decide (y.rank.toIdx = (s₁.found y.suit).length)) = true := hny
    rw [hs₁y] at h
    exact h
  cases b with
  | inl a =>
      obtain ⟨hempty, hking⟩ := canPlace_inl hcp
      have hsp : ∀ a', s₁.piles a' =
          (if a' = a then (⟨[], [c]⟩ : Pile) else st.piles a') := by
        intro a'
        rw [hs₁]
        have hp := putCard_piles_inl (st.setFound c.suit (chop (st.found c.suit))) c a
        have h := congrFun hp a'
        rw [h]
        show (if a' = a then (⟨[], [c]⟩ : Pile)
            else (st.setFound c.suit (chop (st.found c.suit))).piles a') = _
        by_cases haa : a' = a
        · rw [haa, ite_eq_left rfl, ite_eq_left rfl]
        · rw [ite_eq_right haa, ite_eq_right haa, setFound_piles]
      have hkne : ky ≠ a := by
        intro hka
        have hlasty := (pileOfTop_top hky).2
        have h := hsp ky
        rw [ite_eq_left hka] at h
        have hlastc : lastOf (s₁.piles ky).faceUp = some c :=
          congrArg (fun p => lastOf p.faceUp) h
        rw [hlastc] at hlasty
        exact hcy (Option.some.inj hlasty).symm
      have hs₁k : s₁.piles ky = st.piles ky := by
        have h := hsp ky
        rw [ite_eq_right hkne] at h
        exact h
      have hstyk : (st.piles ky).top = some y := by
        have hlasty := (pileOfTop_top hky).2
        show lastOf (st.piles ky).faceUp = some y
        rw [← hs₁k]
        exact hlasty
      have hstky : st.pileOfTop y = some ky :=
        (pileOfTop_eq_some_iff hwf).mpr hstyk
      obtain ⟨r, hrdef⟩ : ∃ r : State, r = { st.setFound y.suit (st.found y.suit ++ [y]) with
        piles := fun a' => if a' = ky then
            Pile.afterRunRemoved (st.piles ky) (chop (st.piles ky).faceUp)
          else st.piles a' } := ⟨_, rfl⟩
      have hrspec : State.step st (Move.tabToFound y) = some r := by
        rw [hrdef]
        exact tabToFound_fires_eq hny' hstky
      have hrp : ∀ a', r.piles a' =
          (if a' = ky then Pile.afterRunRemoved (st.piles ky) (chop (st.piles ky).faceUp)
            else st.piles a') := by
        intro a'
        rw [hrdef]
      have hwfr : r.WF := step_wf hwf hrspec
      have hrfc : r.found c.suit = st.found c.suit := by
        rw [hrdef]
        exact setFound_found_ne hsc
      have htopr : r.foundTop c.suit = some c := by
        show lastOf (r.found c.suit) = some c
        rw [hrfc]
        exact htop
      have hpa : r.piles a = st.piles a := by
        have h := hrp a
        rw [ite_eq_right (Ne.symm hkne)] at h
        exact h
      have hcpr : r.canPlace c (Sum.inl a) = true := by
        simp only [State.canPlace, hpa, hempty, decide_eq_true hking, Bool.true_and]
      refine ⟨r, hrspec, ?_⟩
      have hworry : State.step r (Move.foundToTab c (Sum.inl a)) =
          some ((r.setFound c.suit (chop (r.found c.suit))).putCard c (Sum.inl a)) :=
        foundToTab_fires_eq htopr hcpr
      rw [hworry]
      have hshape : t = { s₁.setFound y.suit (s₁.found y.suit ++ [y]) with
        piles := fun a' => if a' = ky then
            Pile.afterRunRemoved (s₁.piles ky) (chop (s₁.piles ky).faceUp)
          else s₁.piles a' } := tabToFound_shape hm hky
      rw [hshape]
      refine congrArg some ?_
      apply State.ext
      · funext σ
        show ((r.setFound c.suit (chop (r.found c.suit))).putCard c (Sum.inl a)).found σ
          = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).found σ
        rw [putCard_found]
        by_cases hσc : σ = c.suit
        · rw [hσc, setFound_found_self, hrfc, setFound_found_ne hsc, hsf c.suit,
            ite_eq_left rfl]
        · by_cases hσy : σ = y.suit
          · rw [hσy, setFound_found_ne hsc.symm, hrdef, setFound_found_self,
              setFound_found_self, hs₁y]
          · rw [setFound_found_ne hσc, hrdef, setFound_found_ne hσy,
              setFound_found_ne hσy, hsf σ, ite_eq_right hσc]
      · funext a''
        have hp := putCard_piles_inl (r.setFound c.suit (chop (r.found c.suit))) c a
        have hL := congrFun hp a''
        rw [hL]
        show (if a'' = a then (⟨[], [c]⟩ : Pile)
            else (r.setFound c.suit (chop (r.found c.suit))).piles a'') =
          (if a'' = ky then Pile.afterRunRemoved (s₁.piles ky) (chop (s₁.piles ky).faceUp)
            else s₁.piles a'')
        rw [setFound_piles, hrp a'']
        by_cases haky : a'' = ky
        · rw [haky, ite_eq_right hkne, ite_eq_left rfl, ite_eq_left rfl, hs₁k]
        · by_cases haa : a'' = a
          · rw [haa, ite_eq_left rfl, ite_eq_right (Ne.symm hkne), hsp a, ite_eq_left rfl]
          · rw [ite_eq_right haa, ite_eq_right haky, ite_eq_right haky, hsp a'',
              ite_eq_right haa]
      · rw [putCard_stock, setFound_stock, hrdef]
        show (st.setFound y.suit (st.found y.suit ++ [y])).stock = _
        rw [setFound_stock]
        show st.stock = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).stock
        rw [setFound_stock, hs₁, putCard_stock, setFound_stock]
      · rw [putCard_waste, setFound_waste, hrdef]
        show (st.setFound y.suit (st.found y.suit ++ [y])).waste = _
        rw [setFound_waste]
        show st.waste = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).waste
        rw [setFound_waste, hs₁, putCard_waste, setFound_waste]
      · rw [putCard_drawStep, setFound_drawStep, hrdef]
        show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = _
        rw [setFound_drawStep]
        show st.drawStep = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).drawStep
        rw [setFound_drawStep, hs₁, putCard_drawStep, setFound_drawStep]
  | inr z =>
      obtain ⟨k_z, hz, hfit⟩ := canPlace_inr hcp
      have hyz : y ≠ z := by
        intro h
        rw [← h] at hcorn
        exact hcorn rfl
      have hzp' : (st.setFound c.suit (chop (st.found c.suit))).pileOfTop z = some k_z := by
        have hcc : firstWhere (fun a'' =>
              decide (((st.setFound c.suit (chop (st.found c.suit))).piles a'').top = some z))
              Anchor.all =
            firstWhere (fun a'' => decide ((st.piles a'').top = some z)) Anchor.all :=
          firstWhere_congr (fun _ => rfl)
        show firstWhere (fun a'' =>
              decide (((st.setFound c.suit (chop (st.found c.suit))).piles a'').top = some z))
              Anchor.all = some k_z
        rw [hcc]
        show st.pileOfTop z = some k_z
        exact hz
      have hsp : ∀ a', s₁.piles a' =
          (if a' = k_z then { st.piles k_z with faceUp := (st.piles k_z).faceUp ++ [c] }
            else st.piles a') := by
        intro a'
        rw [hs₁]
        have hp := putCard_piles_inr (st.setFound c.suit (chop (st.found c.suit))) c z k_z hzp'
        have h := congrFun hp a'
        rw [h]
        show (if a' = k_z then { st.piles k_z with faceUp := (st.piles k_z).faceUp ++ [c] }
            else (st.setFound c.suit (chop (st.found c.suit))).piles a') = _
        rw [setFound_piles]
      have hkkz : ky ≠ k_z := by
        intro h
        have hlasty := (pileOfTop_top hky).2
        have hface : (s₁.piles ky).faceUp = (st.piles k_z).faceUp ++ [c] := by
          have hp := hsp k_z
          rw [← h] at hp
          rw [ite_eq_left rfl] at hp
          rw [hp, ← h]
        have hlastc : lastOf (s₁.piles ky).faceUp = some c := by
          rw [hface]
          exact lastOf_snoc
        rw [hlastc] at hlasty
        exact hcy (Option.some.inj hlasty).symm
      have hs₁k : s₁.piles ky = st.piles ky := by
        have h := hsp ky
        rw [ite_eq_right hkkz] at h
        exact h
      have hstyk : (st.piles ky).top = some y := by
        have hlasty := (pileOfTop_top hky).2
        show lastOf (st.piles ky).faceUp = some y
        rw [← hs₁k]
        exact hlasty
      have hstky : st.pileOfTop y = some ky :=
        (pileOfTop_eq_some_iff hwf).mpr hstyk
      obtain ⟨r, hrdef⟩ : ∃ r : State, r = { st.setFound y.suit (st.found y.suit ++ [y]) with
        piles := fun a' => if a' = ky then
            Pile.afterRunRemoved (st.piles ky) (chop (st.piles ky).faceUp)
          else st.piles a' } := ⟨_, rfl⟩
      have hrspec : State.step st (Move.tabToFound y) = some r := by
        rw [hrdef]
        exact tabToFound_fires_eq hny' hstky
      have hrp : ∀ a', r.piles a' =
          (if a' = ky then Pile.afterRunRemoved (st.piles ky) (chop (st.piles ky).faceUp)
            else st.piles a') := by
        intro a'
        rw [hrdef]
      have hwfr : r.WF := step_wf hwf hrspec
      have hrfc : r.found c.suit = st.found c.suit := by
        rw [hrdef]
        exact setFound_found_ne hsc
      have htopr : r.foundTop c.suit = some c := by
        show lastOf (r.found c.suit) = some c
        rw [hrfc]
        exact htop
      have hrnk : (r.piles ky).top ≠ some z := by
        intro hcon
        have h1 : r.pileOfTop z = some ky := (pileOfTop_eq_some_iff hwfr).mpr hcon
        have h2 : (r.piles k_z).top = some z := by
          have hp := hrp k_z
          rw [ite_eq_right (Ne.symm hkkz)] at hp
          rw [hp]
          exact (pileOfTop_eq_some_iff hwf).mp hz
        have h3 : r.pileOfTop z = some k_z := (pileOfTop_eq_some_iff hwfr).mpr h2
        rw [h3] at h1
        exact absurd (Option.some.inj h1) (Ne.symm hkkz)
      have hpcongr : ∀ (a' : Anchor),
          (decide ((st.piles a').top = some z)) =
          (decide ((r.piles a').top = some z)) := by
        intro a'
        by_cases hak : a' = ky
        · rw [hak, hstyk]
          have h1 : decide (some y = some z) = false :=
            decide_false_of_not (fun heq => hyz (Option.some.inj heq))
          have h2 : decide ((r.piles ky).top = some z) = false :=
            decide_false_of_not (fun heq => hrnk heq)
          rw [h1, h2]
        · rw [hrp a', ite_eq_right hak]
      have hrzz : r.pileOfTop z = st.pileOfTop z := by
        show (firstWhere (fun a' => decide ((r.piles a').top = some z)) Anchor.all
            = firstWhere (fun a' => decide ((st.piles a').top = some z)) Anchor.all)
        exact (firstWhere_congr hpcongr).symm
      have hcpr : r.canPlace c (Sum.inr z) = true := by
        show (match r.pileOfTop z with
          | some _ => canSitOn c z
          | none => false) = true
        rw [hrzz, hz]
        exact hfit
      refine ⟨r, hrspec, ?_⟩
      have hworry : State.step r (Move.foundToTab c (Sum.inr z)) =
          some ((r.setFound c.suit (chop (r.found c.suit))).putCard c (Sum.inr z)) :=
        foundToTab_fires_eq htopr hcpr
      rw [hworry]
      have hshape : t = { s₁.setFound y.suit (s₁.found y.suit ++ [y]) with
        piles := fun a' => if a' = ky then
            Pile.afterRunRemoved (s₁.piles ky) (chop (s₁.piles ky).faceUp)
          else s₁.piles a' } := tabToFound_shape hm hky
      rw [hshape]
      refine congrArg some ?_
      apply State.ext
      · funext σ
        show ((r.setFound c.suit (chop (r.found c.suit))).putCard c (Sum.inr z)).found σ
          = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).found σ
        rw [putCard_found]
        by_cases hσc : σ = c.suit
        · rw [hσc, setFound_found_self, hrfc, setFound_found_ne hsc, hsf c.suit,
            ite_eq_left rfl]
        · by_cases hσy : σ = y.suit
          · rw [hσy, setFound_found_ne hsc.symm, hrdef, setFound_found_self,
              setFound_found_self, hs₁y]
          · rw [setFound_found_ne hσc, hrdef, setFound_found_ne hσy,
              setFound_found_ne hσy, hsf σ, ite_eq_right hσc]
      · funext a''
        have hzr' : (r.setFound c.suit (chop (r.found c.suit))).pileOfTop z = some k_z := by
          have hcc : firstWhere (fun a'' =>
                decide (((r.setFound c.suit (chop (r.found c.suit))).piles a'').top = some z))
                Anchor.all =
              firstWhere (fun a'' => decide ((r.piles a'').top = some z)) Anchor.all :=
            firstWhere_congr (fun _ => rfl)
          show firstWhere (fun a'' =>
                decide (((r.setFound c.suit (chop (r.found c.suit))).piles a'').top = some z))
                Anchor.all = some k_z
          rw [hcc]
          show r.pileOfTop z = some k_z
          rw [hrzz]
          exact hz
        have hp := putCard_piles_inr (r.setFound c.suit (chop (r.found c.suit))) c z k_z hzr'
        have hL := congrFun hp a''
        rw [hL]
        show (if a'' = k_z then { r.piles k_z with faceUp := (r.piles k_z).faceUp ++ [c] }
            else (r.setFound c.suit (chop (r.found c.suit))).piles a'') =
          (if a'' = ky then Pile.afterRunRemoved (s₁.piles ky) (chop (s₁.piles ky).faceUp)
            else s₁.piles a'')
        rw [setFound_piles, hrp a'']
        by_cases haky : a'' = ky
        · rw [haky, ite_eq_right hkkz, ite_eq_left rfl, ite_eq_left rfl, hs₁k]
        · by_cases hzak : a'' = k_z
          · rw [hzak, ite_eq_left rfl, ite_eq_right (Ne.symm hkkz), hrp k_z,
              ite_eq_right (Ne.symm hkkz), hsp k_z, ite_eq_left rfl]
          · rw [ite_eq_right hzak, ite_eq_right haky, ite_eq_right haky, hsp a'',
              ite_eq_right hzak]
      · rw [putCard_stock, setFound_stock, hrdef]
        show (st.setFound y.suit (st.found y.suit ++ [y])).stock = _
        rw [setFound_stock]
        show st.stock = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).stock
        rw [setFound_stock, hs₁, putCard_stock, setFound_stock]
      · rw [putCard_waste, setFound_waste, hrdef]
        show (st.setFound y.suit (st.found y.suit ++ [y])).waste = _
        rw [setFound_waste]
        show st.waste = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).waste
        rw [setFound_waste, hs₁, putCard_waste, setFound_waste]
      · rw [putCard_drawStep, setFound_drawStep, hrdef]
        show (st.setFound y.suit (st.found y.suit ++ [y])).drawStep = _
        rw [setFound_drawStep]
        show st.drawStep = (s₁.setFound y.suit (s₁.found y.suit ++ [y])).drawStep
        rw [setFound_drawStep, hs₁, putCard_drawStep, setFound_drawStep]

/-- **The both-constructions sequencing (part i, public).**  An
adjacent `[worry; raise]` window in a winning play replays with the
raise FIRST — win-preserved, the two-moves-shorter-rest verbatim.
The square makes the swap composite-equal, so the gate's own reading
holds: accommodate the live suit first; the raised card is no longer
stackable; THEN the gate itself opens the twin worry.  The
order-locked corner (`b = inr y`) is barred by `hcorn` — its
decide-anchored exhibit lives in the probe battery below. -/
theorem stackPile_worry_sequence {u : State} {c y : Card} {b : Base}
    {rest : List Move} {w : State}
    (hwf : u.WF) (hsy : y.suit ≠ c.suit) (hcorn : b ≠ Sum.inr y)
    (hfin : u.run (Move.foundToTab c b :: Move.tabToFound y :: rest) = some w) :
    u.run (Move.tabToFound y :: Move.foundToTab c b :: rest) = some w := by
  obtain ⟨s₁, h1, hrest⟩ := State.run_cons hfin
  obtain ⟨t, h2, htail⟩ := State.run_cons hrest
  obtain ⟨r, hr1, hr2⟩ := raise_worry_square hwf hsy hcorn h1 h2
  show (match State.step u (Move.tabToFound y) with
    | some st' => State.run st' (Move.foundToTab c b :: rest)
    | none => none) = _
  rw [hr1]
  show (match State.step r (Move.foundToTab c b) with
    | some st' => State.run st' rest
    | none => none) = _
  rw [hr2]
  exact htail

/-! ### The named residue (the spread window) -/

/-- **The spread residue — the card's ONE named stub.**

The engine below reduces the whole-pruned question to this shape: a
first-occurrence worry window `[m; m₂]` with `m₂` other than the
restack — a winning play from the window state through the worry,
inside a play from the gated root.  The stub owes the m-avoiding
winning play FROM THE GATED ROOT.

**Route (the staged ledger, per the overnight banks):**

* **(i) residue input, pre-sequenced.**  When the window's `m₂` is a
  `tabToFound y` of the twin suit, `stackPile_worry_sequence` swaps
  the window to raise-first — the both-constructions case sequences
  rather than derailing; iterate while adjacent twin raises remain
  (bounded: each swap raises the twin foundation; the pair
  `paired_stack` lex-least restriction and the cascade's rank cap are
  the gate's OWN dominances, out of scope here).  Deeper-gap twin
  raises bubble through the same squares — the (iii) legs below.
* **(ii) the single-pad exchange.**  The worried twin is exchanged
  THROUGH `twin_fate` (`Orig/Twin.lean`: relabel by the suit twin
  preserves the verdict; `State.twinMap`/`Move.twinMove` conjugate
  play and win) at the TWIN-EQUAL EXPOSURE MOMENT — the moment the
  twin foundation stands level with the worried suit's, so
  `twin c` is pullable and seats the very runs `c` seated
  (`canSitOn_twin_right`: the tableau fit rules cannot tell twins
  apart); the worried card's downstream uses are carried by the
  twin-twin play conjugation (`Orig/TwinExchangeBoth.lean`'s local
  exchange grades `exchange_go_gen`/`bothOcc_exchangeTwin` at the
  both-occupied/bare licenses).
* **(iii) the interference squares.**  The window bubbling legs are
  the C-session bank, LIFO: `foundToTab_wasteToFound_square`
  (composite-equal, this file), `foundToTab_return` (the adjacent
  identity — paid by the engine already), `bump2_comm` (distinct
  suits), `lower_foundToTab1` — with the banked square inventory's
  warning that worry-worry pairs never square LIFO and the genuine
  corner is the STORAGE shape (a segment placing onto the
  worry-created seat: the seat exists ONLY because of the worry, so
  no square applies — decide-exhibited here as `storC_preVoid` /
  `storC_postFires`).
* **Refute-first gate.**  The residue's premise honesty, the spread
  shape's realizability, and the repair's positive instance are
  decide-anchored at the craft state in the battery below
  (`wGate_spreadPremises`, `wGate_repairPlay`): every premise of the
  stub co-fires at ONE state with a spread-window winning witness,
  and the SAME state carries a worry-free winning play.  The
  52-card full countermodel search is outside decide reach — no
  refutation of the residue-shaped statement was found this session;
  resume from the twin-equal moment's transport.  TODO(proof). -/
theorem stackPile_worry_spread_residue {st : State} {c : Card} {b : Base}
    {q s₁ : State} {m₂ : Move} {rest : List Move} {w : State}
    (hwf : st.WF) (hgate : suitLive c.suit.twin st = true)
    (hreach : Reach st q) (hwfq : q.WF)
    (hf : State.step q (Move.foundToTab c b) = some s₁)
    (hne : m₂ ≠ Move.tabToFound c)
    (hrun : s₁.run (m₂ :: rest) = some w) (hwin : w.isWin = true) :
    ∃ play v, st.run play = some v ∧ v.isWin = true ∧
      ∀ m' ∈ play, m' ≠ Move.foundToTab c b := sorry

/-! ### The engine (the first-occurrence elimination) -/

/-- The engine: strong induction on a witnessing play's length.  At
the first `m`-occurrence, either the play already avoids `m`, or the
worry is terminal (impossible: the raised-away foundation is short
of thirteen — `wf_found_chop_toIdx` against `isWin_len`), or the
occurrence is an adjacent restack window (excised through
`foundToTab_return`'s identity, two moves shorter), or it is a
spread window — the residue's instance, with the gated root, the
reached window state, and the follow-move contract. -/
private theorem worry_elim : ∀ (n : Nat) (st : State) (c : Card) (b : Base)
    (π : List Move) (w : State),
    st.WF → suitLive c.suit.twin st = true →
    st.run π = some w → w.isWin = true → π.length ≤ n →
    (∃ play v, st.run play = some v ∧ v.isWin = true ∧
      ∀ m' ∈ play, m' ≠ Move.foundToTab c b) := by
  intro n
  induction n with
  | zero =>
      intro st c b π w hwf hgate hrun hwin hlen
      cases π with
      | nil => exact ⟨[], w, hrun, hwin, by simp⟩
      | cons m rest => exact absurd hlen (by simp)
  | succ n ih =>
      intro st c b π w hwf hgate hrun hwin hlen
      rcases mem_avoid_or_first π with hclean | ⟨A, rest, hπ, hA⟩
      · exact ⟨π, w, hrun, hwin, hclean⟩
      · obtain ⟨u, hA', hu⟩ :=
          run_app_split A st (Move.foundToTab c b :: rest) w (by rw [hπ] at hrun; exact hrun)
        cases rest with
        | nil =>
            obtain ⟨s₁, h1, hlast⟩ := State.run_cons hu
            have hx : (some s₁ : Option State) = some w := hlast
            have hw : s₁ = w := Option.some.inj hx
            rw [← hw] at hwin
            obtain ⟨htop, -, hs₁⟩ := foundToTab_fires h1
            have hwu : u.WF := run_wf A hA' hwf
            have hchop : (chop (u.found c.suit)).length = c.rank.toIdx :=
              wf_found_chop_toIdx hwu htop
            have h13 : (s₁.found c.suit).length = 13 := isWin_len c.suit hwin
            rw [hs₁, putCard_found, setFound_found_self] at h13
            exact absurd h13 (by have := Rank.toIdx_lt c.rank; rw [← hchop] at this; omega)
        | cons m₂ tail =>
            obtain ⟨s₁, h1, hrest⟩ := State.run_cons hu
            by_cases hm₂ : m₂ = Move.tabToFound c
            · obtain ⟨s₂, h2, htail⟩ := State.run_cons hrest
              subst hm₂
              have hret := foundToTab_return (run_wf A hA' hwf) h1
              have hu2 : s₂ = u := Option.some.inj (h2.symm.trans hret)
              rw [hu2] at htail
              have hnew : st.run (A ++ tail) = some w :=
                run_app_glue A st u w tail hA' htail
              have hnl : (A ++ tail).length ≤ n := by
                have hπl : π.length = A.length + tail.length + 2 := by
                  rw [hπ, List.length_append, List.length_cons, List.length_cons]
                  omega
                rw [List.length_append]
                omega
              exact ih st c b (A ++ tail) w hwf hgate hnew hwin hnl
            · exact stackPile_worry_spread_residue hwf hgate ⟨A, hA'⟩ (run_wf A hA' hwf)
                h1 hm₂ hrest hwin

/-! ### The capstone -/

/-- **The suit-grade gate theorem (the card's capstone).**  At a `WF`
state whose worried suit's TWIN is live (`suitLive c.suit.twin` —
committable-now or committable-pending content per the Rust `extra`
formula), the worry-back `Move.foundToTab c b` is prunable: SOME
winning play avoids it entirely.  This certifies the pruning the
production Rust gate already performs (`gen_moves`'s `suit_filter`:
a suit-s worry is offered only when the twin suit is not live) —
the complementary direction of the same gate.  PROVEN as the
assembly over the one named residue `stackPile_worry_spread_residue`
above (the vacate pattern): the verbatim case, the
impossible-terminal corner, and every adjacent restack window are
PROVEN here; the spread window — the seat-work and the
pause-and-restack-with-cargo shapes — rides the named stub's route.
The Klondike twin of this theorem (`stackPile_safe_prunable`,
`Klondike/Dominance.lean` §5.4) should import on harvest: (a) the
framework's shape here (the whole-play avoidance — stronger than the
Klondike chapter's head-avoidance reading); (b) the residue-less
skeleton's split — adjacent-window excision via the two-step undo
identity (the Klondike `foundToTab_undo` family is the analog of
`foundToTab_return`), the impossible-terminal corner (a raised-away
foundation cannot be a win), and the collected spread windows into
one named stub; (c) the commit-first sequencing square — the
twin-anchored raise-vs-worry composite — as the (i) leg the stub's
route consumes. -/
theorem stackPile_worry_prunableAt {st : State} {c : Card} {b : Base}
    (hwf : st.WF) (hgate : suitLive (c.suit.twin) st = true) :
    prunableAt st (Move.foundToTab c b) := by
  intro hsolv
  obtain ⟨π, w, hrun, hwin⟩ := hsolv
  exact worry_elim π.length st c b π w hwf hgate hrun hwin (Nat.le_refl π.length)

/-! ### The probe battery (craft states and corner exhibits)

The residue's refute-first battery and the def-reading probes, all
decide-anchored inline (the file-touch rule of this card bars a
witnesses-file landing; every exhibit here is `by decide` on the
same 14-field hand-rolled `DecidableEq State` the witness corpus
carries — family 1, dedup-marked there).

* **The craft state `wGate`:** hearts at 12 (worried top `♥Q`, exit
  ♥K stocked), clubs at 12 (seat `♣K`), spades complete, diamonds at
  5 with the LIVE twin content `♦6` (`suitCommitNow .diamond` — a
  zero-reveal `nextUp` tableau top).  The gate premise fires
  (`wGate_gateTwinLive`); the club suit is ALSO live (its own `♣K`
  raise is pending — an honest side-reading, not probed).
* `wGate_spreadPremises`: every premise of the residue co-fires at
  ONE 52-card WF state, with a spread-window winning play whose
  second move is the twin's own commit — the both-constructions
  surface.  `wGate_repairPlay`: the SAME state carries a worry-free
  winning play — the repair's positive instance.
* `wGate_lastNotWin`: the worry cannot terminate a winning play (the
  impossible-terminal corner at a concrete instance).
* `wGate_orderLockA`/`B`: the square's `hcorn` bar is real — at the
  craft state the worry-onto-`♣K`-and-raise-`♣K` pair is illegal in
  BOTH orders (`b = inr y`: the raise consumes the worry's own seat).
* `storC_preVoid`/`postFires`: the STORAGE corner is real — the
  `♠2` waste placement onto the worried `♥3`'s seat is illegal
  before the worry and legal after it (the seat exists only because
  of the worry).
* `probe_cnow_*`, `probe_xnext_*`: the two disjunct readings fire
  and fail independently — the hand-slip probes. -/

namespace WorryCoReal

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

private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

private def foundWG : Suit → List Card
  | .heart => [H .ace, H .two, H .three, H .four, H .five, H .six, H .seven,
      H .eight, H .nine, H .ten, H .jack, H .queen]
  | .club => [C .ace, C .two, C .three, C .four, C .five, C .six, C .seven,
      C .eight, C .nine, C .ten, C .jack, C .queen]
  | .spade => [S .ace, S .two, S .three, S .four, S .five, S .six, S .seven,
      S .eight, S .nine, S .ten, S .jack, S .queen, S .king]
  | .diamond => [D .ace, D .two, D .three, D .four, D .five]

/-- The craft state: hearts 12 (worried `♥Q`), clubs 12 (seat
`♣K`), spades complete, diamonds 5 with the live twin `♦6`; the
diamond ladder and ♥K stocked. -/
def wGate : State where
  found := foundWG
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [D .six]⟩
    | .p1 => ⟨[], [C .king]⟩
    | _ => ⟨[], []⟩
  stock := [D .seven, D .eight, D .nine, D .ten, D .jack, D .queen, D .king, H .king]
  waste := []
  drawStep := 1

/-- The post-worry state of the exhibited spread play. -/
def wMid : State where
  found := fun s =>
    match s with
    | .heart => [H .ace, H .two, H .three, H .four, H .five, H .six, H .seven,
        H .eight, H .nine, H .ten, H .jack]
    | .club => foundWG .club
    | .spade => foundWG .spade
    | .diamond => foundWG .diamond
  piles := fun a =>
    match a with
    | .p1 => ⟨[], [C .king, H .queen]⟩
    | _ => (wGate.piles) a
  stock := wGate.stock
  waste := []
  drawStep := 1

/-- The won endpoint of both exhibited plays. -/
def wFin : State where
  found := fun s => s.upCards
  piles := fun _ => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

private def drawChain : List Move :=
  [Move.draw, Move.wasteToFound (D .seven), Move.draw, Move.wasteToFound (D .eight),
   Move.draw, Move.wasteToFound (D .nine), Move.draw, Move.wasteToFound (D .ten),
   Move.draw, Move.wasteToFound (D .jack), Move.draw, Move.wasteToFound (D .queen),
   Move.draw, Move.wasteToFound (D .king), Move.draw, Move.wasteToFound (H .king)]

/-- The residue-shaped tail: the twin's own commit opens, the
worried `♥Q` returns, `♣K` rises, then the ladder. -/
def wRest : List Move :=
  [Move.tabToFound (H .queen), Move.tabToFound (C .king)] ++ drawChain

theorem wGate_wf : wGate.WF := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    cases s with
    | spade => exact ⟨13, rfl⟩
    | heart => exact ⟨12, rfl⟩
    | diamond => exact ⟨5, rfl⟩
    | club => exact ⟨12, rfl⟩
  · intro a; cases a <;> decide
  · intro c _
    rcases c with ⟨s, r⟩
    cases s <;> cases r <;> decide
  · decide

/-- The gate's premise at the craft state: the twin of the worried
suit (diamond, of hearts) IS live — the now-reading. -/
theorem wGate_gateTwinLive : suitLive (H .queen).suit.twin wGate = true := by decide

/-- The worried suit itself and the complete spades are NOT live. -/
theorem wGate_notLive :
    suitLive (H .queen).suit wGate = false ∧ suitLive (S .two).suit wGate = false := by
  decide

/-- The worry cannot terminate a winning play (the
impossible-terminal corner, concretely). -/
theorem wGate_lastNotWin :
    ((wGate.run [Move.foundToTab (H .queen) (Sum.inr (C .king))]).map
      (fun s => s.isWin)) = some false := by decide

/-- The residue is non-vacuous: every premise co-fires at one 52-card
WF state with a spread-shaped winning witness. -/
theorem wGate_spreadPremises :
    ∃ q s₁ m₂ rest w,
      wGate.WF ∧ suitLive (H .queen).suit.twin wGate = true ∧ Reach wGate q ∧ q.WF ∧
      State.step q (Move.foundToTab (H .queen) (Sum.inr (C .king))) = some s₁ ∧
      m₂ ≠ Move.tabToFound (H .queen) ∧ s₁.run (m₂ :: rest) = some w ∧ w.isWin = true := by
  refine ⟨wGate, wMid, Move.tabToFound (D .six), wRest, wFin, wGate_wf,
    wGate_gateTwinLive, ⟨[], rfl⟩, wGate_wf, by decide, by decide, by decide,
    by decide⟩

/-- The repair's positive instance: the same state carries a winning
play with NO `♥Q` worry anywhere — the residue's owed conclusion,
witnessed. -/
theorem wGate_repairPlay :
    ∃ v, wGate.run ([Move.tabToFound (D .six), Move.tabToFound (C .king)] ++ drawChain)
        = some v ∧ v.isWin = true ∧
      ([Move.tabToFound (D .six), Move.tabToFound (C .king)] ++ drawChain).all
        (fun m' =>
          match m' with
          | .foundToTab x _ => decide (x ≠ H .queen)
          | _ => true) = true := by
  refine ⟨wFin, by decide, by decide, by decide⟩

/-- The order-locked corner, forward: after the worry, `♣K` no longer
tops its pile — the raise dies. -/
theorem wGate_orderLockA :
    (wGate.run [Move.foundToTab (H .queen) (Sum.inr (C .king)),
      Move.tabToFound (C .king)]).isSome = false := by decide

/-- The order-locked corner, backward: after the raise, the worry's
seat is gone — the passage `hcorn` bars real moves, not ghosts. -/
theorem wGate_orderLockB :
    (wGate.run [Move.tabToFound (C .king),
      Move.foundToTab (H .queen) (Sum.inr (C .king))]).isSome = false := by decide

/-- The storage probe state: `♥3` founded, `♠4` seated, `♠2` waiting
in the waste. -/
private def storP : State where
  found := fun s =>
    match s with
    | .heart => [H .ace, H .two, H .three]
    | .club => [C .ace, C .two]
    | _ => []
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [S .four]⟩
    | _ => ⟨[], []⟩
  stock := []
  waste := [S .two]
  drawStep := 1

/-- The storage corner, before: the `♠2` placement onto the worried
`♥3`'s seat is illegal — the seat does not exist yet. -/
theorem storC_preVoid : (storP.step (Move.wasteToTab (S .two) (Sum.inr (H .three)))).isSome
    = false := by decide

/-- The storage corner, after: the SAME placement is legal beyond
the worry — the seat exists only because of the worry, so no
commutation square can carry it. -/
theorem storC_postFires :
    (storP.run [Move.foundToTab (H .three) (Sum.inr (S .four)),
      Move.wasteToTab (S .two) (Sum.inr (H .three))]).isSome = true := by decide

/-- The commitNow probe state: `♣3` on `♦4` — club has
committable-now content. -/
private def cnowP : State where
  found := fun s =>
    match s with
    | .heart => [H .ace, H .two, H .three]
    | .club => [C .ace, C .two]
    | _ => []
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [D .four, C .three]⟩
    | _ => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

theorem probe_cnow_club : (suitCommitNow .club cnowP) = true := by decide

theorem probe_cnow_others :
    (suitCommitNow .heart cnowP) = false ∧ (suitCommitNow .spade cnowP) = false ∧
      (suitCommitNow .diamond cnowP) = false := by decide

theorem probe_cnow_live :
    (suitLive .club cnowP) = true ∧ (suitLive .heart cnowP) = false ∧
      (suitLive .spade cnowP) = false := by decide

/-- The exposesNext probe state: `♣3` pending, the twin spade's
`♠4` exposed one rank up. -/
private def xnextP : State where
  found := fun s =>
    match s with
    | .heart => [H .ace, H .two, H .three]
    | .club => [C .ace, C .two]
    | .spade => [S .ace, S .two, S .three]
    | .diamond => []
  piles := fun a =>
    match a with
    | .p0 => ⟨[], [D .four, C .three]⟩
    | .p1 => ⟨[], [S .four]⟩
    | _ => ⟨[], []⟩
  stock := []
  waste := []
  drawStep := 1

theorem probe_xnext_spade : (suitExposesNext .spade xnextP) = true := by decide

theorem probe_xnext_others :
    (suitExposesNext .heart xnextP) = false ∧ (suitExposesNext .diamond xnextP) = false ∧
      (suitExposesNext .club xnextP) = false := by decide

end WorryCoReal

/-! ### Axiom discipline

Per-declaration `#print axioms` audit for the new public heads; the
gate targets `[propext]`/`[propext, Quot.sound]` for the sorry-free
rows.  The two sorry-tainted rows are the named residue itself and
the capstone's assembly over it (the vacate-pattern form: the
skeleton is sorry-free; the content rides the named stub). -/

#print axioms dominantAt
#print axioms prunableAt
#print axioms dominates
#print axioms suitCommitNow
#print axioms suitExposesNext
#print axioms suitLive
#print axioms stackPile_worry_sequence
#print axioms stackPile_worry_spread_residue
#print axioms stackPile_worry_prunableAt
#print axioms WorryCoReal.wGate_wf
#print axioms WorryCoReal.wGate_gateTwinLive
#print axioms WorryCoReal.wGate_notLive
#print axioms WorryCoReal.wGate_lastNotWin
#print axioms WorryCoReal.wGate_spreadPremises
#print axioms WorryCoReal.wGate_repairPlay
#print axioms WorryCoReal.wGate_orderLockA
#print axioms WorryCoReal.wGate_orderLockB
#print axioms WorryCoReal.storC_preVoid
#print axioms WorryCoReal.storC_postFires
#print axioms WorryCoReal.probe_cnow_live
#print axioms WorryCoReal.probe_cnow_others
#print axioms WorryCoReal.probe_xnext_spade
#print axioms WorryCoReal.probe_xnext_others
