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

/-- Taking at least the whole list takes the whole list. -/
private theorem take_ge_length {α : Type} : ∀ (l : List α) (n : Nat),
    l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil => intro n _; cases n <;> rfl
  | cons x t ih =>
      intro n h
      cases n with
      | zero => exact absurd h (by simp)
      | succ m =>
          show x :: t.take m = x :: t
          exact congrArg (x :: ·) (ih m (by simp at h; omega))

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

/-- Append-glue for pure-draw prefixes: after `q` draws land at `z`,
the suffix continues from `z`. -/
private theorem run_replicate_append :
    ∀ (q : Nat) (u z : State) (rest : List Move),
    u.run (List.replicate q Move.draw) = some z →
    u.run (List.replicate q Move.draw ++ rest) = z.run rest := by
  intro q
  induction q with
  | zero =>
      intro u z rest h
      have hx : (some u : Option State) = some z := h
      injection hx with hx2
      rw [← hx2]
      rfl
  | succ q ih =>
      intro u z rest h
      obtain ⟨u₁, hstep, hrest⟩ := State.run_cons h
      show u.run (Move.draw :: (List.replicate q Move.draw ++ rest)) = z.run rest
      rw [run_step_cons hstep]
      exact ih u₁ z rest hrest

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

/-- **(B) The compliant replay**: with `c` stocked next for its
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

STATUS (this row's engine kit is landed BELOW, sorry-free; the
nine-case assembly remains).  The landed private strip:

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
(B) really cites (A)).  TODO(assembly). -/
theorem draw1_compliant_replay {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock) :
    ∀ π w, rungHeldUntilExit c π → st.run π = some w → w.isWin = true →
      ∃ k s', st.run (List.replicate k Move.draw ++ [Move.wasteToFound c]) = some s' ∧
        WinFrom s' := sorry

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
