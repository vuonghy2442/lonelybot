import Orig.Shuttle
import Orig.Phase
import Orig.Irreversible
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

`runOK_snoc_sit` and `lastOf_exists` mirror Canonical's private
copies; they are re-proven here so this chapter imports nothing
unmerged.  Promote or delete against the canonical versions when
the chapters merge. -/

/-- A legal run sits each card on the one below: the premise of the
under-seat undo. -/
private theorem runOK_snoc_sit {c : Card} : ∀ {l : List Card}, l ≠ [] →
    runOK (l ++ [c]) = true → ∃ z, lastOf l = some z ∧ canSitOn c z = true := by
  intro l
  induction l with
  | nil => intro hne _; exact absurd rfl hne
  | cons x t ih =>
      intro _ h
      cases t with
      | nil =>
          refine ⟨x, rfl, ?_⟩
          have hexp : runOK (x :: ([] : List Card) ++ [c]) = (canSitOn c x && true) := rfl
          rw [hexp, Bool.and_true] at h
          exact h
      | cons y t' =>
          have hexp : runOK (x :: (y :: t') ++ [c]) =
              (canSitOn y x && runOK ((y :: t') ++ [c])) := rfl
          rw [hexp, Bool.and_eq_true] at h
          obtain ⟨z, hz, hsit⟩ := ih (by simp) h.2
          exact ⟨z, hz, hsit⟩

/-- A nonempty list has a last element. -/
private theorem lastOf_exists : ∀ {l : List Card}, l ≠ [] → ∃ z, lastOf l = some z := by
  intro l
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons x t ih =>
      intro _
      cases t with
      | nil => exact ⟨x, rfl⟩
      | cons y t' =>
          obtain ⟨z, hz⟩ := ih (by simp)
          have hll : lastOf (x :: y :: t') = lastOf (y :: t') := rfl
          exact ⟨z, by rw [hll]; exact hz⟩

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
private theorem nextUp_congr {u v : State} {x : Card} (h : v.found x.suit = u.found x.suit) :
    v.nextUp x = u.nextUp x := by
  show decide (x.rank.toIdx = (v.found x.suit).length)
      = decide (x.rank.toIdx = (u.found x.suit).length)
  rw [h]

/-- The below-run keeps only cards of the run it cuts. -/
private theorem mem_below {c : Card} : ∀ {l : List Card} {z : Card},
    z ∈ below c l → z ∈ l := by
  intro l z
  induction l with
  | nil => intro h; cases h
  | cons x t ih =>
      intro h
      have hunf : below c (x :: t) = if x = c then [] else x :: below c t := rfl
      rw [hunf] at h
      split at h
      · cases h
      · rcases List.mem_cons.1 h with he | hrest
        · exact List.mem_cons.2 (Or.inl he)
        · exact List.mem_cons.2 (Or.inr (ih hrest))

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
      rw [nextUp_congr (hB x.suit hxs)]
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
      rw [nextUp_congr (hB x.suit hxs)]
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

/-- **(A) The stock-as-reserve lemma, physical form** (B&G §5.4.1's
exception, draw-1): sameCycle twins are the same verdict.  Route:
the replay of a winning play from the twin splices pure draws in
front of each consuming move (`draw` commutes past every board move
and past other draws by the phase table; a `wasteTo*` fires after
enough draws bring its card to hand — at `drawStep = 1` the cycle is
a plain rotation, `dealUpTo 1`); board moves fire verbatim
(`Phase`'s step table: no move but `draw` reads the stock or waste).
TODO(proof). -/
theorem draw1_sameCycle_sameFate {st st' : State}
    (h1 : st.drawStep = 1) (h2 : st'.drawStep = 1)
    (hsc : sameCycle st st') : sameFate st st' := sorry

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

TODO(proof). -/
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
theorem draw1_compliant_normalForm {st : State} {c : Card}
    (hwf : st.WF) (hstep : st.drawStep = 1)
    (hsafe : safeToFound st c = true)
    (hrung : st.nextUp c = true) (hstock : c ∈ st.stock)
    (hsolv : WinFrom st) :
    ∃ π w, st.run π = some w ∧ w.isWin = true ∧ rungHeldUntilExit c π := sorry

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
