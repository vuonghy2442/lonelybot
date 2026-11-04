import Orig2.Fork.Class.ForkPairRung
import Orig2.Fork.Class.ForkRungGeGadget
import Orig2.Fork.Split.ForkPin
import Orig2.Substrate.Integrity
import Orig2.Fork.Class.ForkTwinLive
import Orig2.Fork.Class.ForkLivePair

/-! ## Merged from `ForkRungGe.lean` (2026-11-02) -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Orig2/ForkRungGe — the twin-suit rung is not an independent residual

READ-ONLY scratch card.  No source file is modified; nothing committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## What this card proves

`TwinKit.SplitPairRungEq` (`Orig2/Fork/Class/ForkTwinLive.lean:411`), equivalently the
one-sided `PairRungKit.SplitTwinRungGe` (`Orig2/Fork/Class/ForkPairRung.lean:176`), is the
campaign's last purely arithmetic clause:

    at every split:  rungAt F c.twin.suit = rungAt F c.suit.

**The main theorem of this card: the residual is not an independent
obligation.**  The *S-liveness of the twin at the bottom* pins it outright
(`canRaiseS_rung`), and that liveness is already the content of the campaign's
own live-pair residual:

    `SplitKit.SplitLivePair → TwinKit.SplitPairRungEq`
      (`splitPairRungEq_of_splitLivePair`),

i.e. the pair-rung equality — both halves, not merely the one-sided target —
follows from `SplitKit.SplitLivePair` *alone*: **no `SplitBlock`, no
`SplitContainment`, no siting, no cover datum.**  In particular it follows from
the repository's existing valley-elimination residual
`ValleyElim.ValleyElimNonfork` (`LiveKit.splitLivePair_of_valleyElim`):

    `splitPairRungEq_of_valleyElim`.

## The mechanism

Three lines:

* `CanRaiseS F c` is green at every split (`SplitKit.splitHyp_green`);
* `TwinLivePair F d` says the live set is exactly `{d, d.twin}`, so
  `c ∈ {d, d.twin}`;
* in *either* arm `c.twin` is one of the two live cards
  (`canRaiseS_twin_of_livePair` — the arm `c = d` reads the twin `d.twin`).

Two `canRaiseS_rung` instances then give
`rungAt F c.twin.suit = c.rank.toIdx = rungAt F c.suit`.

This is *sharper* than the repository's `TwinKit.rungAt_twin_of_landingLivePair`
(`Orig2/Fork/Class/ForkTwinLive.lean:308`), which needs the whole `LandingLivePair`
(twin liveness **plus** the third-suit containment) as input: here the single
`TwinLivePair` conjunct suffices, and the containment clause is not consulted.

Provenance: the repository already carried every ingredient
(`Landing.twinLivePair_at_F_of_splitLivePair`, `Orig2/Fork/Split/ForkLanding.lean:295`,
re-pivots the live pair to `c`; `canRaiseS_rung` then pins the rung) but never
the implication.  What is new here is the statement itself, the pivot-free
proof (`canRaiseS_twin_of_livePair` handles both arms), the exact `↔` with the
pin under `SplitBlock + SplitContainment`, and the negative result
(`Temp/RungGe_Gadget.lean`) showing the cover-source datum cannot supply it.

## Exactness

With `SplitBlock` + `SplitContainment` the converse is the repository's
`TwinKit.splitLivePair_of_block_containment_of_pin`
(`Orig2/Fork/Class/ForkTwinLive.lean:602`), so the pair-rung residual *is* the live-pair
residual in the presence of the other two clauses:

    `splitLivePair_iff_pairRungEq_of_block_containment`.
-/

namespace RungGe

open TwinKit

/-! ## §1. Twin liveness pins the twin-suit rung -/

/-- **TWIN LIVENESS PINS THE TWIN RUNG.**  An S-live `c.twin` sits on the
frontier of its own suit (`canRaiseS_rung`), and the twin keeps `c`'s rank. -/
theorem rungAt_twin_eq_of_live {F : State} {c : Card}
    (h : CanRaiseS F c.twin) : rungAt F c.twin.suit = c.rank.toIdx := by
  have hh := canRaiseS_rung (st := F) (c := c.twin) h
  rwa [show c.twin.rank = c.rank from rfl] at hh

/-- The same read as `nextUp`, i.e. the `TwinKit.SplitTwinRungPin` clause. -/
theorem nextUp_twin_of_live {F : State} {c : Card}
    (h : CanRaiseS F c.twin) : F.nextUp c.twin = true :=
  TwinKit.nextUp_true_iff.mpr (rungAt_twin_eq_of_live h)

/-! ## §2. The live-pair residual supplies the twin's liveness -/

/-- **THE CASE ANALYSIS.**  `CanRaiseS F c` puts the pull card in the live pair
`{d, d.twin}`; in both arms the twin `c.twin` is one of the two live cards, so
it is S-live.  Nothing is assumed about `c` and `d` beyond `TwinLivePair`. -/
theorem canRaiseS_twin_of_livePair {F : State} {c d : Card}
    (hS : CanRaiseS F c) (hl : TwinLivePair F d) :
    CanRaiseS F c.twin := by
  rcases (hl c).mp hS with h | h
  · -- `c = d`: the twin is the *other* card of the pair
    rw [h]
    exact (hl d.twin).mpr (Or.inr rfl)
  · -- `c = d.twin`: the twin is the raise card itself
    rw [h, card_twin_twin]
    exact (hl d).mpr (Or.inl rfl)

/-- The twin's S-liveness at every split's bottom — the *single* missing
datum, named (it is the first conjunct of `Mech.LandingLivePair`). -/
def SplitTwinLiveAtBottom : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail →
    CanRaiseS F c.twin

#print axioms RungGe.rungAt_twin_eq_of_live
#print axioms RungGe.nextUp_twin_of_live
#print axioms RungGe.canRaiseS_twin_of_livePair

end RungGe


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-!
# Temp/TwinAt — the last unowned half of `SplitLivePair`, factored exactly

READ-ONLY scratch card.  No source file is modified; nothing committed.
Zero `sorry`, zero `Classical.choice`, zero `native_decide`; axiom battery at
the tail.

## The target

`RungGe.SplitTwinLiveAtBottom` (`Orig2/Fork/Class/ForkRungGe.lean:130`):

    at every valley split:  CanRaiseS F c.twin.

## What this card proves

1. **THE EXACT FACTORIZATION (§3).**

       RungGe.SplitTwinLiveAtBottom  ↔
         TwinKit.SplitTwinRungPin ∧ TwinAt.SplitTwinSited

   No `SplitBlock`, no `SplitContainment`, no extra minimality, no circular
   hypothesis.  `SplitTwinRungPin` is the campaign's own pre-existing residual
   (the twin-suit rung pin) and `SplitTwinSited` is the *static* siting clause

       TwinSited F c = c.twin is face-up with company below, or a bare king.

   Both directions are proven, so the target contains **exactly one** clause
   that is not already a named campaign residual: the siting.

2. **The pointwise engine (§2).**  The single unconditional lemma

       F.WF → CanRaiseS F c → F.nextUp c.twin = true → TwinSited F c
         → CanRaiseS F c.twin          (`canRaiseS_twin_of_pin_and_sited`)

   by a case split on `CanRaise F c`: if `c` tops a pile the
   `canRaiseS_twin_iff` reduction applies; if `c` is blocked the *cover* clause
   of `c.twin`'s licence is supplied by `pileOfTop_twin_of_block` plus the
   `fromCard`-singleton read of "`c.twin` is a pile top".  This is **stronger**
   than the `canRaiseS_twin_iff` route the brief proposes: no
   `pileOfTop F c ≠ none` hypothesis is needed.

3. **The siting clause is ONE explicit corner (§4).**

       TwinAlone F c := c.twin is the ONLY face-up card of its pile, and the
                        pile is not a bare king
                        (hidden nonempty, or c.twin is not a king).

   Under `SplitBlock`, `SplitTwinSited ↔ (no split realises TwinAlone F c)`
   (`splitTwinSited_iff_splitTwinAlone`), so the whole target is

       SplitTwinRungPin  ∧  SplitTwinAlone.

4. **The siting clause is NOT a local consequence (§5).**  `RungGeGadget.F`
   already carries `F.WF`, `CanRaiseS F 5H`, `¬ CanRaise F 5H` and
   `¬ TwinSited F 5H`, so

       ¬ ∀ F c, F.WF → CanRaiseS F c → ¬ CanRaise F c → TwinSited F c
       (`not_local_twinSited`)

   is kernel-checked.  No argument from the split's *local* data can prove the
   target; only minimality + the saturation of `u`,`v` can (which the gadget,
   not being a split of a minimal play, does not have).

5. **The corner is exactly the mechanism failure (§6).**
   `TwinAlone F c → ¬ CanRaise F c.twin`, so at a corner split the raise card
   `d` is *not* `c.twin` (`corner_split_raise_ne_twin`): the siting failure and
   the mechanism failure are the same event.

## What is NOT proved

`SplitTwinSited` is not derived here, and §5 shows it cannot be derived from the
bottom's local data.  The probes (`Temp/TwinAt_probe.py`: 432/432 splits of 27
boards; `Temp/TwinAt_rand.py`: 3946 random components, 42 saturated pairs) never
see the corner at a minimal split, so it is *minimality-gated*.  The exact
residual is `SplitTwinAlone`, and `rungGe_iff_pin_and_notAlone_of_block` is the
exact statement of the target in terms of it.
-/

namespace TwinAt

open TwinKit

/-! ## §1. The two clauses -/

/-- **`SplitTwinSited`** — the *static* siting clause of the target at every
split's bottom: `c.twin` is face up with company below it, or is a bare king.
No rungs, no licences, no cargo. -/
def SplitTwinSited : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail → TwinSited F c

/-- **`TwinAlone F c`** — the ONE corner in which `TwinSited F c` fails: the
twin is the sole face-up card of its pile, and the pile is not a bare king
(hidden nonempty, or the twin is not a king). -/
def TwinAlone (F : State) (c : Card) : Prop :=
  ∃ a : Anchor,
    (F.piles a).faceUp = [c.twin] ∧
      ((F.piles a).hidden ≠ [] ∨ c.twin.rank ≠ Rank.king)

/-- **`SplitTwinAlone`** — no split's bottom realises the corner. -/
def SplitTwinAlone : Prop :=
  ∀ (u v : State) (ρ : List Move) (F : State)
    (left right : List Move) (c d : Card) (b : Base)
    (pre post tail : List Move),
    SplitKit.SplitHyp u v ρ F left right c d b pre post tail → ¬ TwinAlone F c

/-! ## §2. Kit -/

/-- `below c l = []` plus `lastOf l = some c` plus `Nodup l` forces `l = [c]`. -/
theorem eq_singleton_of_below_nil {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlast : lastOf l = some c) (hbelow : below c l = []) :
    l = [c] := by
  have hmem : c ∈ l := lastOf_mem hlast
  obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem hmem
  have hsplit := tfc_below_fromCard c l
  rw [hbelow, ht, List.nil_append] at hsplit
  cases t with
  | nil => rw [← hsplit]
  | cons y t' =>
      exfalso
      have hnd' : (c :: y :: t').Nodup := hsplit ▸ hnd
      have hcnot : c ∉ (y :: t') := (List.nodup_cons.mp hnd').1
      have hlast' : lastOf (c :: y :: t') = some c := hsplit ▸ hlast
      exact hcnot (lastOf_mem hlast')

/-- **A pile top's `fromCard` is the singleton.**  `lastOf l = some c` at a
`Nodup` run means `c` is the *last* occurrence, so the first-occurrence suffix
`fromCard c l` is exactly `[c]`. -/
theorem fromCard_singleton_of_lastOf : ∀ (l : List Card) (c : Card),
    l.Nodup → lastOf l = some c → fromCard c l = [c]
  | [], c, _, h => by simp [lastOf] at h
  | [x], c, _, h => by
      have hxc : x = c := Option.some.inj h
      subst hxc
      exact fromCard_head_eq
  | x :: y :: t, c, hnd, h => by
      have hlast : lastOf (y :: t) = some c := h
      have hnd' : (y :: t).Nodup := hnd.of_cons
      have hfrom : fromCard c (y :: t) = [c] :=
        fromCard_singleton_of_lastOf (y :: t) c hnd' hlast
      have hxc : x ≠ c := by
        intro hxc
        have hmem : c ∈ (y :: t) := lastOf_mem hlast
        rw [hxc] at hnd
        exact (List.nodup_cons.mp hnd).1 hmem
      show fromCard c (x :: y :: t) = [c]
      rw [fromCard, ite_eq_right hxc, hfrom]

/-! ## §3. The pointwise engine and the exact factorization -/

/-- **THE BLOCKED ARM OF THE ENGINE.**  With `c` blocked, `c.twin` tops a pile
(`pileOfTop_twin_of_block`), so its `fromCard` is the singleton and the flat
licence form applies. -/
theorem canRaiseS_twin_of_blocked {F : State} {c : Card}
    (hF : F.WF) (hS : CanRaiseS F c) (hb : ¬ CanRaise F c)
    (hpin : F.nextUp c.twin = true) (hsit : TwinSited F c) :
    CanRaiseS F c.twin := by
  have htop : F.pileOfTop c.twin ≠ none :=
    PairRungKit.pileOfTop_twin_of_block hF hS hb
  obtain ⟨a, ha⟩ := option_some_of_ne_none htop
  have htopa : (F.piles a).top = some c.twin := (pileOfTop_eq_some_iff hF).mp ha
  have hmem : c.twin ∈ (F.piles a).faceUp := Pile.mem_of_top htopa
  obtain ⟨a', hmem', hseat'⟩ := hsit
  have h1 : F.pileHolding c.twin = some a := (pileHolding_eq_some_iff hF).mpr hmem
  have h2 : F.pileHolding c.twin = some a' := (pileHolding_eq_some_iff hF).mpr hmem'
  have haa : a = a' := Option.some.inj (h1.symm.trans h2)
  subst haa
  have hfc : fromCard c.twin (F.piles a).faceUp = [c.twin] :=
    fromCard_singleton_of_lastOf _ _ (runOK_nodup (hF.2.1 a)) htopa
  exact (LandKit.canRaiseS_below_form hF).mpr
    ⟨hpin, a, hmem, hseat', Or.inl hfc⟩

/-- **PIN + SITING GIVE THE TWIN'S S-LICENCE.**  Unconditional in the block:
the case split on the pile top of `c` supplies the cover clause of `c.twin`'s
licence in both arms.  (The `canRaiseS_twin_iff` reduction made block-free.)
The split is on the `Option` `pileOfTop`, so it is constructive — no
`Classical.choice`. -/
theorem canRaiseS_twin_of_pin_and_sited {F : State} {c : Card}
    (hF : F.WF) (hS : CanRaiseS F c)
    (hpin : F.nextUp c.twin = true) (hsit : TwinSited F c) :
    CanRaiseS F c.twin := by
  cases hp : F.pileOfTop c with
  | none =>
      exact canRaiseS_twin_of_blocked hF hS (by
        rintro ⟨-, a, ha, -⟩
        rw [hp] at ha
        exact absurd ha (by simp)) hpin hsit
  | some a =>
      by_cases hseat : (chop (F.piles a).faceUp ≠ [] ∨
          ((F.piles a).hidden = [] ∧ c.rank = Rank.king))
      · exact canRaiseS_twin_of_datum hF (by rw [hp]; exact Option.some_ne_none a)
          ⟨hpin, hsit⟩
      · exact canRaiseS_twin_of_blocked hF hS (by
          rintro ⟨-, a', ha', hseat'⟩
          rw [hp] at ha'
          have haa : a' = a := (Option.some.inj ha').symm
          subst haa
          exact hseat hseat') hpin hsit

/-- **THE FORWARD HALF: the target gives the pin.** -/
theorem splitTwinRungPin_of_twinLive (h : RungGe.SplitTwinLiveAtBottom) :
    SplitTwinRungPin := by
  intro u v ρ F left right c d b pre post tail hh
  exact nextUp_true_iff.mpr (canRaiseS_rung (h u v ρ F left right c d b pre post tail hh))

/-- **THE FORWARD HALF: the target gives the siting.** -/
theorem splitTwinSited_of_twinLive (h : RungGe.SplitTwinLiveAtBottom) :
    SplitTwinSited := by
  intro u v ρ F left right c d b pre post tail hh
  exact sited_of_canRaiseS (SplitKit.splitHyp_green hh).1
    (h u v ρ F left right c d b pre post tail hh)

/-- **THE BACKWARD HALF: pin + siting give the target.** -/
theorem twinLive_of_pin_and_sited (hpin : SplitTwinRungPin)
    (hsit : SplitTwinSited) : RungGe.SplitTwinLiveAtBottom := by
  intro u v ρ F left right c d b pre post tail hh
  obtain ⟨hF, hS, -, -⟩ := SplitKit.splitHyp_green hh
  exact canRaiseS_twin_of_pin_and_sited hF hS
    (hpin u v ρ F left right c d b pre post tail hh)
    (hsit u v ρ F left right c d b pre post tail hh)

/-- **THE EXACT FACTORIZATION OF THE TARGET.**  The last unowned half of
`SplitLivePair` is *exactly* the campaign's twin-rung pin plus the static
siting clause.  No `SplitBlock`, no `SplitContainment`, no extra minimality, and
no circular hypothesis. -/
theorem twinLive_iff_pin_and_sited :
    RungGe.SplitTwinLiveAtBottom ↔ SplitTwinRungPin ∧ SplitTwinSited :=
  ⟨fun h => ⟨splitTwinRungPin_of_twinLive h, splitTwinSited_of_twinLive h⟩,
    fun h => twinLive_of_pin_and_sited h.1 h.2⟩

/-! ## §4. The siting clause is one explicit corner -/

theorem twinAlone_not_canRaise {F : State} {c : Card} (hF : F.WF)
    (h : TwinAlone F c) : ¬ CanRaise F c.twin := by
  obtain ⟨a, hfu, hcorner⟩ := h
  rintro ⟨-, a', ha', hseat'⟩
  have htopa' : (F.piles a').top = some c.twin := (pileOfTop_eq_some_iff hF).mp ha'
  have h1 : F.pileHolding c.twin = some a := (pileHolding_eq_some_iff hF).mpr (by
    rw [hfu]; exact List.mem_singleton_self c.twin)
  have h2 : F.pileHolding c.twin = some a' := (pileHolding_eq_some_iff hF).mpr
    (Pile.mem_of_top htopa')
  have haa : a = a' := Option.some.inj (h1.symm.trans h2)
  subst haa
  rcases hseat' with hb | ⟨hh0, hk⟩
  · rw [hfu] at hb
    rw [show ([c.twin] : List Card) = c.twin :: [] from rfl] at hb
    exact hb rfl
  · rcases hcorner with hne | hrk
    · exact hne hh0
    · exact hrk hk

/-- **AT A CORNER SPLIT THE RAISE CARD IS NOT THE TWIN.** -/
theorem corner_split_raise_ne_twin {u v : State} {ρ : List Move} {F : State}
    {left right : List Move} {c d : Card} {b : Base} {pre post tail : List Move}
    (hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (halone : TwinAlone F c) : d ≠ c.twin := by
  intro hd
  have hg := SplitKit.splitHyp_green hh
  rw [hd] at hg
  exact twinAlone_not_canRaise hg.1 halone hg.2.2.1

/-! ## §8. Battery -/

#print axioms SplitKit.splitHyp_green
#print axioms sited_of_canRaiseS
#print axioms canRaiseS_rung
#print axioms PairRungKit.pileOfTop_twin_of_block
#print axioms LandKit.canRaiseS_below_form
#print axioms canRaiseS_twin_of_datum
#print axioms TwinAt.eq_singleton_of_below_nil
#print axioms TwinAt.fromCard_singleton_of_lastOf
#print axioms TwinAt.canRaiseS_twin_of_blocked
#print axioms TwinAt.canRaiseS_twin_of_pin_and_sited
#print axioms TwinAt.splitTwinRungPin_of_twinLive
#print axioms TwinAt.splitTwinSited_of_twinLive
#print axioms TwinAt.twinLive_of_pin_and_sited
#print axioms TwinAt.twinLive_iff_pin_and_sited
#print axioms TwinAt.twinAlone_not_canRaise
#print axioms TwinAt.corner_split_raise_ne_twin

/-- **A CORNER SPLIT REFUTES THE CAMPAIGN'S LIVE PAIR.**  If any split's bottom
realised the corner, `SplitKit.SplitLivePair` would be false: the live pair
forces the raise card to be the twin (`splitTwin_of_livePair_block`), and at a
corner that card is not raisable.  So the residual is exactly load-bearing for
`SplitLivePair` — it is not a technicality. -/
theorem not_splitLivePair_of_corner (hb : SplitKit.SplitBlock)
    {u v : State} {ρ : List Move} {F : State} {left right : List Move}
    {c d : Card} {b : Base} {pre post tail : List Move}
    (hh : SplitKit.SplitHyp u v ρ F left right c d b pre post tail)
    (halone : TwinAlone F c) : ¬ SplitKit.SplitLivePair := by
  intro hl
  exact corner_split_raise_ne_twin hh halone
    (SplitKit.splitTwin_of_livePair_block hl hb u v ρ F left right c d b pre post tail hh)

end TwinAt
