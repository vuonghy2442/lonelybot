import Orig.ForkStateSB

/-!
# Orig.ConeCrossarm — the cross-arm pull congruence, down to its gate

The old gated row `cone_pulls_congr_crossarm` (`Orig/MacroInternal.lean`,
the statement at lines 1019-1029, sorry'd at 1029, its audit line at
1986) re-landed as a leaf: two same-class members at the same height
tuple hanging off TWO saturated anchors pull equal card-multisets,
given the corridor the envelope supplies between the arm anchors.

What this file proves, and what it prices:

* THE MECHANICAL CLOSURE (zero sorry, §2): given that the two anchors
  agree on their height tuples, the comparison closes at the shared
  arm anchor through `cone_pop_window` exactly as the old docstring
  recorded: both ledgers are forced pop records, so per-card counts
  are window counts (`cone_pop_countP`); equal anchor rungs read the
  same founded content card-for-card (`rung_found_congr`, through
  `rung_found_prefix`), and the end-tuple lock `htup` identifies the
  two windows.  This part is pure assembly of banked rows.

* THE CORRIDOR GATE (§1, the one named residue): the anchor-tuple
  agreement itself — two WF `Final` class-mates joined by the
  corridor (∃ z, `ConePath A₁ z` ∧ `sameOrbitSetoid.r z A₂`) have
  equal height tuples.  This is exactly the de-flipped reading of the
  classification tier that sits gated in-tree
  (`saturated_tuple_orbit`, `finals_topFibers`, `envelope` — all
  sorry): the orbit theorem's flip branch is the one live alternative
  to the agreement, so the residue IS the flip decision at the
  corridor.  Its docstring records the analyzed route and the
  sharpness evidence: should flipped Final pairs exist inside a
  corridor-reachable class, the headline row is FALSE as stated (the
  per-card counts diverge at the flipped suit's window edge — the
  card of rank `min(r₁, r₂)` sits in one window and not the other,
  since both members chop to it), so the gate is not a convenience —
  it is the row's truth content.

House compliance: additive leaf; the in-tree interface consumed as-is
(`ConePath`, `ConeLedger`, `cone_pop_countP`, `rung_found_prefix`,
`rung_found_congr`, `Final`, `sameOrbitSetoid`); the headline
statement is the sibling's verbatim copy (its MainInternal twin is
deleted by the root surgery; this leaf is the surgery-ready
re-landing, namespaced to avoid the import-closure collision until
that surgery frees the bare name).
-/

namespace ConeCrossarm

/-! ## §1. The corridor gate — the named residue

The route (its own analysis, priced honestly):

1. The corridor `∃ z, ConePath A₁ z ∧ r z A₂` makes the anchors
   class-mates (the cone legs are reversible, so `cone_inClass`
   chains the path into the rev-closure), both saturated, so the
   gated orbit theorem applies with its flip branch: equal tuples, or
   ONE twin pair flipped (`saturated_tuple_orbit`,
   `Orig/MacroInternal.lean` §7).  The gap is to kill the flip branch
   under the corridor's cone shape (cone legs are rung-monotone
   (`cone_rung_mono`), so `z` sits at-or-below `A₁` pointwise).
2. The flip's obstruction analysis (the honest content a full proof
   must formalize): at a `Final` anchor the escape channels of a
   next-up card `c` are each irreversible — a seated topping next-up
   would already raise (`Final` is `∀ c, ¬ CanRaise`, the seat in
   plain view); a covered next-up's cover `d` is rank-pinned by the
   tableau fit to the two-card family {`c`, `c.twin`} (the only
   rank-`h` cards of the coverable color), the cover's only
   uncovering slide lands `d` ON `c.twin`'s top and thereby blocks
   the raised card's only seated return (a pulled-back card lands
   through its twin's top or, for kings, a bare anchor); a bare
   non-king's departure reveals over a hidden deck
   (`journey_tabToTab_never_reveal`) or abandons a seat no play can
   refill with anything but a king (the first-refill-is-a-king pillar
   of `Orig.PositionSeat`); stock- and waste-resident next-ups can
   never ride a witness journey (the draw-zone conservation and the
   waste rows of `Orig.ForkStateUniqGate` §2).  A general proof
   assembles these into: the rev-closure between two Finals is
   founded-flat, the tuples agree.
3. Until that assembly lands (it is `finals_topFibers`'s second
   conjunct / `saturated_tuple_orbit`'s benign branch — the
   classification card's territory), the gate stays named here, and
   the headline rides it. -/

/-- **THE CORRIDOR GATE** (the named residue): two saturated WF
anchors joined by the cone corridor share their height tuples.  This is
the de-flipped classification content; see §1's route. -/
private theorem crossarm_anchor_agree {A₁ A₂ : State}
    (hwf₁ : A₁.WF) (hwf₂ : A₂.WF)
    (hsat₁ : Final A₁) (hsat₂ : Final A₂)
    (hcorr : ∃ z, ConePath A₁ z ∧ sameOrbitSetoid.r z A₂) :
    ∀ s : Suit, rungAt A₁ s = rungAt A₂ s := by
  sorry

/-! ## §2. The mechanical closure — the shared-arm-anchor comparison

Given the anchor agreement, everything is banked-row assembly: the
ledgers are forced pop windows (`cone_pop_countP` reads each
discipline'd anchor through `rung_found_prefix`), equal anchor rungs
read the same per-suit founded content (`rung_found_congr`), and the
end-tuple lock `htup` identifies the two chop depths — the two
windows are then the SAME LIST, per-card countP equality for free.
This is the old docstring's "closes at the shared arm anchor through
`cone_pop_window`", made formal.

The gate is not merely sufficient — it is necessary.  If the anchors'
rungs differ at some suit, say `rungAt A₁ s < rungAt A₂ s`, the cone
monotonicity (`cone_rung_mono`, both paths) puts the common member
tuple at `rungAt w s ≤ rungAt A₁ s`, so arm 2's window holds the card
`⟨s, Rk (rungAt A₁ s)⟩` in its forced window while arm 1's, chopped
exactly to its own rung, does not — one card counters the congruence.
So no weaker gate can ever close the row: the headline is the
anchor-tuple agreement, cone-forced windows included. -/

/-- The intra-arm closure grade, crossed: with the anchor tuples in
agreement, two same-tuple descendants of either anchor pull equal
card-multisets.  Everything here is cited from the banked rows. -/
theorem cone_pulls_congr_crossarm_of_anchorRungs {A₁ A₂ w w' : State}
    (hwf₁ : A₁.WF) (hwf₂ : A₂.WF)
    (p₁ : ConePath A₁ w) (L₁ : List Card) (hl₁ : ConeLedger p₁ L₁)
    (p₂ : ConePath A₂ w') (L₂ : List Card) (hl₂ : ConeLedger p₂ L₂)
    (htup : ∀ s : Suit, rungAt w s = rungAt w' s)
    (hanchors : ∀ s : Suit, rungAt A₁ s = rungAt A₂ s) :
    ∀ c : Card,
      L₁.countP (fun x => decide (x = c)) =
        L₂.countP (fun x => decide (x = c)) := by
  have hA₁ : ∀ σ, A₁.found σ = σ.upCards.take (rungAt A₁ σ) :=
    fun σ => rung_found_prefix A₁ hwf₁ σ
  have hA₂ : ∀ σ, A₂.found σ = σ.upCards.take (rungAt A₂ σ) :=
    fun σ => rung_found_prefix A₂ hwf₂ σ
  have hfound : ∀ σ, A₁.found σ = A₂.found σ := fun σ =>
    rung_found_congr A₁ A₂ hwf₁ hwf₂ σ (hanchors σ)
  intro c
  have h1 := cone_pop_countP p₁ hl₁ hA₁ c
  have h2 := cone_pop_countP p₂ hl₂ hA₂ c
  rw [h1, h2, hfound c.suit, htup c.suit]

/-! ## §3. The headline — the sibling's verbatim row, re-landed

The statement is the gated `Orig.MacroInternal` row word for word
(only the anchor names' subscripts differ in nothing): the corridor
hypothesis rides the §1 gate; the ledgers and the end-tuple lock ride
the §2 assembly. -/

/-- **CONE PULLS CROSS-ARM CONGRUENCE** — the old gated row (the
sibling at `Orig/MacroInternal.lean` lines 1019-1029, sorry'd there
gated on the envelope), re-landed on this leaf: the corridor gate
(§1) reduces it to the shared-arm-anchor comparison (§2), which is
pure window arithmetic through `cone_pop_window`'s countP read. -/

theorem cone_pulls_congr_crossarm {A₁ A₂ w w' : State}
    (hwf₁ : A₁.WF) (hwf₂ : A₂.WF)
    (hsat₁ : Final A₁) (hsat₂ : Final A₂)
    (p₁ : ConePath A₁ w) (L₁ : List Card) (hl₁ : ConeLedger p₁ L₁)
    (p₂ : ConePath A₂ w') (L₂ : List Card) (hl₂ : ConeLedger p₂ L₂)
    (htup : ∀ s : Suit, rungAt w s = rungAt w' s)
    (hcorr : ∃ z, ConePath A₁ z ∧ sameOrbitSetoid.r z A₂) :
    ∀ c : Card,
      L₁.countP (fun x => decide (x = c)) =
        L₂.countP (fun x => decide (x = c)) :=
  cone_pulls_congr_crossarm_of_anchorRungs hwf₁ hwf₂ p₁ L₁ hl₁ p₂ L₂ hl₂ htup
    (crossarm_anchor_agree hwf₁ hwf₂ hsat₁ hsat₂ hcorr)

end ConeCrossarm

/-! ## The leaf audit battery

 `#print axioms` per fresh head.  The mechanical closure (§2) must
 come out clean; the headline carries the §1 gate's `sorryAx` — the
named residue is the ONLY sorry surface of this leaf, exactly as the
gated in-tree sibling's audit shows it. -/

#print axioms ConeCrossarm.cone_pulls_congr_crossarm_of_anchorRungs
#print axioms ConeCrossarm.crossarm_anchor_agree
#print axioms ConeCrossarm.cone_pulls_congr_crossarm
