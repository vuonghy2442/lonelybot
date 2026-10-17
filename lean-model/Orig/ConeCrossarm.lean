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

* THE PRICED CORRIDOR KIT (§1.5 below, additive, zero sorry): the
  route's banked halves, landed — the corridor puts its anchors in
  one class (`crossarm_corridor_class`); the register's flip branch,
  at two saturated mates, either degenerates or exhibits an
  arm-contingent card (`crossarm_flip_benign_or_forked` — the
  corridor flip's kill IS the class's benignity, a `forkedCard`);
  and the gate assembled from its remaining two named gaps — the
  in-tree register plus corridor-benign
  (`crossarm_anchor_agree_of_benign`).  The residue is priced
  exactly: register + benign, nothing thinner.

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
   the headline rides it.

4. Update (additive, zero sorry): the banked halves above are now
   LANDED as rows in §1.5 below.  `crossarm_corridor_class` is item
   1's first half (the corridor is a class-mate chain through the
   rev-closure).  `crossarm_flip_benign_or_forked` is item 2's
   de-flip reduction: at two Finals of one class the flip branch
   either degenerates (the twin pair's readings coincide, so the
   anchor tuples agree outright) or EXHIBITS an arm-contingent card —
   the flipped suit's card at the pair's shallower index is FOUNDED
   at the deep-reading anchor and merely at-rung at the shallow one,
   a `forkedCard`; so the corridor flip's kill IS the class's
   benignity (`benign_sat_iff_surely`'s `forkfree` premise).
   `crossarm_anchor_agree_of_benign` assembles everything: the gate
   follows from (i) the register — the in-tree gated orbit theorem's
   conclusion at the anchors — plus (ii) corridor-benign (item 2's
   obstruction content).  The residue's price is thereby two-sided
   and named twice; nothing thinner closes it. -/

/-! ### §1.5 The priced corridor kit — the route's landed halves

Every fresh head here is zero-sorry (the battery shows the grades):
`crossarm_corridor_class` banks the class-mate chain;
`crossarm_flip_benign_or_forked` banks the flip-fork reduction
through the `FoundKit` founding-height bridge
(`mem_found_of_rung`/`mem_found_rank_lt`, whose `foundHeight` fields
read `rungAt` by `rfl`, and the `Card.mk`/`FoundKit.Rk` exhibit
idiom); `crossarm_anchor_agree_of_benign` banks the assembly the
gate rides. -/

/-- **The corridor's class-mate chain** (route item 1's first half,
the banked one): cone legs are reversible, so the cone chains into
the rev-closure (`cone_inClass`), and the setoid welds the two
relations (`RevEqW_trans`) — the anchors joined by a corridor are
same-orbit mates. -/
theorem crossarm_corridor_class {A₁ A₂ : State}
    (hcorr : ∃ z, ConePath A₁ z ∧ sameOrbitSetoid.r z A₂) :
    sameOrbitSetoid.r A₁ A₂ := by
  obtain ⟨z, p, hz⟩ := hcorr
  exact RevEqW_trans hz (cone_inClass A₁ z p)

/-- Kit: the split exhibit at the class grade — a card founded at
one member and missing at a saturated mate is arm-contingency
(`satStackable` witnessed by the deep member, `surelyStackable`
refuted by the shallow one).  Pure class bookkeeping; no state
physics. -/
private theorem crossarm_forked_of_split {C : SameOrbit} {D S : State}
    (hclsD : classOf C D) (hclsS : classOf C S) (hsatS : Final S)
    {c : Card} (hmemD : c ∈ D.found c.suit)
    (hnmemS : ¬ c ∈ S.found c.suit) : forkedCard C c :=
  ⟨⟨D, hclsD, hmemD⟩, fun hS => absurd (hS S hclsS hsatS) hnmemS⟩

/-- **THE FLIP-FORK REDUCTION** (route item 2, de-flipped): at two
WF saturated same-orbit mates, the register's flip branch at a card
`x` either degenerates — the twin pair's own readings coincide, so
the anchor tuples agree outright — or exhibits an arm-contingent
card: the `x.suit` card indexed by the pair's shallower reading is
FOUNDED at the one anchor (the flipped readings make it the deep
wing there — `FoundKit.mem_found_of_rung`) and merely next-up at the
other (its index IS that anchor's own rung —
`FoundKit.mem_found_rank_lt` refutes membership), i.e. a
`forkedCard` of the anchors' class.  The orbit theorem's flip
decision IS the fork decision: the flip branch dies exactly where
the class is benign. -/
theorem crossarm_flip_benign_or_forked {A₁ A₂ : State}
    (hwf₁ : A₁.WF) (hwf₂ : A₂.WF)
    (hsat₁ : Final A₁) (hsat₂ : Final A₂)
    (hclass : sameOrbitSetoid.r A₁ A₂)
    (hflip : ∃ x : Card,
      rungAt A₁ x.suit = rungAt A₂ x.twin.suit ∧
      rungAt A₁ x.twin.suit = rungAt A₂ x.suit ∧
      (∀ s : Suit, s ≠ x.suit → s ≠ x.twin.suit → rungAt A₁ s = rungAt A₂ s)) :
    (∀ s : Suit, rungAt A₁ s = rungAt A₂ s) ∨
    ∃ c : Card, forkedCard (Quotient.mk sameOrbitSetoid A₁) c := by
  obtain ⟨x, h1, h2, h3⟩ := hflip
  have hclsA₂ : classOf (Quotient.mk sameOrbitSetoid A₁) A₂ :=
    (Quotient.sound hclass).symm
  rcases Nat.lt_trichotomy (rungAt A₁ x.suit) (rungAt A₁ x.twin.suit) with
    hsh | hseq | hdp
  · -- `x.suit` is the shallow wing at A₁: the at-rung card of
    -- `x.suit` is founded at A₂ (the flipped deep wing) and merely
    -- next-up at A₁, the shallow anchor of the same suit.
    have hk13 : rungAt A₁ x.suit < 13 :=
      Nat.lt_of_lt_of_le hsh (FoundKit.rung_le hwf₁ x.twin.suit)
    have hk : (Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.suit))).rank.toIdx =
        rungAt A₁ x.suit := FoundKit.Rk_toIdx _ hk13
    have hmemA₂ : Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.suit)) ∈
        A₂.found x.suit :=
      FoundKit.mem_found_of_rung hwf₂ (by
        show (Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.suit))).rank.toIdx <
          rungAt A₂ x.suit
        rw [hk]
        omega)
    have hnmemA₁ : ¬ Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.suit)) ∈
        A₁.found x.suit := by
      intro hmemA₁
      have hclt : (Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.suit))).rank.toIdx <
          rungAt A₁ x.suit :=
        FoundKit.mem_found_rank_lt hwf₁ hmemA₁
      rw [hk] at hclt
      exact absurd hclt (Nat.lt_irrefl (rungAt A₁ x.suit))
    exact Or.inr ⟨Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.suit)),
      crossarm_forked_of_split hclsA₂ rfl hsat₁ hmemA₂ hnmemA₁⟩
  · -- the twin pair's readings coincide: the flip degenerates, and
    -- the tuples agree outright.
    refine Or.inl fun s => ?_
    rcases Decidable.em (s = x.suit) with rfl | hs1
    · exact hseq.trans h2
    · rcases Decidable.em (s = x.twin.suit) with rfl | hs2
      · exact hseq.symm.trans h1
      · exact h3 s hs1 hs2
  · -- `x.suit` is the deep wing at A₁: the mirror exhibit — the same
    -- at-rung card, founded at A₁, merely next-up at A₂.
    have hk13 : rungAt A₁ x.twin.suit < 13 :=
      Nat.lt_of_lt_of_le hdp (FoundKit.rung_le hwf₁ x.suit)
    have hk : (Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.twin.suit))).rank.toIdx =
        rungAt A₁ x.twin.suit := FoundKit.Rk_toIdx _ hk13
    have hmemA₁ : Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.twin.suit)) ∈
        A₁.found x.suit :=
      FoundKit.mem_found_of_rung hwf₁ (by
        show (Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.twin.suit))).rank.toIdx <
          rungAt A₁ x.suit
        rw [hk]
        exact hdp)
    have hnmemA₂ : ¬ Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.twin.suit)) ∈
        A₂.found x.suit := by
      intro hmemA₂
      have hclt : (Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.twin.suit))).rank.toIdx <
          rungAt A₂ x.suit :=
        FoundKit.mem_found_rank_lt hwf₂ hmemA₂
      rw [hk] at hclt
      rw [h2] at hclt
      exact absurd hclt (Nat.lt_irrefl (rungAt A₂ x.suit))
    exact Or.inr ⟨Card.mk x.suit (FoundKit.Rk (rungAt A₁ x.twin.suit)),
      crossarm_forked_of_split rfl hclsA₂ hsat₂ hmemA₁ hnmemA₂⟩

/-- **THE ASSEMBLY CONDITIONAL** — the gate, decomposed: the anchor
agreement follows from (i) the register's conclusion at the anchors
(`saturated_tuple_orbit`'s disjunction, gated in-tree at
`Orig/MacroInternal.lean` §7 — taken here as a premise) and (ii)
corridor-benign: no arm-contingent card in the anchors' class.  The
corridor banks the class-mate chain, the flip-fork reduction turns
the register's flip branch into a `forkedCard`, and the benign
premise kills it.  This is the gate's whole remaining architecture —
exactly two named gaps, both on the classification card's territory:
the register, and the corridor-benign row (the item-2 escape-channel
obstruction assembly). -/
theorem crossarm_anchor_agree_of_benign {A₁ A₂ : State}
    (hwf₁ : A₁.WF) (hwf₂ : A₂.WF)
    (hsat₁ : Final A₁) (hsat₂ : Final A₂)
    (hcorr : ∃ z, ConePath A₁ z ∧ sameOrbitSetoid.r z A₂)
    (horbit : (∀ s : Suit, rungAt A₁ s = rungAt A₂ s) ∨
      ∃ x : Card,
        rungAt A₁ x.suit = rungAt A₂ x.twin.suit ∧
        rungAt A₁ x.twin.suit = rungAt A₂ x.suit ∧
        (∀ s : Suit, s ≠ x.suit → s ≠ x.twin.suit → rungAt A₁ s = rungAt A₂ s))
    (hbenign : ∀ c : Card, ¬ forkedCard (Quotient.mk sameOrbitSetoid A₁) c) :
    ∀ s : Suit, rungAt A₁ s = rungAt A₂ s := by
  rcases horbit with hag | hflip
  · exact hag
  · rcases crossarm_flip_benign_or_forked hwf₁ hwf₂ hsat₁ hsat₂
      (crossarm_corridor_class hcorr) hflip with hag | ⟨c, hf⟩
    · exact hag
    · exact absurd hf (hbenign c)

/-- **THE CORRIDOR GATE** (the named residue): two saturated WF
anchors joined by the cone corridor share their height tuples.  This is
the de-flipped classification content; see §1's route.  Update record
(additive, this session): the gate's assembly is landed as
`crossarm_anchor_agree_of_benign` (§1.5) — it rides exactly (i) the
register's conclusion at the anchors (`saturated_tuple_orbit`'s
disjunction, gated in-tree) and (ii) corridor-benign (no `forkedCard`
in the anchors' class), and `crossarm_flip_benign_or_forked` shows
(ii) is precisely the flip-kill: the flip's non-degenerate case is a
forked-card exhibit.  No banked row decides corridor-benign either
way today; the refutation shape would be a fork arm pair sharing its
pre-state cone corner, and whether the witness-graded undo survives
the cargo seat is exactly the item-2 obstruction content.  The gate
keeps its [H] grade and this sorry. -/
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

 `#print axioms` per fresh head.  The mechanical closure (§2) and the
 §1.5 corridor kit come out clean — the landed heads read [propext] or
 [propext, Quot.sound], zero sorryAx, zero Classical.choice; the
 headline carries the §1 gate's `sorryAx` — the named residue is the
 ONLY sorry surface of this leaf, exactly as the gated in-tree
 sibling's audit shows it. -/

#print axioms ConeCrossarm.cone_pulls_congr_crossarm_of_anchorRungs
#print axioms ConeCrossarm.crossarm_corridor_class
#print axioms ConeCrossarm.crossarm_forked_of_split
#print axioms ConeCrossarm.crossarm_flip_benign_or_forked
#print axioms ConeCrossarm.crossarm_anchor_agree_of_benign
#print axioms ConeCrossarm.crossarm_anchor_agree
#print axioms ConeCrossarm.cone_pulls_congr_crossarm
