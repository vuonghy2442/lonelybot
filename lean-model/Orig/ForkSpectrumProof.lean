import Orig.MacroInternal
import Orig.ForkStateUniq
import Orig.ForkStateUniqGate

/-!
# Orig.ForkSpectrumProof — the spectrum completeness row, closed by
falsifier

THE BRIEF (third formulation): the going-deeper restricted language is
superseded; the game's own rules are the only constraint, and the
spectrum of a class's `forkState`s is the closure under three named
structural generators (cecab21/8e469a3, in-tree `ForkSpectrum`):
`twinSwap` (`conjugateForkState`), `parentSwap` (the conditional (x+1)
under-seat trade — the premise delegated to this card), `cargo`
(`CargoPath`).  The proof target: `forkSpectrum_complete` — every
`forkState` of one class is in this closure.

**THE PROBE-FIRST VERDICT (the third landing of the ForkUniqProbe
family).**  The in-tree statement is REFUTED at theorem grade, and the
mechanism is the same one the G2 gate card isolated: ALL THREE
GENERATORS ARE FOUNDATION-FLAT —

* `twinSwap`: the conjugate composite raises x (+1 own suit), slides
  (flat), pulls x back (−1 own suit) — net-flat card-for-card
  (`conjugate_endpoint_netflat`, whose loose `∃ d` absorbs the
  172ca30-corrected `d := x.twin` verbatim);
* `cargo`: every leg is a `tabToTab` — flat
  (`cargoPath_rungs`, §1 of `Orig.ForkStateUniq`);
* `parentSwap`: the (x+1) trade is a composite of board slides — flat
  (this file's §3 instantiates the delegated conditional and proves
  its flatness too).

So every `ForkSpectrum` endpoint shares the start's entire height
tuple (§1 below).  But the macro class carries same-pair,
same-orientation `forkState`s whose NON-PAIR rungs differ — the G2
counterexample export (`forkGate_strict_head_false`, public at
`Orig.ForkStateUniqGate`; witness pair {5♥, 5♦}, spade rungs 5 vs 6) —
and the forward journey between them (`[tabToTab 5♥ (inr 6♣),
tabToFound 6♠]`) decomposes as ONE CARGO LEG plus ONE NON-PAIR RAISE:
the closure generates the slide but has NO LETTER that raises
non-pair material.  The foundation bookkeeping the brief calls
"already accounted for by the stack discipline" is carried by NO
generator: the cascade exit — the user's own (a) generator from the
first formulation, the (x+1)-parent climb — is the missing letter.
This file lands:

* §1 THE FLATNESS LAWS — `forkSpectrum_rungsFlat` (every leg preserves
  all four rungs), `forkSpectrum_wf` (WF travels), and
  `forkSpectrum_foundsFlat` (the endpoints read the foundations
  card-for-card): the spectrum's invariant floor, sorry-free.
* §2 THE REFUTATION — `forkSpectrum_complete_refuted`: the in-tree
  row's own statement negated, all premises satisfied (the gate's
  public export consumed; cite-before-craft, no new states built).
* §3 THE DELEGATED CONDITIONAL — `ParentSwap` instantiated honestly:
  the structural shape (the twins parent-seated, the (x+1) cards
  trading piles, the boards agreeing elsewhere) PLUS the closure
  carrier (the `CargoPath` premise is exactly the fit-side conditional
  — "sometimes available" is a per-state availability claim, and the
  composite semantics live inside the closure).  Even instantiated,
  the trade is rung-flat — so the rescue the completeness needs cannot
  come from this generator.
* §4 THE NON-VACUITY BATTERY — the closure genuinely generates the
  face world: `FaceShape` embeds (`faceShape_spectrum`), the slid mate
  orbit embeds (`slidMate_spectrum`, consuming §3 of
  `Orig.ForkStateUniq`), and the king shuffle embeds
  (`kingVacWalk_spectrum`, §2 there).
* §5 THE REPAIR LEDGER — the equality-locked completeness
  (`forkSpectrum_complete_locked`, named BLOCKED, the G1–G3 diagnosis
  restated at the equal-rung grade the craft forces) and the
  cascade-letter direction: the honest full spectrum is this closure
  PLUS a raising letter, with the going-deeper domination semantics.

House compliance: additive leaf (not wired into the root, mirroring
the MacroInternal discipline); every fresh head audited
(`#print axioms` — expected `[propext]`/`[propext, Quot.sound]`, zero
`Classical.choice`); exactly ONE `sorry` (the named BLOCKED target);
the in-tree interface (`ForkSpectrum`, `conjugateForkState`,
`CargoPath`, `forkState`) mirrored, never redefined.  The import list
extends the mandated `Orig.MacroInternal` with `Orig.ForkStateUniq`
and `Orig.ForkStateUniqGate` — the refutation consumes the gate's
banked public counterexample export, and re-crafting a duplicate
family would violate the dedup discipline.
-/

/-! ## §1. The flatness laws — the spectrum's invariant floor -/

/-- A cargo walk preserves `WF`, leg by leg.  (The copy of
`Orig.ForkStateUniq`'s private `cargoPath_wf`; the components it
splits into — `step_wf` — are public at `Orig/Reach.lean`.) -/
private theorem cargoPathWf : ∀ {st w : State},
    CargoPath st w → st.WF → w.WF := by
  intro st w h
  induction h with
  | refl s => exact fun hx => hx
  | @cons s₀ z u₂ _hstep hkind _t ih =>
      obtain ⟨c, b, hfire, hrev, _⟩ := hkind
      exact fun hwf => ih (step_wf hwf hfire)

/-- **THE HEIGHT-TUPLE FIXITY LAW** — every leg of the fork spectrum
preserves all four rungs: the conjugate composite is net-flat on the
foundations (the §4 raise+slide+pull arithmetic of
`Orig.ForkStateUniq`), the parent-swap trade is a cargo composite
(§3), and the cargo closure never writes a foundation.  This is the
row the counterexample weaponizes: the spectrum CANNOT MOVE A RUNG. -/
theorem forkSpectrum_rungsFlat : ∀ {st w : State},
    ForkSpectrum st w → ∀ σ, rungAt w σ = rungAt st σ := by
  intro st w h
  induction h with
  | base s =>
      intro σ
      rfl
  | @twinSwap st₀ z w₁ hc _t ih =>
      obtain ⟨x, ba, bb, s₁, s₂, -, h₁, h₂, h₃⟩ := hc
      have hnet := conjugate_endpoint_netflat (x := x) (w := z)
        ⟨x.twin, ba, bb, s₁, s₂, h₁, h₂, h₃⟩
      intro σ
      exact (ih σ).trans (by
        show (z.found σ).length = (st₀.found σ).length
        rw [hnet σ])
  | @parentSwap st₀ z w₁ hp _t ih =>
      obtain ⟨heq, -⟩ := hp
      subst heq
      exact ih
  | @cargo st₀ z w₁ hcp _t ih =>
      intro σ
      exact (ih σ).trans (cargoPath_rungs hcp σ)

/-- `WF` travels the spectrum: every generator's legs are legal
firing moves (the conjugate composite is three steps, the trade rides
cargo, the stub identity leg is `rfl`). -/
theorem forkSpectrum_wf : ∀ {st w : State},
    ForkSpectrum st w → st.WF → w.WF := by
  intro st w h
  induction h with
  | base s => exact fun hx => hx
  | @twinSwap st₀ z w₁ hc _t ih =>
      obtain ⟨x, ba, bb, s₁, s₂, -, h₁, h₂, h₃⟩ := hc
      exact fun hwf => ih (step_wf (step_wf (step_wf hwf h₁) h₂) h₃)
  | @parentSwap st₀ z w₁ hp _t ih =>
      obtain ⟨heq, -⟩ := hp
      subst heq
      exact ih
  | @cargo st₀ z w₁ hcp _t ih =>
      exact fun hwf => ih (cargoPathWf hcp hwf)

/-- **THE CONTENT FIXITY LAW** — a `WF` spectrum endpoint reads the
foundations card-for-card (the height-tuple fixity law lifted through
the banked `rung_found_congr`: at a fixed height tuple the founded
content is the rank-ordered prefix, card for card).  The spectrum
relocates boards; it never rewrites a foundation. -/
theorem forkSpectrum_foundsFlat {st w : State} (hwf : st.WF)
    (h : ForkSpectrum st w) (σ : Suit) :
    w.found σ = st.found σ :=
  rung_found_congr w st (forkSpectrum_wf h hwf) hwf σ
    (forkSpectrum_rungsFlat h σ)

/-! ## §2. The refutation — the third landing of the ForkUniqProbe family

The gate's public export `forkGate_strict_head_false` carries the
counterexample as a self-contained existential: two `WF` `forkState`s
of one macro class, witnessing the same pair with the same
orientation (the iff names the SAME card at both), whose non-pair
spade rungs differ by exactly one.  Together with the flatness law
this negates the in-tree completeness row at its own shape: the
cascade exit (the climb of the exposed (x+1) parent 6♠) is a
non-pair `tabToFound` — a letter NO generator carries. -/

/-- **THE IN-TREE COMPLETENESS ROW IS FALSE AS STATED** — with all its
premises satisfied by the gate's craft, `ForkSpectrum st w` cannot
close: the spectrum is height-tuple-fix (§1) and the class carries a
same-class same-pair `forkState` pair whose spade rungs differ.  The
row's sorry is not a blocked gate; it is a false conjunct, exactly as
the G2 verdict found for `forkState_unique` (the same cell, the same
family, third landing).  The missing generator is the raising letter
(see §5). -/
theorem forkSpectrum_complete_refuted :
    ¬ (∀ (st : State), st.WF → forkState st → ∀ (w : State),
        sameOrbitSetoid.r st w → forkState w → ForkSpectrum st w) := by
  intro h
  obtain ⟨C, st₁, st₂, x, s, hpack⟩ := forkGate_strict_head_false
  obtain ⟨hwf₁, hwf₂, hfs₁, hfs₂, hc₁, hc₂, -, -, -, -, hne⟩ := hpack
  have hr : sameOrbitSetoid.r st₁ st₂ :=
    Quotient.exact (hc₁.trans hc₂.symm)
  have hflat := forkSpectrum_rungsFlat (h st₁ hwf₁ hfs₁ st₂ hr hfs₂)
  exact hne (hflat s).symm

/-! ## §3. The delegated conditional — the parent swap instantiated

cecab21 lands `ForkSpectrum.parentSwap` with a placeholder premise
(`st = w ∧ True`, "to be instantiated") and delegates the
formalization ("the fit-side conditions, the tabToTab composite
semantics") to this card.  The honest instantiation: the trade's
STRUCTURE is the endpoint read (the twins parent-seated on their own
piles, both parents of the pair rank and of the twins' opposing color
family; at the endpoint the parents have traded piles, the twins
re-seated directly on the other's parent, the boards agreeing
everywhere else), and the trade's LEGALITY is carried by the
`CargoPath` premise — exactly the "SOMETIMES available" conditional:
availability is per-state, and the composite legs (temporary-seating
choreography included) live inside the closure.  The v1 shape is the
bare-top trade (no covering cards above the twins); the covering-
following generalization folds the same legs over the covering runs —
each leg's run carries its cover, and the closure carrier absorbs it
unchanged. -/

/-- The structural shape of the parent trade, read at the two
endpoints: `x` sits directly on `p` at pile `a` and `x.twin` directly
on `q` at pile `b` (both parents rank-(pair+1) — the (x+1) cards — of
the twins' opposing color family); at `w` the PARENTS have traded
piles (the twins stay, re-seated on the other's parent); all other
piles and both hidden decks are untouched. -/
def ParentSwapShape (st w : State) (x p q : Card)
    (a b : Anchor) (bs₁ bs₂ : List Card) : Prop :=
  p ≠ q ∧ a ≠ b ∧
    x.rank.toIdx + 1 = p.rank.toIdx ∧
    x.rank.toIdx + 1 = q.rank.toIdx ∧
    ¬ twinSuit p.suit x.suit ∧ ¬ twinSuit q.suit x.suit ∧
    (st.piles a).faceUp = bs₁ ++ [p, x] ∧
    (st.piles b).faceUp = bs₂ ++ [q, x.twin] ∧
    (w.piles a).faceUp = bs₁ ++ [q, x] ∧
    (w.piles b).faceUp = bs₂ ++ [p, x.twin] ∧
    (∀ y, y ≠ a → y ≠ b → w.piles y = st.piles y) ∧
    (w.piles a).hidden = (st.piles a).hidden ∧
    (w.piles b).hidden = (st.piles b).hidden

/-- **THE PARENT SWAP** — the delegated conditional, instantiated: the
`CargoPath` premise is the fit-side carrier (the trade fires through
reversible cargo legs exactly when the alternating-color discipline
permits both parents at the traded positions — "sometimes"), and the
shape premise is the structural residue (the (x+1) cards trading
between the twins' two piles).  Read at the states where the
`forkState` detection fires, this is the spectrum's second named
generator at honest grade. -/
def ParentSwap (st w : State) (x p q : Card) : Prop :=
  ∃ a b bs₁ bs₂, CargoPath st w ∧ ParentSwapShape st w x p q a b bs₁ bs₂

/-- The instantiated generator rides the spectrum: the trade is a
cargo-composite, so the `cargo` constructor absorbs it (with the
in-tree stub replaced upstream by this premise, the constructor's
argument is exactly this `CargoPath`). -/
theorem parentSwap_spectrum {st w : State} {x p q : Card}
    (h : ParentSwap st w x p q) : ForkSpectrum st w := by
  obtain ⟨a, b, bs₁, bs₂, hcp, -⟩ := h
  exact ForkSpectrum.cargo hcp (ForkSpectrum.base w)

/-- **Even instantiated, the parent swap is rung-flat** — the headline
of §3: the trade relocates board content and nothing else, so the
rescue the completeness row needs CANNOT come from instantiating this
conditional.  The missing content is the raising letter (§5). -/
theorem parentSwap_rungsFlat {st w : State} {x p q : Card}
    (h : ParentSwap st w x p q) :
    ∀ σ, rungAt w σ = rungAt st σ :=
  forkSpectrum_rungsFlat (parentSwap_spectrum h)

/-- The trade preserves `WF` (it is a cargo walk). -/
theorem parentSwap_wf {st w : State} {x p q : Card}
    (h : ParentSwap st w x p q) : st.WF → w.WF :=
  forkSpectrum_wf (parentSwap_spectrum h)

/-! ## §4. The non-vacuity battery — what the closure genuinely generates

The refutation is about COMPLETENESS, not about the generators: the
closure is the honest carrier of the face world, and the rows below
witness each in-tree generator family by a banked sorry-free public
row.  (The twin-swap's own firing witness lives on the sibling probe
branch `orig-conjugate-probe`, not merged at this base; the ledger
row in §5 records it.) -/

/-- The in-tree face world embeds in the spectrum: `FaceShape` is the
one-conjugate-deep closure (cargo-only, or one conjugate bridge plus
cargo in the dual face), and both grades are vanilla spectrum walks. -/
theorem faceShape_spectrum {st w : State} (h : FaceShape st w) :
    ForkSpectrum st w := by
  rcases h with hcp | ⟨z, hconj, hcpz⟩
  · exact ForkSpectrum.cargo hcp (ForkSpectrum.base w)
  · exact ForkSpectrum.twinSwap hconj
      (ForkSpectrum.cargo hcpz (ForkSpectrum.base w))

/-- The slid mate face is in the spectrum: §3 of `Orig.ForkStateUniq`
lands the mate as ONE reversible cargo leg off the witness state, so
the mate orbit (the non-king two-face book) is closure-generated.  The
premises are `forkState_slide_mate`'s own — read at a `forkState`
whose twin is directly covered by a fitting cargo carrying the seat
package. -/
theorem slidMate_spectrum {st : State} {x d : Card} {q : Anchor}
    {bs : List Card}
    (hwf : st.WF)
    (hpin1 : rungAt st x.suit = x.rank.toIdx)
    (hpin2 : rungAt st x.twin.suit = x.rank.toIdx)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hshape : (st.piles q).faceUp = bs ++ [x.twin, d])
    (hfit : canSitOn d x = true)
    (hseat : bs ≠ [] ∨ ((st.piles q).hidden = [] ∧ x.twin.rank = Rank.king)) :
    ∃ s', forkState s' ∧ ForkSpectrum st s' := by
  obtain ⟨s', -, hfs, hcp⟩ :=
    forkState_slide_mate hwf hpin1 hpin2 hiff hshape hfit hseat
  exact ⟨s', hfs, ForkSpectrum.cargo hcp (ForkSpectrum.base s')⟩

/-- The king shuffle orbit is in the spectrum: §2 of
`Orig.ForkStateUniq` realizes every bare-king vacate as ONE
reversible cargo leg, so the whole king-wandering orbit is
closure-generated. -/
theorem kingVacWalk_spectrum {st w : State} (h : KingVacWalk st w) :
    ForkSpectrum st w :=
  ForkSpectrum.cargo (kingVacWalk_cargoPath h) (ForkSpectrum.base w)

/-! ## §5. The repair ledger — the honest targets the refutation leaves

Two directions, both priced against the craft:

* **RAISING LETTER, the full-spectrum repair**: the cascade exit is
  the composite the craft itself performs — a channel slide (the
  witness relocating off the covered next-up; the slide of a PAIR
  card rides cargo verbatim) followed by the `tabToFound` climb of
  the exposed (x+1) parent.  Adding the climb letter (with the
  going-deeper domination semantics of the superseded formulation)
  makes the cell→mate journey `cargo ∘ raise` — two generators, both
  witnessed by the craft.  The raise letter is exactly the user's
  own (a) generator from the first formulation ("the cascade (raise
  (x+1), (x+2), … — each exhaustive per its pile; each cascade exit
  can re-serve as a forkState").
* **EQUALITY LOCK, the state-grade repair**: the completeness row at
  FIXED height tuple.  The craft proves the lock necessary (this
  file, §2); at equal rungs the content agreement is banked
  (`forkState_content_of_rungsAgree`: founds and hidden profiles
  agree card-for-card and per-pile), and the residual is the board
  normalization — the same G1/G3 tier the maximality analysis priced:

  - **G1 (pair transport)**: the two endpoints must witness the same
    pair up to twin flip — the `fork_threeCards` tier, sorry'd
    in-tree;
  - **G2 (coverage)**: the mate production needs the covering-cargo
    parcel (`forkState_slide_mate`'s premises name it: the twin
    directly covered by a fitting cargo, the exposed twin's seat
    package) — the (Q,J)-corner shapes degenerate to the witness's
    own cargo orbit;
  - **G3 (board normalization)**: the extra non-covering wiggle must
    be linked into the {twinSwap, parentSwap, cargo} walks through
    reversible legs keeping the fork geometry — the
    `saturated_classification`/`canonFace_sameShape` tier, sorry'd
    in-tree.

  The row below is that target, named BLOCKED, consuming nothing. -/

/-- **THE EQUALITY-LOCKED COMPLETENESS — the honest repair target**
(named BLOCKED, the in-tree gated-row precedent `forkState_unique` →
the craft carries).  Same class, both `forkState`s, and the height
tuple FIXED EQUAL: then (and only then — §2 shows the lock is
necessary) is the second forkState inside the three-generator
closure?  The three gates are priced in the §5 ledger; this row is
the finishing target the next classification card owns. -/
theorem forkSpectrum_complete_locked (st : State) (hwf : st.WF)
    (hfs : forkState st) (w : State)
    (hcls : sameOrbitSetoid.r st w) (hwfs : forkState w)
    (heqrungs : ∀ σ : Suit, rungAt st σ = rungAt w σ) :
    ForkSpectrum st w := by
  sorry

/-! ## The audit battery

`#print axioms` per fresh head — expected `[propext]` or
`[propext, Quot.sound]`, ZERO `Classical.choice` (every row is
inductive bookkeeping over banked sorry-free public components);
the named BLOCKED target shows its `sorryAx` exactly as the
in-tree gated rows do (`cone_pulls_congr_crossarm`,
`forkState_unique` precedents). -/

#print axioms forkSpectrum_rungsFlat
#print axioms forkSpectrum_wf
#print axioms forkSpectrum_foundsFlat
#print axioms forkSpectrum_complete_refuted
#print axioms parentSwap_spectrum
#print axioms parentSwap_rungsFlat
#print axioms parentSwap_wf
#print axioms faceShape_spectrum
#print axioms slidMate_spectrum
#print axioms kingVacWalk_spectrum
#print axioms forkSpectrum_complete_locked

/- APPEND-MARKER -/
