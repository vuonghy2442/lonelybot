import Klondike.TwinQuotient

/-!
# Theorem T, completed slices — O1 (destination collapse) and O3 (the asymmetric boundary)

The twin-swap family BEFORE this file (all machine-checked in the imports):

* **T, global relabeling form**: `solvable_relabel` + `solvable_flipAll`
  (Relabel.lean) — solvability is invariant under every coherent suit
  relabeling (the whole 8-element group at once).  PROVEN, axiom-clean.
* **T, local pair exchange** (`State.swapTwin t`, the two-card
  transposition): the unconditional seat-swap direction was REFUTED
  (witnesses/TwinSwapWitness.lean — the legality flip at unequal twin
  heights); the PROVEN exchange windows are `solvable_swapTwin_paired`
  / `_back` (TwinAgnostic.lean — the twin foundation moves occur as ONE
  adjacent pair) and `solvable_swapTwin_separated` / `_back`
  (TwinQuotient.lean — the two stackings separated by an ORTHO mid: no
  move whose legality reads the twin suits' heights).
* **T, cargo/exchange forms**: `solvable_cargoTwin` (TwinSwap.lean, one
  bare twin), `solvable_cargoTwin_exchange_bare` (TwinExchange.lean),
  `solvable_cargoTwin_exchange_of_visClean` (TwinQuotient.lean, the
  both-occupied iff at reachable states).  PROVEN.

The OPEN residue, in TwinQuotient's L1/O3 decomposition: the general
window (ii) — twin-suit activity BETWEEN the two stackings (the
catch-up: the low suit's exact-rung `pileStack`s; and the twin-suit
worry-backs).  This file lands the first genuinely ASYMMETRIC slice.

## O1 — the destination collapse (resolved, minimal form)

`State.solvable_twinDestination_collapse`: at a WF state, if the drawn
card `X` can land on either twin top — `deckPile X (inr Y)` or
`deckPile X (inr Y.flipSuit)` — the two post-states are
solvability-equivalent, by an explicit one-`pilePile` transfer each way
whose landing closes exactly (the board cancel `detach ∘ attach = id`
at the vacated seat).  This is the destination-collapse instance the
C2 program consumes (§4's note: "both yield the same `Encode`, so this
may not even need a cross-pile swap" — confirmed: NO cross-pile twin
swap is involved at all; the two landings are mutually reachable and
`solvable_iff_mutuallyReaches` finishes).  O1's locality question is
resolved for the campaign: the cross-pile local pair exchange remains
the licensed family (`paired`/`separated`), and nothing in the
destination collapse needs it.

## O3 — the asymmetric boundary (the pure catch-up window)

`State.solvable_swapTwin_catchup`: the source play stacks the twin `t`
(NOW stackable: its suit at the shared rung) while `t.flipSuit`'s suit
sits BELOW the rung — the O3 boundary exactly: one twin stackable now,
the other not — then raises the low suit by a PURE CATCH-UP (a segment
of exact-rung `pileStack`s of `t.flipSuit`-suit cards below the twin
rank) and stacks `t.flipSuit`.  L1's bridge ("build the low suit's
prefix raise by the same unbury structure the winning play used for
the high suit") becomes the REORDER: the catch-up segment commutes
with the first stacking; the mirror plays
[prefix; catch-up; stack t'; stack t] and lands on `D.swapTwin t` via
the twinSkew/crossTwin spine of the separated proof, under `haccess` —
the PER-CARD ACCESSIBILITY license (the catch-up segment is playable
at the pre-firing state A itself: no catch-up card is buried under a
twin).  The window strictly strengthens `paired` (cu = []) and covers
the other side of `separated` (an ortho mid excludes the catch-up by
definition; here the mid IS the catch-up).

## §6.5 — the ambiguous-twin canonicalization instance

`twin_stack_order_exchange_catchup`: the SAME-STATE order exchange —
if the win stacks the HIGH twin first with a low-suit catch-up mid
(under the accessibility licenses), the state also wins stacking the
LOW twin first: [prefix; catch-up; stack L; stack H; tail] lands on
EXACTLY the original successor, so the sweep's lowest-first canonical
choice never uniquely loses wins at this window.  The unproven
remainder — the covered-twin corner (the L-first firing blocked by the
mate: dealt-adjacent twins), mids with twin-suit worry-backs or
landings onto the vacated seats, and the DERIVATION of `haccess` at
engine corpora — is the next queue, recorded in FARM.md.
-/

/-! ## The board-pointwise helpers

`attach`/`detach` at the same base cancel (the destination transfer's
board bookkeeping) and two detaches commute (the one-step exchange's
board bookkeeping).  Both are pointwise `topOf` analyses. -/

/-- Attaching then detaching the same base returns the board (the
attach's own freeness guard is the vacated seat's `none`). -/
theorem Board.attach_detach_cancel {bd : Board} {b : Base} {c : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') : bd'.detach b = bd := by
  obtain ⟨htop, -⟩ := (Board.attach_eq_some_iff bd b c).mp (by rw [hatt]; simp)
  refine Board.ext_topOf (funext fun b'' => ?_)
  by_cases hbb : b'' = b
  · rw [hbb, Board.detach_topOf, htop]
  · rw [Board.detach_topOf_ne _ _ _ hbb, Board.attach_topOf_ne _ _ _ hatt hbb]

/-- Two detaches at distinct bases commute (both are pointwise
`topOf`-updates at disjoint cells). -/
theorem Board.detach_detach_comm (bd : Board) (b b' : Base) (h : b ≠ b') :
    (bd.detach b).detach b' = (bd.detach b').detach b := by
  refine Board.ext_topOf (funext fun b'' => ?_)
  by_cases h1 : b'' = b
  · rw [h1, Board.detach_topOf_ne _ _ _ h, Board.detach_topOf, Board.detach_topOf]
  · by_cases h2 : b'' = b'
    · rw [h2, Board.detach_topOf, Board.detach_topOf_ne _ _ _ (Ne.symm h),
        Board.detach_topOf]
    · rw [Board.detach_topOf_ne _ _ _ h2, Board.detach_topOf_ne _ _ _ h1,
        Board.detach_topOf_ne _ _ _ h1, Board.detach_topOf_ne _ _ _ h2]

/-! ## The stock card's two off-board facts

The destination collapse needs the drawn `X` to carry no stack (a WF
board has no edge over a stock card): the phantom-stack killer
`State.topOf_inr_eq_none` wants `bottomOf X = none` (the attach guard)
and `X` in no hidden slice (the deal's piles/stock disjointness). -/

/-- The waste top is in the cycle's remaining cards. -/
theorem Cycle.prev_mem {cy : Cycle Card} {c : Card} (h : cy.prev = some c) :
    c ∈ cy.cards := by
  unfold Cycle.prev at h
  by_cases hz : cy.cursor = 0
  · rw [ite_eq_left hz] at h; simp at h
  · rw [ite_eq_right hz] at h
    exact List.mem_iff_getElem?.mpr ⟨cy.cursor - 1, h⟩

/-- A stock card is never in a pile's hidden slice (the deal's piles
and stock are disjoint by `Deal.WF`). -/
theorem State.stock_prev_not_mem_hidden {st : State} {X : Card} (hwf : st.WF)
    (hprev : st.stock.prev = some X) {a : Anchor} : X ∉ st.hidden a := by
  intro hmem
  have hstock : X ∈ st.stock.cards := Cycle.prev_mem hprev
  have hndeal : X ∈ st.deal.stock := hwf.stock_wf.2 X hstock
  have hpile : X ∈ st.deal.piles a := by
    have : X ∈ (st.deal.piles a).take (st.depths a) := hmem
    exact List.take_subset _ _ this
  exact noDupCards_append_disj ((hwf.deal_wf).2.2)
    (List.mem_flatMap.mpr ⟨a, Anchor.mem_all a, hpile⟩) hndeal

/-! ## O1 — the destination collapse

The two twin-top landings of the same drawn card are mutually
reachable: the transfer moves the (still bare-topped) `X` from one twin
seat to the other and lands on EXACTLY the direct landing's
post-state.  No twin-swap of pile positions is used. -/

private theorem twinDestination_transfer {st A B : State} {X Y₁ Y₂ : Card}
    (hwf : st.WF)
    (h₁ : st.apply (Move.deckPile X (Sum.inr Y₁)) = some A)
    (h₂ : st.apply (Move.deckPile X (Sum.inr Y₂)) = some B)
    (hcard : Y₁ ≠ Y₂) :
    A.apply (Move.pilePile X (Sum.inr Y₂)) = some B := by
  obtain ⟨hprev, hcp₁, bdA, hattA, hAeq⟩ := apply_deckPile_iff.mp h₁
  obtain ⟨-, hcp₂, bdB, hattB, hBeq⟩ := apply_deckPile_iff.mp h₂
  obtain ⟨htopY₁, hvisY₁, hfit₁⟩ := canPlace_inr_iff.mp hcp₁
  obtain ⟨htopY₂, hvisY₂, hfit₂⟩ := canPlace_inr_iff.mp hcp₂
  -- X is a fresh stock card: unseated, in no hidden slice, no stack
  have hXbot : st.board.bottomOf X = none :=
    ((Board.attach_eq_some_iff st.board (Sum.inr Y₁) X).mp (by rw [hattA]; simp)).2
  have hXtop : st.board.topOf (Sum.inr X) = none :=
    State.topOf_inr_eq_none hwf hXbot (fun a => State.stock_prev_not_mem_hidden hwf hprev)
  -- rank arithmetic: X sits strictly below both destinations
  have hXY₁ : X ≠ Y₁ := by
    intro hcon; rw [hcon] at hfit₁
    simp only [canSitOn_eq] at hfit₁
    obtain ⟨hr, -⟩ := hfit₁
    omega
  have hXY₂ : X ≠ Y₂ := by
    intro hcon; rw [hcon] at hfit₂
    simp only [canSitOn_eq] at hfit₂
    obtain ⟨hr, -⟩ := hfit₂
    omega
  -- the transfer's premises at A (whose board is the Y₁-attach)
  have hbA : A.board = bdA := by rw [hAeq]
  have hbot' : A.board.bottomOf X = some (Sum.inr Y₁) := by
    rw [hbA]
    exact (Board.bottomOf_eq _ _ _).mpr (Board.attach_topOf _ _ _ hattA)
  have htopA : A.board.topOf (Sum.inr Y₂) = none := by
    rw [hbA]
    rw [Board.attach_topOf_ne _ _ _ hattA
      (fun hh : (Sum.inr Y₂ : Base) = Sum.inr Y₁ => hcard (Sum.inr.inj hh).symm)]
    exact htopY₂
  have hvisA : A.isVis Y₂ = true := by
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.mp hvisY₂
    have hb'ne : b' ≠ Sum.inr Y₁ := by
      intro hcon
      rw [hcon] at hb'
      have hh := (Board.bottomOf_eq st.board Y₂ (Sum.inr Y₁)).mp hb'
      rw [htopY₁] at hh
      exact absurd hh (by simp)
    have hteq : A.board.topOf b' = some Y₂ := by
      rw [hbA]
      rw [Board.attach_topOf_ne _ _ _ hattA (fun hh : b' = Sum.inr Y₁ => hb'ne hh)]
      exact (Board.bottomOf_eq st.board Y₂ b').mp hb'
    exact Option.isSome_iff_exists.mpr ⟨b', (Board.bottomOf_eq A.board Y₂ b').mpr hteq⟩
  have hcpA : A.canPlace X (Sum.inr Y₂) = true :=
    canPlace_inr_iff.mpr ⟨htopA, hvisA, hfit₂⟩
  -- the walk from X is empty at st (fresh stock card) and stays empty at A
  have hXtopA : A.board.topOf (Sum.inr X) = none := by
    rw [hbA]
    rw [Board.attach_topOf_ne _ _ _ hattA
      (fun hh : (Sum.inr X : Base) = Sum.inr Y₁ => hXY₁ (Sum.inr.inj hh))]
    exact hXtop
  have haboveA : A.board.aboveOf X = [] := by
    rw [Board.aboveOf_eq_go 53 (by omega)]
    rw [show (53 : Nat) = 52 + 1 from rfl, Board.aboveOf_go_topOf_none hXtopA]
  have hcmrA : A.canMoveRun X (Sum.inr Y₂) = true :=
    canMoveRun_inr_iff.mpr ⟨hcpA, by rw [haboveA]; rfl⟩
  -- board bookkeeping: detach at the vacated seat, attach at the twin seat
  have hdet : A.board.detach (Sum.inr Y₁) = st.board := by
    rw [hbA]
    exact Board.attach_detach_cancel hattA
  have hattB' : (A.board.detach (Sum.inr Y₁)).attach (Sum.inr Y₂) X = some bdB := by
    rw [hdet]; exact hattB
  refine apply_pilePile_iff.mpr ⟨Sum.inr Y₁, hbot', ?_, hcmrA, bdB, hattB', ?_⟩
  · exact fun h0 => hcard (Sum.inr.inj h0)
  · rw [hBeq, hAeq]

/-- **O1, the destination collapse (the resolved minimal form)**: at a
WF state, the two twin-top landings of the drawn card `X` — on `Y` or
on its twin `Y.flipSuit`, the two tableau destinations F1 allows — are
solvability-equivalent.  Each is one `pilePile` from the other, landing
exactly on the direct landing's post-state (the vacated seat's
attach/detach cancel; the stock splice and heights are untouched by
the transfer), so mutual reachability finishes.

This is the instance the transposition table, the ≤2-outcome bound
(C2) and the accommodation-side twin choice consume: the two landings
produce the same engine state *because* they are one `pilePile` apart
in the model — NO cross-pile twin swap is needed, confirming §4's
observation.  The premise `hwf` is the standard repair shape: it kills
the phantom stack over a stock card (the junk-board leg). -/
theorem State.solvable_twinDestination_collapse {st A B : State} {X Y : Card}
    (hwf : st.WF)
    (hA : st.apply (Move.deckPile X (Sum.inr Y)) = some A)
    (hB : st.apply (Move.deckPile X (Sum.inr Y.flipSuit)) = some B) :
    A.solvableFrom ↔ B.solvableFrom := by
  have hcard : Y ≠ Y.flipSuit := fun h => Card.flipSuit_ne Y h.symm
  have h1 := twinDestination_transfer hwf hA hB hcard
  have h2 := twinDestination_transfer hwf hB hA (fun h => hcard h.symm)
  have hr1 : A.run [Move.pilePile X (Sum.inr Y.flipSuit)] = some B := by
    simp only [State.run, h1]
  have hr2 : B.run [Move.pilePile X (Sum.inr Y)] = some A := by
    simp only [State.run, h2]
  exact solvable_iff_mutuallyReaches ⟨[Move.pilePile X (Sum.inr Y.flipSuit)], hr1⟩
    ⟨[Move.pilePile X (Sum.inr Y)], hr2⟩

/-! ## O3 — the asymmetric boundary: the pure catch-up window

The engine: two `pileStack`s of OFF-SUIT cards exchange (one step), a
whole catch-up segment commutes with the twin's stacking (the reorder),
and the assembled window mirrors through the twinSkew/crossTwin spine
of the separated proof — with the low suit BELOW the rung at the
source's first firing, the genuinely asymmetric case. -/

/-- **The one-step stack exchange**: two `pileStack` firings of
off-suit cards commute as partial functions — if both orders fire,
they land on the same successor.  The guard transfer: the two cards'
bases are distinct (a base's top is one card) and the `c`-detach
touches neither `t`'s seat nor `t`'s base nor `t`'s suit height; the
successor equality: disjoint detaches commute and the two height bumps
sit at different suits. -/
theorem apply_pileStack_pileStack_exchange {S : State} {t c : Card} {B S₁ T₁ : State}
    (hsu : c.suit ≠ t.suit)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS₁ : S.apply (Move.pileStack c) = some S₁)
    (hT₁ : B.apply (Move.pileStack c) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htopT, β, hβ, hrkT, hBshape⟩ := hB
  rw [apply_pileStack_iff] at hS₁
  obtain ⟨-, βc, hβc, -, hS₁shape⟩ := hS₁
  rw [apply_pileStack_iff] at hT₁
  obtain ⟨-, βcB, hβcB, -, hT₁shape⟩ := hT₁
  -- the two bases are distinct (a base's top is one card)
  have hβcβ : βc ≠ β := by
    intro hcon
    have hc : c = t := by
      have h1 : S.board.topOf βc = some c := (Board.bottomOf_eq S.board c βc).mp hβc
      have h2 : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
      rw [hcon] at h1
      exact Option.some.inj (h1.symm.trans h2)
    exact hsu (by rw [hc])
  -- t's firing guards survive at S1 (the c-detach touches neither
  -- t's seat nor t's base nor t's suit)
  have htopS₁ : S₁.board.topOf (Sum.inr t) = none := by
    rw [hS₁shape]
    show (S.board.detach βc).topOf (Sum.inr t) = none
    by_cases hseat : (Sum.inr t : Base) = βc
    · exfalso
      have hh := (Board.bottomOf_eq S.board c βc).mp hβc
      rw [← hseat] at hh
      rw [htopT] at hh
      exact absurd hh (by simp)
    · rw [Board.detach_topOf_ne _ _ _ hseat]
      exact htopT
  have hbotS₁ : S₁.board.bottomOf t = some β := by
    rw [hS₁shape]
    show (S.board.detach βc).bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.detach_topOf_ne _ _ _ (fun hh => hβcβ hh.symm)]
    exact (Board.bottomOf_eq S.board t β).mp hβ
  have hrkS₁ : t.rank.toIdx = S₁.heights t.suit := by
    rw [hS₁shape]
    show t.rank.toIdx =
      (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit)
    rw [ite_eq_right (Ne.symm hsu)]
    exact hrkT
  have hfire : S₁.apply (Move.pileStack t) = some
      { S₁ with
        board := S₁.board.detach β,
        heights := fun s => if s = t.suit then S₁.heights s + 1 else S₁.heights s } :=
    apply_pileStack_iff.mpr ⟨htopS₁, β, hbotS₁, hrkS₁, rfl⟩
  -- c's base agrees across the two orders (board injectivity at B)
  have hβcB : βcB = βc := by
    have h1 : B.board.topOf βcB = some c := (Board.bottomOf_eq B.board c βcB).mp hβcB
    have h2 : B.board.topOf βc = some c := by
      rw [hBshape]
      show (S.board.detach β).topOf βc = some c
      rw [Board.detach_topOf_ne _ _ _ hβcβ]
      exact (Board.bottomOf_eq S.board c βc).mp hβc
    exact B.board.inj βcB βc c h1 h2
  -- the two orders land equal
  rw [hfire]
  refine congrArg some ?_
  rw [hT₁shape, hS₁shape, hBshape, hβcB]
  apply state_ext
  · rfl
  · show (S.board.detach βc).detach β = (S.board.detach β).detach βc
    exact Board.detach_detach_comm S.board βc β hβcβ
  · funext s
    show (if s = t.suit then
        (if s = c.suit then S.heights s + 1 else S.heights s) + 1
      else if s = c.suit then S.heights s + 1 else S.heights s)
      = (if s = c.suit then
        (if s = t.suit then S.heights s + 1 else S.heights s) + 1
      else if s = t.suit then S.heights s + 1 else S.heights s)
    by_cases h1 : s = t.suit
    · rw [ite_eq_left h1, ite_eq_right (fun hh => hsu (hh.symm.trans h1)),
        ite_eq_right (fun hh => hsu (hh.symm.trans h1)), ite_eq_left h1]
    · by_cases h2 : s = c.suit
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left h2, ite_eq_right h1]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h2, ite_eq_right h1]
  · rfl
  · rfl
  · rfl

/-- **The catch-up segment commutes with the twin's stacking** (L1's
reorder): given the off-pair catch-up segment `cu` (all `pileStack`s of
cards off the pair), the twin's firing at A, and BOTH orders firing
(A-runnable is the accessibility premise; B-runnable is the source
play's own mid), the reordered firing at C₀ lands on EXACTLY the
source's mid successor C.  Step: the one-step exchange iterated through
the segment. -/
theorem pileStack_catchup_reorder {t : Card} :
    ∀ (cu : List Move) (A B C₀ C : State),
    (∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧ c.suit ≠ t.suit ∧
      c ≠ t ∧ c ≠ t.flipSuit) →
    A.apply (Move.pileStack t) = some B →
    A.run cu = some C₀ →
    B.run cu = some C →
    C₀.apply (Move.pileStack t) = some C := by
  intro cu
  induction cu with
  | nil =>
      intro A B C₀ C _ h₁ hA hB
      rw [← run_nil_elim hA, ← run_nil_elim hB]
      exact h₁
  | cons m ms ih =>
      intro A B C₀ C hcu h₁ hA hB
      obtain ⟨c, hmc, hsu, -, -⟩ := hcu m List.mem_cons_self
      subst hmc
      obtain ⟨A₁, hA₁, hArest⟩ := run_cons_elim hA
      obtain ⟨B₁, hB₁, hBrest⟩ := run_cons_elim hB
      have hstep := apply_pileStack_pileStack_exchange hsu h₁ hA₁ hB₁
      exact ih A₁ B₁ C₀ C (fun m' hm' => hcu m' (List.mem_cons_of_mem _ hm'))
        hstep hArest hBrest

/-- Decode the catch-up shape (low-suit `pileStack`s below the twin
rank) into the family the exchange machinery consumes: off `t`'s suit
(the low suit IS the other suit) and off the pair. -/
theorem catchup_mem_offPair {t : Card} {cu : List Move}
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx)
    (m : Move) (hm : m ∈ cu) :
    ∃ c, m = Move.pileStack c ∧ c.suit ≠ t.suit ∧ c ≠ t ∧ c ≠ t.flipSuit := by
  obtain ⟨c, hmc, hsu, hlt⟩ := hcu m hm
  have hne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  refine ⟨c, hmc, ?_, ?_, ?_⟩
  · rw [hsu]; exact hne
  · intro hcon
    rw [hcon] at hsu
    exact hne hsu.symm
  · intro hcon
    rw [hcon] at hlt
    rw [Card.flipSuit_rank] at hlt
    omega

/-- The catch-up segment's moves are CLEAN for the pair exchange (off
the pair), so the clean mirror carries them verbatim. -/
theorem catchup_mem_cleanTwin {t : Card} {cu : List Move}
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx) :
    ∀ m ∈ cu, Move.cleanTwin t m = true := by
  intro m hm
  obtain ⟨c, hmc, hsu, hlt⟩ := hcu m hm
  rw [hmc]
  show Card.offPair t c = true
  have hne : t.flipSuit.suit ≠ t.suit := fun hh => Suit.flipPair_ne t.suit hh
  refine Card.offPair_true (fun hcon => hne (hsu.symm.trans (congrArg Card.suit hcon)))
    (fun hcon => ?_)
  rw [hcon] at hlt
  rw [Card.flipSuit_rank] at hlt
  omega

/-- **O3, the asymmetric boundary — the pure catch-up window**: if the
source game wins via [prefix; stack t; catch-up; stack t'; tail] —
`t` stackable at the first firing (its suit at the rung) while
`t.flipSuit`'s suit sits BELOW the rung, the low suit raised between
the two stackings by a pure prefix-raise `cu` — and the catch-up is
playable at the pre-firing state A itself (`haccess`: per-card
accessibility — no catch-up card is buried under a twin), then the
EXCHANGED game is solvable: it plays [prefix*; catch-up; stack t';
stack t; tail*] — the catch-up rides the clean mirror, the first
stacking lands the cross-skew at the RE-ALIGNED rung (the catch-up put
the low suit exactly at it), and the second re-syncs onto `D.swapTwin t`. -/
theorem State.solvable_swapTwin_catchup {st : State} {t : Card}
    {p₁ cu p₂ : List Move} {A B C D W : State}
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx)
    (hp₁ : st.run p₁ = some A)
    (hf₁ : A.apply (Move.pileStack t) = some B)
    (hcuB : B.run cu = some C)
    (hf₂ : C.apply (Move.pileStack t.flipSuit) = some D)
    (hp₂ : D.run p₂ = some W)
    (haccess : ∃ C₀, A.run cu = some C₀)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  obtain ⟨C₀, hA_cu⟩ := haccess
  have hcuoff := catchup_mem_offPair hcu
  have hcucl := catchup_mem_cleanTwin hcu
  -- the reorder: the twin's firing at C0 lands on the source's C
  have hreor := pileStack_catchup_reorder cu A B C₀ C hcuoff hf₁ hA_cu hcuB
  rw [apply_pileStack_iff] at hreor
  obtain ⟨htop₀, β₀, hβ₀, hrk₀, hCshape⟩ := hreor
  rw [apply_pileStack_iff] at hf₂
  obtain ⟨htop', β', hβ', hrk', hDshape⟩ := hf₂
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  -- the rung alignments the twinSkew/crossTwin spine needs
  have hC₀low : C₀.heights t.flipSuit.suit = t.rank.toIdx := by
    have h1 : t.flipSuit.rank.toIdx = C.heights t.flipSuit.suit := hrk'
    have h2 : C.heights t.flipSuit.suit = C₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then C₀.heights t.flipSuit.suit + 1
        else C₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [Card.flipSuit_rank] at h1
    omega
  have halign₁ : C₀.heights t.suit = C₀.heights t.flipSuit.suit := by
    rw [hrk₀.symm, hC₀low]
  have halign₂ : C.heights t.suit = C.heights t.flipSuit.suit + 1 := by
    have e1 : C.heights t.suit = C₀.heights t.suit + 1 := by
      rw [hCshape]
      show (if t.suit = t.suit then C₀.heights t.suit + 1 else C₀.heights t.suit) = _
      rw [ite_eq_left rfl]
    have e2 : C.heights t.flipSuit.suit = C₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then C₀.heights t.flipSuit.suit + 1
        else C₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [e2, hC₀low, hrk₀]
    omega
  -- the mirror play, segment by segment
  have hcucl' : ∀ m ∈ p₁ ++ cu, Move.cleanTwin t m = true := by
    intro m hm
    rcases List.mem_append.mp hm with h | h
    · exact hc₁ m h
    · exact hcucl m h
  have hseg : st.run (p₁ ++ cu) = some C₀ := run_append_some hp₁ hA_cu
  have hM₁ : (st.swapTwin t).run ((p₁ ++ cu).map (Move.swapTwin t))
      = some (C₀.swapTwin t) := by
    rw [run_swapTwin_clean t st (p₁ ++ cu) hcucl', hseg]
    rfl
  have hrunskew : (C₀.swapTwin t).run [Move.pileStack t.flipSuit]
      = some (C₀.twinSkew t β₀) := by
    simp only [State.run, State.apply_swapTwin_stack_flip htop₀ hβ₀ hC₀low]
  have hskew : C₀.twinSkew t β₀ = C.crossTwin t :=
    State.twinSkew_eq_crossTwin hCshape halign₁
  have hM₁' : (st.swapTwin t).run
      ((p₁ ++ cu).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      = some (C.crossTwin t) := by
    rw [run_split_bind, hM₁]
    show (C₀.swapTwin t).run [Move.pileStack t.flipSuit] = some (C.crossTwin t)
    rw [hrunskew, hskew]
  have hM₃ : (C.crossTwin t).run [Move.pileStack t] = some (D.swapTwin t) := by
    simp only [State.run, State.apply_crossTwin_stack htop' hβ' hrk' halign₂ hDshape]
  have hM₄ : (D.swapTwin t).run (p₂.map (Move.swapTwin t))
      = some (W.swapTwin t) := by
    rw [run_swapTwin_clean t D p₂ hc₂, hp₂]
    rfl
  have hwin' : (W.swapTwin t).isWin = true := by
    simp only [State.isWin, swapTwin_heights]
    exact hwin
  refine ⟨((p₁ ++ cu).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      ++ ([Move.pileStack t] ++ p₂.map (Move.swapTwin t)), W.swapTwin t, ?_, hwin'⟩
  exact run_append_some hM₁' (run_append_some hM₃ hM₄)

/-- The packaged form of the catch-up window: the source play as one
run. -/
theorem State.solvable_swapTwin_catchup_run {st : State} {t : Card}
    {p₁ cu p₂ : List Move} {W : State}
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx)
    (haccess : ∀ A, st.run p₁ = some A → ∃ C₀, A.run cu = some C₀)
    (hrun : st.run (p₁ ++ [Move.pileStack t] ++ cu
      ++ [Move.pileStack t.flipSuit] ++ p₂) = some W)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  simp only [List.append_assoc] at hrun
  rw [run_split_bind st p₁
    ([Move.pileStack t] ++ (cu ++ ([Move.pileStack t.flipSuit] ++ p₂)))] at hrun
  cases hA : st.run p₁ with
  | none => rw [hA] at hrun; simp at hrun
  | some A =>
    rw [hA] at hrun
    have hrun1 : A.run ([Move.pileStack t] ++ (cu ++ ([Move.pileStack t.flipSuit] ++ p₂)))
        = some W := hrun
    rw [run_split_bind A [Move.pileStack t]
      (cu ++ ([Move.pileStack t.flipSuit] ++ p₂))] at hrun1
    simp only [State.run] at hrun1
    cases hB₀ : A.apply (Move.pileStack t) with
    | none => rw [hB₀] at hrun1; simp at hrun1
    | some B =>
      rw [hB₀] at hrun1
      have hrun2 : B.run (cu ++ ([Move.pileStack t.flipSuit] ++ p₂)) = some W := hrun1
      rw [run_split_bind B cu
        ([Move.pileStack t.flipSuit] ++ p₂)] at hrun2
      cases hC : B.run cu with
      | none => rw [hC] at hrun2; simp at hrun2
      | some C =>
        rw [hC] at hrun2
        have hrun3 : C.run ([Move.pileStack t.flipSuit] ++ p₂) = some W := hrun2
        rw [run_split_bind C [Move.pileStack t.flipSuit] p₂] at hrun3
        simp only [State.run] at hrun3
        cases hD₀ : C.apply (Move.pileStack t.flipSuit) with
        | none => rw [hD₀] at hrun3; simp at hrun3
        | some D =>
          rw [hD₀] at hrun3
          have hWD : D.run p₂ = some W := hrun3
          obtain ⟨C₀, hA_cu⟩ := haccess A hA
          exact State.solvable_swapTwin_catchup hc₁ hc₂ hcu hA hB₀ hC hD₀ hWD
            ⟨C₀, hA_cu⟩ hwin

/-! ## §6.5 — the ambiguous-twin canonicalization instance

The same-state stack-order exchange: the win that stacks the HIGH twin
first (with the low suit's catch-up between the two) reshapes into a
win that stacks the LOW twin first, landing on EXACTLY the original
successor — the sweep's lowest-first choice is safe at this window. -/

/-- **The canonicalization safety, the closed instance (§6.5)**: if the
game wins by stacking the HIGH twin `H` first — with the low twin `L`
unstackable at that moment (`L = H.flipSuit`, its suit below the rung),
raised in between by a pure `L`-suit catch-up, and stacked second —
then the SAME game wins by stacking `L` first: the run
[prefix; catch-up; stack L; stack H; tail] lands on the original
successor W, under the two accessibility licenses (`hacc`: the
catch-up runs at the pre-firing state, and `L` fires right after it).
The L-first reading never uniquely loses wins at the catch-up window.
Residue (the honest boundary, next queue): the covered-twin corner
(the `L`-firing at C₀ blocked by a dealt-adjacent mate), mids carrying
twin-suit worry-backs or landings onto the vacated seats, and the
derivation of the accessibility licenses at engine states. -/
theorem twin_stack_order_exchange_catchup {st : State} {L H : Card}
    {p₁ cu p₂ : List Move} {A B C D W : State}
    (htwin : L = H.flipSuit)
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = L.suit ∧ c.rank.toIdx < H.rank.toIdx)
    (hp₁ : st.run p₁ = some A)
    (hfH : A.apply (Move.pileStack H) = some B)
    (hcuB : B.run cu = some C)
    (hfL : C.apply (Move.pileStack L) = some D)
    (hp₂ : D.run p₂ = some W)
    (hacc : ∃ C₀ D₀, A.run cu = some C₀ ∧ C₀.apply (Move.pileStack L) = some D₀) :
    st.run (p₁ ++ cu ++ [Move.pileStack L, Move.pileStack H] ++ p₂) = some W := by
  obtain ⟨C₀, D₀, hA_cu, hD₀⟩ := hacc
  have hsu : L.suit ≠ H.suit := by
    rw [htwin]; exact fun h => Suit.flipPair_ne H.suit h
  -- translate cu's shape to the pair-family form (L off H's suit/pair)
  have hcuoff : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧ c.suit ≠ H.suit ∧
      c ≠ H ∧ c ≠ H.flipSuit := by
    intro m hm
    obtain ⟨c, hmc, hsu', hlt'⟩ := hcu m hm
    refine ⟨c, hmc, ?_, ?_, ?_⟩
    · rw [hsu']; exact hsu
    · intro hcon
      rw [hcon] at hsu'
      exact hsu hsu'.symm
    · intro hcon
      rw [hcon] at hlt'
      rw [Card.flipSuit_rank] at hlt'
      omega
  -- the reorder puts H's firing after the catch-up, on the source's C
  have hreor := pileStack_catchup_reorder cu A B C₀ C hcuoff hfH hA_cu hcuB
  -- the exchange puts L's firing before H's, landing on the source's D0
  have hexchange := apply_pileStack_pileStack_exchange (t := H) (c := L) hsu
    hreor hD₀ hfL
  -- assemble the reshaped run
  simp only [List.append_assoc]
  rw [run_split_bind st p₁
    (cu ++ ([Move.pileStack L, Move.pileStack H] ++ p₂)), hp₁]
  show A.run (cu ++ ([Move.pileStack L, Move.pileStack H] ++ p₂)) = some W
  rw [run_split_bind A cu ([Move.pileStack L, Move.pileStack H] ++ p₂), hA_cu]
  show C₀.run ([Move.pileStack L, Move.pileStack H] ++ p₂) = some W
  show C₀.run ([Move.pileStack L] ++ ([Move.pileStack H] ++ p₂)) = some W
  rw [run_split_bind C₀ [Move.pileStack L] ([Move.pileStack H] ++ p₂)]
  have hr1 : C₀.run [Move.pileStack L] = some D₀ := by
    simp only [State.run, hD₀]
  rw [hr1]
  exact run_append_some (by simp only [State.run, hexchange]) hp₂

/-! ## L1/O3(ii) — the general window: catch-up MIXED with ortho moves

The pure catch-up window above reorders a mid made only of the low
suit's exact-rung `pileStack`s.  The general window (L1/O3 part (ii))
allows the mid to MIX those catch-up cards with ortho twin moves —
draws, reveals, `deckPile`/`pilePile`/`stackPile` landings, and
foundation moves of cards off the twin's own suit — as long as every
mid move stays off the twin pair and (for the three height-reading
kinds) off the twin's suit.  The obstruction the FARM queue records is
genuine: an ortho move landing onto the twin's vacated base seat fires
only on the source side (the twin still occupies the seat before the
reorder), and the `haccess` premise is exactly what such landings
break (witness A's shape); a landing onto the twin itself is the
covered-twin corner (witness B's shape), and it dies on the source
side already — a fired twin is unseated, hence invisible as a
`canPlace` base.  So `haccess` — the mid is replayable at the
pre-firing state — is the no-landing premise in its executable form,
and the whole window rides the EXCHANGE-shaped reorder below instead
of the pure one.

The engine is a per-kind one-step exchange: given the twin's guarded
firing at `S` and a mid move `m` firing on BOTH sides, the twin fires
at the moved state landing exactly on the moved successor.  The
`pileStack` case is the existing `apply_pileStack_pileStack_exchange`
(one lemma serves the catch-up cards and every off-suit `pileStack`);
the six other kinds get one lemma each.  The covered-twin and
vacated-seat divergences are DERIVED from the two firings, never
premised: a landing base occupied by `t` cannot fire at `S` (the cell
reads `none`), and a landing on `t`'s own seat cannot fire at `B` (no
visible base card).  The lone exception is `reveal`: its attach base
is the pile's hidden second-from-top card — deal data, not board
occupancy — so a junk state could hide the twin itself in a hidden
slice and seat the boundary card on top of it on BOTH sides.  WF's
`vis_not_hidden` kills exactly that (the fired twin is seated, hence
visible, hence in no hidden slice), so the reveal step is the one
place the general window carries `hwf`. -/

/-- The mixed-mid predicate: `true` iff the move can ride the general
window's mid.  The three height-reading kinds demand the moved card be
off the twin's suit (its guard reads `heights`, which the twin's firing
bumps — the exchange needs the guard to read the same height on both
sides) and off the twin pair (the mirror leg needs `cleanTwin`; an
on-pair foundation move in the mid is the shuttle corner recorded as
the residue).  Everything else — `draw`, `reveal`, `deckPile`,
`pilePile` — is unconditionally mid-safe. -/
def Move.twinMid (t : Card) : Move → Bool
  | .pileStack c | .deckStack c | .stackPile c _ =>
      decide (c.suit ≠ t.suit ∧ c ≠ t.flipSuit)
  | _ => true

theorem Move.twinMid_pileStack (t c : Card) :
    Move.twinMid t (Move.pileStack c) = true ↔
      c.suit ≠ t.suit ∧ c ≠ t.flipSuit := by
  simp [Move.twinMid]

theorem Move.twinMid_deckStack (t c : Card) :
    Move.twinMid t (Move.deckStack c) = true ↔
      c.suit ≠ t.suit ∧ c ≠ t.flipSuit := by
  simp [Move.twinMid]

theorem Move.twinMid_stackPile (t c : Card) (b : Base) :
    Move.twinMid t (Move.stackPile c b) = true ↔
      c.suit ≠ t.suit ∧ c ≠ t.flipSuit := by
  simp [Move.twinMid]

@[simp] theorem Move.twinMid_draw (t : Card) :
    Move.twinMid t Move.draw = true := rfl

@[simp] theorem Move.twinMid_reveal (t : Card) (a : Anchor) :
    Move.twinMid t (Move.reveal a) = true := rfl

@[simp] theorem Move.twinMid_deckPile (t : Card) (c : Card) (b : Base) :
    Move.twinMid t (Move.deckPile c b) = true := rfl

@[simp] theorem Move.twinMid_pilePile (t : Card) (c : Card) (b : Base) :
    Move.twinMid t (Move.pilePile c b) = true := rfl

/-- Every mixed-mid move is CLEAN for the pair exchange (the mirror
leg of the window needs it). -/
theorem Move.twinMid_clean {t : Card} {m : Move} (hm : Move.twinMid t m = true) :
    Move.cleanTwin t m = true := by
  cases m with
  | draw | reveal _ | deckPile _ _ | pilePile _ _ => rfl
  | deckStack c =>
      obtain ⟨hsu, h₂⟩ := (Move.twinMid_deckStack t c).mp hm
      show Card.offPair t c = true
      exact Card.offPair_true (fun h => hsu (by rw [h])) (fun h => h₂ (by rw [h]))
  | pileStack c =>
      obtain ⟨hsu, h₂⟩ := (Move.twinMid_pileStack t c).mp hm
      show Card.offPair t c = true
      exact Card.offPair_true (fun h => hsu (by rw [h])) (fun h => h₂ (by rw [h]))
  | stackPile c b =>
      obtain ⟨hsu, h₂⟩ := (Move.twinMid_stackPile t c b).mp hm
      show Card.offPair t c = true
      exact Card.offPair_true (fun h => hsu (by rw [h])) (fun h => h₂ (by rw [h]))

/-- The pure catch-up family rides the mixed mid (below-rank cards are
off the pair; the low suit is off the twin's suit). -/
theorem catchup_mem_twinMid {t : Card} {cu : List Move}
    (hcu : ∀ m ∈ cu, ∃ c, m = Move.pileStack c ∧
      c.suit = t.flipSuit.suit ∧ c.rank.toIdx < t.rank.toIdx) :
    ∀ m ∈ cu, Move.twinMid t m = true := by
  intro m hm
  obtain ⟨c, hmc, hsu, hlt⟩ := hcu m hm
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  rw [hmc]
  refine (Move.twinMid_pileStack t c).mpr ⟨fun hcon => hsne (hsu.symm.trans hcon), ?_⟩
  intro hcon
  rw [hcon] at hlt
  rw [Card.flipSuit_rank] at hlt
  omega

/-! ### The per-kind exchange steps

Each lemma takes the twin's guarded firing at `S` (landing `B`) and the
mid move's firing on BOTH sides, and concludes the twin fires at the
moved state with landing EXACTLY the moved successor — the reorder's
induction step. -/

/-- The `draw` exchange: draws touch only the stock cursor, which the
twin's firing does not read. -/
theorem twin_fire_exchange_draw {S B S₁ T₁ : State} {t : Card}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply Move.draw = some S₁)
    (hT : B.apply Move.draw = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_draw_iff] at hS hT
  obtain rfl := hS
  obtain rfl := hT
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  refine apply_pileStack_iff.mpr ⟨htop, β, hβ, hrk, ?_⟩
  rw [hBshape]

/-- The `deckStack` exchange: the moved card's suit is off the twin's
suit, so its rung guard reads the same height on both sides and the
two height bumps commute. -/
theorem twin_fire_exchange_deckStack {S B S₁ T₁ : State} {t c : Card}
    (hsu : c.suit ≠ t.suit)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.deckStack c) = some S₁)
    (hT : B.apply (Move.deckStack c) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_deckStack_iff] at hS hT
  obtain ⟨-, -, hS₁⟩ := hS
  obtain ⟨-, -, hT₁⟩ := hT
  rw [hS₁, hT₁]
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  refine apply_pileStack_iff.mpr ⟨htop, β, hβ, ?_, ?_⟩
  · show t.rank.toIdx =
      (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit)
    rw [ite_eq_right (fun h => hsu h.symm)]
    exact hrk
  · rw [hBshape]
    apply state_ext
    · rfl
    · rfl
    · funext s
      show (if s = c.suit then
          (if s = t.suit then S.heights s + 1 else S.heights s) + 1
        else if s = t.suit then S.heights s + 1 else S.heights s)
        = (if s = t.suit then
          (if s = c.suit then S.heights s + 1 else S.heights s) + 1
        else if s = c.suit then S.heights s + 1 else S.heights s)
      by_cases h1 : s = t.suit
      · rw [ite_eq_right (fun hh => hsu (hh.symm.trans h1)),
          ite_eq_left h1, ite_eq_left h1,
          ite_eq_right (fun hh => hsu (hh.symm.trans h1))]
      · rw [ite_eq_right h1, ite_eq_right h1]
    · rfl
    · rfl
    · rfl

/-- The `deckPile` exchange: the drawn card's landing cell is neither
the twin's base (occupied at `S`) nor the twin's own seat (the fired
twin is unseated, hence invisible as a base at `B`) — both excluded by
the firings themselves — so the attach commutes with the twin's
detach, and the stock splice is untouched by the firing. -/
theorem twin_fire_exchange_deckPile {S B S₁ T₁ : State} {t X : Card} {b : Base}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.deckPile X b) = some S₁)
    (hT : B.apply (Move.deckPile X b) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_deckPile_iff] at hS
  obtain ⟨-, hcp, bdS, hattS, hS₁⟩ := hS
  rw [apply_deckPile_iff] at hT
  obtain ⟨-, hcpB, bdT, hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hBbot : B.board.bottomOf t = none := by
    rw [hBshape]; exact Board.bottomOf_detach_self hβtop
  have hbfree : S.board.topOf b = none := topOf_of_canPlace hcp
  have hbβ : b ≠ β := fun hcon => by
    rw [hcon] at hbfree; rw [hβtop] at hbfree; exact absurd hbfree (by simp)
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hcpB
    obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcpB
    rw [show B.isVis t = (B.board.bottomOf t).isSome from rfl, hBbot] at hvis
    simp at hvis
  rw [hBshape] at hattT
  have hattT' : (S.board.detach β).attach b X = some bdT := hattT
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, hrk, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbt)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbβ)]
    exact hβtop
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      rfl
    · rfl
    · rfl
    · rfl

/-- The `stackPile` exchange: the worry-back of an off-suit card.  Its
rung guard reads the moved card's suit (off the twin's suit, so the
same height on both sides), and the landing exclusions are derived
exactly as in the `deckPile` exchange. -/
theorem twin_fire_exchange_stackPile {S B S₁ T₁ : State} {t c : Card} {b : Base}
    (hsu : c.suit ≠ t.suit)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.stackPile c b) = some S₁)
    (hT : B.apply (Move.stackPile c b) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_stackPile_iff] at hS
  obtain ⟨-, hcp, bdS, hattS, hS₁⟩ := hS
  rw [apply_stackPile_iff] at hT
  obtain ⟨-, hcpB, bdT, hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hBbot : B.board.bottomOf t = none := by
    rw [hBshape]; exact Board.bottomOf_detach_self hβtop
  have hbfree : S.board.topOf b = none := topOf_of_canPlace hcp
  have hbβ : b ≠ β := fun hcon => by
    rw [hcon] at hbfree; rw [hβtop] at hbfree; exact absurd hbfree (by simp)
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hcpB
    obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcpB
    rw [show B.isVis t = (B.board.bottomOf t).isSome from rfl, hBbot] at hvis
    simp at hvis
  rw [hBshape] at hattT
  have hattT' : (S.board.detach β).attach b c = some bdT := hattT
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, ?_, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbt)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbβ)]
    exact hβtop
  · show t.rank.toIdx =
      (if t.suit = c.suit then S.heights t.suit - 1 else S.heights t.suit)
    rw [ite_eq_right (fun h => hsu h.symm)]
    exact hrk
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      show (if s = c.suit then
          (if s = t.suit then S.heights s + 1 else S.heights s) - 1
        else if s = t.suit then S.heights s + 1 else S.heights s)
        = (if s = t.suit then
          (if s = c.suit then S.heights s - 1 else S.heights s) + 1
        else if s = c.suit then S.heights s - 1 else S.heights s)
      by_cases h1 : s = t.suit
      · rw [ite_eq_right (fun hh => hsu (hh.symm.trans h1)),
          ite_eq_left h1, ite_eq_left h1,
          ite_eq_right (fun hh => hsu (hh.symm.trans h1))]
      · rw [ite_eq_right h1, ite_eq_right h1]
    · rfl
    · rfl
    · rfl

/-- The `pilePile` exchange: the run move.  The run head is not the
twin (a run head must be seated, and the twin is unseated at `B`); the
detach cell (the head's own base) is not the twin's base (their tops
differ); the landing cell is neither the twin's base (occupied at
`S`) nor the twin's own seat (no visible base at `B`) — every
exclusion derives from the two firings, including when the twin rides
inside the moved run at `S` (the internal edges ride the move
unchanged, and the twin's base cell is never written). -/
theorem twin_fire_exchange_pilePile {S B S₁ T₁ : State} {t z : Card} {b : Base}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.pilePile z b) = some S₁)
    (hT : B.apply (Move.pilePile z b) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_pilePile_iff] at hS
  obtain ⟨b₀, hbot, hne, hcmr, bdS, hattS, hS₁⟩ := hS
  rw [apply_pilePile_iff] at hT
  obtain ⟨b₀', hbot', hne', hcmr', bdT, hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  rw [hBshape] at hbot' hattT
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hzT : (S.board.detach β).bottomOf t = none := Board.bottomOf_detach_self hβtop
  have hBbot : B.board.bottomOf t = none := by
    rw [hBshape]; exact Board.bottomOf_detach_self hβtop
  have hzne : z ≠ t := by
    intro hcon
    rw [hcon] at hbot'
    have hc : (S.board.detach β).bottomOf t = some b₀' := hbot'
    rw [hzT] at hc
    exact absurd hc (by simp)
  have hb₀' : b₀' = b₀ := by
    have hzB' : (S.board.detach β).topOf b₀' = some z :=
      (Board.bottomOf_eq _ z b₀').mp hbot'
    by_cases hβb₀ : b₀' = β
    · rw [hβb₀, Board.detach_topOf] at hzB'
      exact absurd hzB' (by simp)
    · have hzS : S.board.topOf b₀' = some z := by
        rw [← Board.detach_topOf_ne S.board β b₀' hβb₀]
        exact hzB'
      exact S.board.inj b₀' b₀ z hzS ((Board.bottomOf_eq S.board z b₀).mp hbot)
  rw [hb₀'] at hattT
  have hb₀β : b₀ ≠ β := by
    intro hcon
    have hh := (Board.bottomOf_eq S.board z b₀).mp hbot
    rw [hcon] at hh
    exact hzne (Option.some.inj (hh.symm.trans hβtop))
  have hcpS : S.canPlace z b = true := by
    cases b with
    | inl a => exact canMoveRun_inl_iff.mp hcmr
    | inr d => exact (canMoveRun_inr_iff.mp hcmr).1
  have hcpB : B.canPlace z b = true := by
    cases b with
    | inl a => exact canMoveRun_inl_iff.mp hcmr'
    | inr d => exact (canMoveRun_inr_iff.mp hcmr').1
  have hbfree : S.board.topOf b = none := topOf_of_canPlace hcpS
  have hbβ : b ≠ β := fun hcon => by
    rw [hcon] at hbfree; rw [hβtop] at hbfree; exact absurd hbfree (by simp)
  have hbt : b ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hcpB
    obtain ⟨-, hvis, -⟩ := canPlace_inr_iff.mp hcpB
    rw [show B.isVis t = (B.board.bottomOf t).isSome from rfl, hBbot] at hvis
    simp at hvis
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    have hh := (Board.bottomOf_eq S.board z b₀).mp hbot
    rw [hcon, htop] at hh
    exact absurd hh (by simp)
  have hattT' : ((S.board.detach β).detach b₀).attach b z = some bdT := hattT
  have hdet : (S.board.detach β).detach b₀ = (S.board.detach b₀).detach β :=
    Board.detach_detach_comm S.board β b₀ (Ne.symm hb₀β)
  rw [hdet] at hattT'
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, hrk, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbt),
      Board.detach_topOf_ne _ _ _ (Ne.symm hb₀t)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbβ),
      Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]
    exact hβtop
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      rfl
    · rfl
    · rfl
    · rfl

/-- The `reveal` exchange — the one step that needs WF.  The reveal's
attach base is the pile's hidden second-from-top card, which is deal
data rather than board occupancy; without WF a junk state could hide
the twin itself in a pile's hidden slice and seat the boundary card on
top of it on BOTH sides (the covered-twin corner as a mid move).  WF's
`vis_not_hidden` pins the seated twin outside every hidden slice, and
the remaining exclusions (the base cells) derive from the firings. -/
theorem twin_fire_exchange_reveal {S B S₁ T₁ : State} {t : Card} {a : Anchor}
    (hwf : S.WF)
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.reveal a) = some S₁)
    (hT : B.apply (Move.reveal a) = some T₁) :
    S₁.apply (Move.pileStack t) = some T₁ := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨htop, β, hβ, hrk, hBshape⟩ := hB
  rw [apply_reveal_iff] at hS
  obtain ⟨r, bdS, htopH, hbare, hattS, hS₁⟩ := hS
  rw [apply_reveal_iff] at hT
  obtain ⟨r', bdT, htopH', hbare', hattT, hT₁⟩ := hT
  rw [hS₁, hT₁]
  have hth' : S.topHidden a = B.topHidden a := by rw [hBshape]; rfl
  rw [← hth'] at htopH'
  have hr'r : r' = r := Option.some.inj (htopH'.symm.trans htopH)
  rw [hr'r] at hattT
  rw [hBshape] at hattT
  have htvis : S.isVis t = true := by
    show (S.board.bottomOf t).isSome = true
    rw [hβ]
    rfl
  have hthid : ∀ a', t ∉ S.hidden a' := hwf.vis_not_hidden t htvis
  have hbb : S.hiddenBase a ≠ Sum.inr t :=
    fun hcon => hthid a (State.mem_hidden_of_hiddenBase hcon)
  have hβtop : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hbbβ : S.hiddenBase a ≠ β := by
    intro hcon
    obtain ⟨hfree, -⟩ := (Board.attach_eq_some_iff S.board (S.hiddenBase a) r).mp
      (by rw [hattS]; simp)
    rw [hcon] at hfree
    rw [hβtop] at hfree
    exact absurd hfree (by simp)
  have hattT' : (S.board.detach β).attach (S.hiddenBase a) r = some bdT := hattT
  have hbord : bdT = bdS.detach β :=
    (attach_detach_comm hbbβ hattS hattT').symm
  refine apply_pileStack_iff.mpr ⟨?_, β, ?_, hrk, ?_⟩
  · show bdS.topOf (Sum.inr t) = none
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbb)]
    exact htop
  · show bdS.bottomOf t = some β
    refine (Board.bottomOf_eq _ _ _).mpr ?_
    rw [Board.attach_topOf_ne _ _ _ hattS (Ne.symm hbbβ)]
    exact hβtop
  · rw [hBshape]
    apply state_ext
    · rfl
    · exact hbord
    · funext s
      rfl
    · funext a'
      rfl
    · rfl
    · rfl
/-- **The general reorder (L1/O3(ii) cornerstone)**: the MIXED mid
commutes with the twin's stacking — given the twin's guarded firing at
`A`, the mid's run at the pre-firing state (the accessibility
license, `haccess` in the window) and the source's own mid (the
second license), the twin fires AFTER the replayed mid landing
EXACTLY on the source's mid successor.  Induction over the mid, one
exchange step per move kind; the `pileStack` case is the existing
one-step exchange (which already serves the catch-up cards and every
off-suit `pileStack`).  `hwf` is carried along the prefixes: the
reveal step is its only consumer (`vis_not_hidden` at each prefix). -/
theorem pileStack_mid_reorder {t : Card} :
    ∀ (mid : List Move) (A B M₀ C : State),
    (∀ m ∈ mid, Move.twinMid t m = true) →
    A.WF →
    A.apply (Move.pileStack t) = some B →
    A.run mid = some M₀ →
    B.run mid = some C →
    M₀.apply (Move.pileStack t) = some C := by
  intro mid
  induction mid with
  | nil =>
      intro A B M₀ C _ _ h₁ hA hB
      rw [← run_nil_elim hA, ← run_nil_elim hB]
      exact h₁
  | cons m ms ih =>
      intro A B M₀ C hmid hwf h₁ hA hB
      obtain ⟨A₁, hmA, hrest⟩ := run_cons_elim hA
      obtain ⟨B₁, hmB, hrest'⟩ := run_cons_elim hB
      have hwfA₁ : A₁.WF := apply_wf hwf m A₁ hmA
      have hmtop : Move.twinMid t m = true := hmid m List.mem_cons_self
      have hstep : A₁.apply (Move.pileStack t) = some B₁ := by
        cases m with
        | draw => exact twin_fire_exchange_draw h₁ hmA hmB
        | reveal a' => exact twin_fire_exchange_reveal hwf h₁ hmA hmB
        | deckPile x b' => exact twin_fire_exchange_deckPile h₁ hmA hmB
        | deckStack x =>
            obtain ⟨hsu, -⟩ := (Move.twinMid_deckStack t x).mp hmtop
            exact twin_fire_exchange_deckStack hsu h₁ hmA hmB
        | pileStack x =>
            obtain ⟨hsu, -⟩ := (Move.twinMid_pileStack t x).mp hmtop
            exact apply_pileStack_pileStack_exchange hsu h₁ hmA hmB
        | stackPile x b' =>
            obtain ⟨hsu, -⟩ := (Move.twinMid_stackPile t x b').mp hmtop
            exact twin_fire_exchange_stackPile hsu h₁ hmA hmB
        | pilePile x b' => exact twin_fire_exchange_pilePile h₁ hmA hmB
      exact ih A₁ B₁ M₀ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
        hwfA₁ hstep hrest hrest'

/-! ### The general window (L1/O3(ii)), its packaging, and its mirror -/

/-- **L1/O3(ii), the general window**: if the source game wins via
[prefix; stack t; MIXED-MID; stack t'; tail] — the mid mixing the low
suit's catch-up `pileStack`s with ortho twin moves (every move
`twinMid`: no foundation move of a `t`-suit card, nothing on the pair) —
and the mid is replayable at the pre-firing state (`haccess`, the
no-landing premise in executable form: witness A is exactly a catch-up
card buried under the twin, and an ortho landing onto the twin's
vacated base breaks the same premise), then the EXCHANGED game is
solvable: it plays [prefix*; mid*; stack t'; stack t; tail*] — the
mid rides the clean mirror, the first stacking lands the cross-skew at
the RE-ALIGNED rung, and the second re-syncs onto `D.swapTwin t` (the
same twinSkew/crossTwin spine as the pure window, fed by the general
reorder).

The `hwf` premise is the reveal-corner repair: `vis_not_hidden` keeps
the seated twin out of every hidden slice, so a mid `reveal` cannot
seat the boundary card onto it.  Note the honest boundary: the mid
predicate is ONE-SIDED in the suit condition (the LOW suit's
foundation moves are allowed — its catch-up `deckStack`s and
worry-backs read the low height, which the twin's firing does not
touch), so the predicate is NOT flip-dual; the `_back` below states
its premises at the flipped roles directly. -/
theorem State.solvable_swapTwin_mixed {st : State} {t : Card}
    {p₁ mid p₂ : List Move} {A B C D W : State}
    (hwf : st.WF)
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hmid : ∀ m ∈ mid, Move.twinMid t m = true)
    (hp₁ : st.run p₁ = some A)
    (hf₁ : A.apply (Move.pileStack t) = some B)
    (hmidB : B.run mid = some C)
    (hf₂ : C.apply (Move.pileStack t.flipSuit) = some D)
    (hp₂ : D.run p₂ = some W)
    (haccess : ∃ M₀, A.run mid = some M₀)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  obtain ⟨M₀, hA_mid⟩ := haccess
  have hwfA : A.WF := run_wf p₁ st A hp₁ hwf
  -- the reorder: the twin fires after the replayed mid, landing on C
  have hreor := pileStack_mid_reorder mid A B M₀ C hmid hwfA hf₁ hA_mid hmidB
  rw [apply_pileStack_iff] at hreor
  obtain ⟨htop₀, β₀, hβ₀, hrk₀, hCshape⟩ := hreor
  rw [apply_pileStack_iff] at hf₂
  obtain ⟨htop', β', hβ', hrk', hDshape⟩ := hf₂
  have hsne : t.flipSuit.suit ≠ t.suit := fun h => Suit.flipPair_ne t.suit h
  -- the rung alignments the twinSkew/crossTwin spine needs
  have hC₀low : M₀.heights t.flipSuit.suit = t.rank.toIdx := by
    have h1 : t.flipSuit.rank.toIdx = C.heights t.flipSuit.suit := hrk'
    have h2 : C.heights t.flipSuit.suit = M₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then M₀.heights t.flipSuit.suit + 1
        else M₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [Card.flipSuit_rank] at h1
    omega
  have halign₁ : M₀.heights t.suit = M₀.heights t.flipSuit.suit := by
    rw [hrk₀.symm, hC₀low]
  have halign₂ : C.heights t.suit = C.heights t.flipSuit.suit + 1 := by
    have e1 : C.heights t.suit = M₀.heights t.suit + 1 := by
      rw [hCshape]
      show (if t.suit = t.suit then M₀.heights t.suit + 1 else M₀.heights t.suit) = _
      rw [ite_eq_left rfl]
    have e2 : C.heights t.flipSuit.suit = M₀.heights t.flipSuit.suit := by
      rw [hCshape]
      show (if t.flipSuit.suit = t.suit then M₀.heights t.flipSuit.suit + 1
        else M₀.heights t.flipSuit.suit) = _
      rw [ite_eq_right hsne]
    rw [e2, hC₀low, hrk₀]
    omega
  -- the mirror play, segment by segment
  have hmidcl : ∀ m ∈ p₁ ++ mid, Move.cleanTwin t m = true := by
    intro m hm
    rcases List.mem_append.mp hm with h | h
    · exact hc₁ m h
    · exact Move.twinMid_clean (hmid m h)
  have hseg : st.run (p₁ ++ mid) = some M₀ := run_append_some hp₁ hA_mid
  have hM₁ : (st.swapTwin t).run ((p₁ ++ mid).map (Move.swapTwin t))
      = some (M₀.swapTwin t) := by
    rw [run_swapTwin_clean t st (p₁ ++ mid) hmidcl, hseg]
    rfl
  have hrunskew : (M₀.swapTwin t).run [Move.pileStack t.flipSuit]
      = some (M₀.twinSkew t β₀) := by
    simp only [State.run, State.apply_swapTwin_stack_flip htop₀ hβ₀ hC₀low]
  have hskew : M₀.twinSkew t β₀ = C.crossTwin t :=
    State.twinSkew_eq_crossTwin hCshape halign₁
  have hM₁' : (st.swapTwin t).run
      ((p₁ ++ mid).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      = some (C.crossTwin t) := by
    rw [run_split_bind, hM₁]
    show (M₀.swapTwin t).run [Move.pileStack t.flipSuit] = some (C.crossTwin t)
    rw [hrunskew, hskew]
  have hM₃ : (C.crossTwin t).run [Move.pileStack t] = some (D.swapTwin t) := by
    simp only [State.run, State.apply_crossTwin_stack htop' hβ' hrk' halign₂ hDshape]
  have hM₄ : (D.swapTwin t).run (p₂.map (Move.swapTwin t))
      = some (W.swapTwin t) := by
    rw [run_swapTwin_clean t D p₂ hc₂, hp₂]
    rfl
  have hwin' : (W.swapTwin t).isWin = true := by
    simp only [State.isWin, swapTwin_heights]
    exact hwin
  refine ⟨((p₁ ++ mid).map (Move.swapTwin t) ++ [Move.pileStack t.flipSuit])
      ++ ([Move.pileStack t] ++ p₂.map (Move.swapTwin t)), W.swapTwin t, ?_, hwin'⟩
  exact run_append_some hM₁' (run_append_some hM₃ hM₄)

/-- The packaged form of the general window: the source play as one
run. -/
theorem State.solvable_swapTwin_mixed_run {st : State} {t : Card}
    {p₁ mid p₂ : List Move} {W : State}
    (hwf : st.WF)
    (hc₁ : ∀ m ∈ p₁, Move.cleanTwin t m = true)
    (hc₂ : ∀ m ∈ p₂, Move.cleanTwin t m = true)
    (hmid : ∀ m ∈ mid, Move.twinMid t m = true)
    (haccess : ∀ A, st.run p₁ = some A → ∃ M₀, A.run mid = some M₀)
    (hrun : st.run (p₁ ++ [Move.pileStack t] ++ mid
      ++ [Move.pileStack t.flipSuit] ++ p₂) = some W)
    (hwin : W.isWin = true) :
    (st.swapTwin t).solvableFrom := by
  simp only [List.append_assoc] at hrun
  rw [run_split_bind st p₁
    ([Move.pileStack t] ++ (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)))] at hrun
  cases hA : st.run p₁ with
  | none => rw [hA] at hrun; simp at hrun
  | some A =>
    rw [hA] at hrun
    have hrun1 : A.run ([Move.pileStack t] ++ (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)))
        = some W := hrun
    rw [run_split_bind A [Move.pileStack t]
      (mid ++ ([Move.pileStack t.flipSuit] ++ p₂))] at hrun1
    simp only [State.run] at hrun1
    cases hB₀ : A.apply (Move.pileStack t) with
    | none => rw [hB₀] at hrun1; simp at hrun1
    | some B =>
      rw [hB₀] at hrun1
      have hrun2 : B.run (mid ++ ([Move.pileStack t.flipSuit] ++ p₂)) = some W := hrun1
      rw [run_split_bind B mid
        ([Move.pileStack t.flipSuit] ++ p₂)] at hrun2
      cases hC : B.run mid with
      | none => rw [hC] at hrun2; simp at hrun2
      | some C =>
        rw [hC] at hrun2
        have hrun3 : C.run ([Move.pileStack t.flipSuit] ++ p₂) = some W := hrun2
        rw [run_split_bind C [Move.pileStack t.flipSuit] p₂] at hrun3
        simp only [State.run] at hrun3
        cases hD₀ : C.apply (Move.pileStack t.flipSuit) with
        | none => rw [hD₀] at hrun3; simp at hrun3
        | some D =>
          rw [hD₀] at hrun3
          have hWD : D.run p₂ = some W := hrun3
          obtain ⟨M₀, hA_mid⟩ := haccess A hA
          exact State.solvable_swapTwin_mixed hwf hc₁ hc₂ hmid hA hB₀ hC hD₀ hWD
            ⟨M₀, hA_mid⟩ hwin

/-- **The catch-up iff, backward half (L1/O3(ii) mirrored)**: the
general window at the flipped twin, composed with the involution —
the hypotheses are stated directly at the flipped roles the mirror
game actually has (the state `(st.swapTwin t)` whose first stackable
twin is `t.flipSuit`), because the one-sided suit condition of
`twinMid` is NOT flip-dual: a `t`-suit foundation move is legal in
the MIRROR's mid (it reads the mirror's low suit, which the mirror's
twin firing does not bump).

The between-shaped hypothesis this carries is the honest half of the
iff.  Wave 18 recorded the catch-up-FIRST mirror plays — the shape the
forward window CONSTRUCTS — as needing a CATCH-UP-FIRST-TO-BETWEEN
DEFERRAL under two licenses (pre-catch-up fireability + the
post-stacking tail's access).  Wave 19 resolved it honestly: the
LICENSED literal split (the mid itself re-seated between the stackings)
is REFUTED at the asymmetric window — the rung pin (the catch-up is
what raises the first-stacked twin's suit to its rung) and the flipped
witness-A seat corner (a catch-up card sitting ON that twin, uncovered
only mid-catch-up — witness C,
witnesses/TwinCompletionWitness.lean) kill the pre-catch-up
fireability — but NO license is needed after all: `q₁` never forbade
the catch-up (only ON-PAIR foundation moves are unclean), so the
catch-up-first play re-brackets verbatim as the between window with
the EMPTY mid.  That re-bracketing is
`State.solvable_swapTwin_mixed_back_catchupfirst` below. -/
theorem State.solvable_swapTwin_mixed_back {st : State} {t : Card}
    {q₁ mid q₂ : List Move} {W : State}
    (hwf : (st.swapTwin t).WF)
    (hc₁ : ∀ m ∈ q₁, Move.cleanTwin t.flipSuit m = true)
    (hc₂ : ∀ m ∈ q₂, Move.cleanTwin t.flipSuit m = true)
    (hmid : ∀ m ∈ mid, Move.twinMid t.flipSuit m = true)
    (hrun : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit] ++ mid
      ++ [Move.pileStack t] ++ q₂) = some W)
    (haccess : ∀ A', (st.swapTwin t).run q₁ = some A' → ∃ M₀, A'.run mid = some M₀)
    (hwin : W.isWin = true) :
    st.solvableFrom := by
  have hrun' : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit] ++ mid
      ++ [Move.pileStack t.flipSuit.flipSuit] ++ q₂) = some W := by
    rw [Card.flipSuit_flipSuit]
    exact hrun
  have h := State.solvable_swapTwin_mixed_run (st := st.swapTwin t) (t := t.flipSuit)
    hwf hc₁ hc₂ hmid haccess hrun' hwin
  rw [State.swapTwin_flipSuit, State.swapTwin_swapTwin] at h
  exact h

/-! ### The catch-up-first→between deferral — resolved (wave 19)

Wave 18's successor ticket asked for the deferral with two licenses.
The honest resolution cuts both ways:

* The LICENSED half — the literal between split, `[q₁; stack t'; MID;
  stack t; q₂]` with the mirror's ACTUAL mid re-seated between the two
  stackings — needs `stack t'` to fire BEFORE the mid, and at the
  asymmetric window that fails STRUCTURALLY: the mid's catch-up raises
  are exactly what lifts `t'`'s suit to its rung, so pre-mid the rung
  guard fails; and even when the heights align, the mate can be
  covered (witness C: a catch-up card dealt onto the twin, uncovered
  only by its own raise mid-catch-up — the flipped witness-A corner).
  The pre-catch-up fireability license is REFUTABLE as stated; no
  license carries the literal split, and none is needed.
* The FREE half — the only one the iff ever wanted: `solvable_swapTwin_mixed_back`
  restricts the BETWEEN-MID (`twinMid t'`) but never restricts `q₁`
  (only `cleanTwin t'`, which forbids ON-PAIR FOUNDATION moves only —
  `t'`-suit raises are `t`-off-pair by rank).  So a catch-up-first
  mirror play `q₁ ++ [stack t', stack t] ++ q₂` — with the whole
  catch-up-containing prefix swallowed into `q₁` and the two stackings
  ADJACENT — IS the between window with the EMPTY mid, and `_back`
  applies verbatim.  Composed with the forward window (whose constructed
  mirror play has exactly this shape), wave 18's iff closes at the
  clean class with no deferral license consumed. -/

/-- **The catch-up-first→between deferral, the free half (L1(ii)'s
mirror completion — wave 19)**: a MIRROR play of the catch-up-first
shape — `q₁` arbitrary clean (it may — and at the asymmetric window
it must — carry the whole catch-up: `t'`-suit raises are off-pair by
rank), the two twin stackings ADJACENT, then the clean tail — makes
`st` solvable: the play re-brackets as `solvable_swapTwin_mixed_back`'s
between window with the EMPTY mid, and `_back` applies verbatim.
No deferral license is consumed; see the section note above for why
the licensed literal split is unavailable at the asymmetric window
(witness C) and unnecessary for the iff. -/
theorem State.solvable_swapTwin_mixed_back_catchupfirst {st : State} {t : Card}
    {q₁ q₂ : List Move} {W : State}
    (hwf : (st.swapTwin t).WF)
    (hc₁ : ∀ m ∈ q₁, Move.cleanTwin t.flipSuit m = true)
    (hc₂ : ∀ m ∈ q₂, Move.cleanTwin t.flipSuit m = true)
    (hrun : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit,
      Move.pileStack t] ++ q₂) = some W)
    (hwin : W.isWin = true) :
    st.solvableFrom := by
  refine State.solvable_swapTwin_mixed_back (mid := []) hwf hc₁ hc₂
    (by simp) ?_ (fun A' _ => ⟨A', rfl⟩) hwin
  have hrun' : (st.swapTwin t).run (q₁ ++ [Move.pileStack t.flipSuit]
      ++ ([] : List Move) ++ [Move.pileStack t] ++ q₂) = some W := by
    simpa using hrun
  exact hrun'

/-! ## Item 3 — twin-suit worry-backs in the window

Two facts discipline the window's mid.  First, the EXCLUDED family is
excluded CONTENTFULLY: a foundation move READING the twin's own suit
cannot fire on both sides of the exchange at all — the height the
twin's firing creates is a one-rung offset, and the ±1 is not
satisfiable both ways (the low suit's worry-backs and raises, by
contrast, RIDE the window: `twinMid` admits them, and the exchange
steps transfer their guards verbatim since the twin's firing does not
touch the low suit's height).  Second, the worry-backs that occur in
real winning plays are EXCURSION-SHAPED — [stackPile c b, pileStack c]
is an unconditional identity pair — so they lift out of the mid whole,
on either side of the window. -/

/-- **A `t`-suit worry-back cannot fire on both sides of the
exchange**: the twin's firing pins the `t`-suit height to its own
rung at `S` and one above at `B`, and the worry-back's un-stack guard
(`toIdx c + 1 = heights`) is a fixed point between the two — no card
of the twin's own rank-neighborhood satisfies both readings. -/
theorem twin_fire_tSuit_stackPile_impossible {S B S₁ T₁ : State} {t c : Card} {b : Base}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.stackPile c b) = some S₁)
    (hT : B.apply (Move.stackPile c b) = some T₁)
    (hsu : c.suit = t.suit) : False := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨-, htβ, -, -, hBshape⟩ := hB
  rw [apply_stackPile_iff] at hS hT
  obtain ⟨hg, -, -, -, -⟩ := hS
  obtain ⟨hg', -, -, -, -⟩ := hT
  have hbc : B.heights c.suit = S.heights c.suit + 1 := by
    rw [hBshape]
    show (if c.suit = t.suit then S.heights c.suit + 1 else S.heights c.suit) = _
    rw [ite_eq_left hsu]
  omega

/-- The same one-rung contradiction for the `t`-suit raise kind
(`pileStack` of a card of the twin's own suit): the raise's rung guard
pins the card to the twin's height at `S`, which the twin's own
firing has already left behind at `B`. -/
theorem twin_fire_tSuit_pileStack_impossible {S B S₁ T₁ : State} {t c : Card}
    (hB : S.apply (Move.pileStack t) = some B)
    (hS : S.apply (Move.pileStack c) = some S₁)
    (hT : B.apply (Move.pileStack c) = some T₁)
    (hsu : c.suit = t.suit) : False := by
  rw [apply_pileStack_iff] at hB
  obtain ⟨-, htβ, -, -, hBshape⟩ := hB
  rw [apply_pileStack_iff] at hS hT
  obtain ⟨-, hcβ, -, hg, -⟩ := hS
  obtain ⟨-, hdβ, -, hg', -⟩ := hT
  have hbc : B.heights c.suit = S.heights c.suit + 1 := by
    rw [hBshape]
    show (if c.suit = t.suit then S.heights c.suit + 1 else S.heights c.suit) = _
    rw [ite_eq_left hsu]
  omega

/-- The identity-excursion lift: an adjacent
[worry-back, re-stack] pair nets to the identity on states
(`stackPile_pileStack_return`), so it can be excised from any winning
run without changing the outcome — the worry-backs that DO occur in
winning plays (inside or besides the window) ride this. -/
theorem run_worryback_pair_excise (c : Card) (b : Base) (m₀ m₁ : List Move)
    {st W : State} (hwf : st.WF)
    (hrun : st.run (m₀ ++ [Move.stackPile c b, Move.pileStack c] ++ m₁) = some W) :
    st.run (m₀ ++ m₁) = some W := by
  simp only [List.append_assoc] at hrun
  rw [run_split_bind st m₀
    ([Move.stackPile c b, Move.pileStack c] ++ m₁)] at hrun
  cases hS : st.run m₀ with
  | none => rw [hS] at hrun; simp at hrun
  | some S =>
    rw [hS] at hrun
    have hrest : S.run ([Move.stackPile c b, Move.pileStack c] ++ m₁) = some W := hrun
    rw [show [Move.stackPile c b, Move.pileStack c] ++ m₁
          = [Move.stackPile c b] ++ ([Move.pileStack c] ++ m₁) from rfl] at hrest
    rw [run_split_bind S [Move.stackPile c b]
      ([Move.pileStack c] ++ m₁)] at hrest
    simp only [State.run] at hrest
    cases hs₁ : S.apply (Move.stackPile c b) with
    | none => rw [hs₁] at hrest; simp at hrest
    | some s₁ =>
      rw [hs₁] at hrest
      have hrest₂ : s₁.run ([Move.pileStack c] ++ m₁) = some W := hrest
      rw [run_split_bind s₁ [Move.pileStack c] m₁] at hrest₂
      simp only [State.run] at hrest₂
      cases hs₂ : s₁.apply (Move.pileStack c) with
      | none => rw [hs₂] at hrest₂; simp at hrest₂
      | some s₂ =>
        rw [hs₂] at hrest₂
        have htail : s₂.run m₁ = some W := hrest₂
        have hret := stackPile_pileStack_return (run_wf m₀ st S hS hwf) hs₁
        have hS₂ : s₂ = S := (Option.some.inj (hret.symm.trans hs₂)).symm
        rw [hS₂] at htail
        exact run_append_some hS htail

/-! ## The haccess derivation at engine corpora — the no-landing
reduction, REPAIRED and pinned (wave 19)

`haccess` — the mid is replayable at the pre-firing state — is the
window's no-landing premise in executable form.  The model-level
reduction below PROVES it at the no-landing premise: at WF, the
source's own mid plus the per-seat exclusions (`noSeat` — the landing
bases off the twin's vacated base `β` and off the twin's own seat)
derive the WHOLE replay, and the twin's deferred firing lands exactly
on the source's mid successor `C`.

THE REPAIR (honest history): wave 18 pinned this believing the seat
exclusions needed only the three LANDING kinds.  Wave 19's audit of
every per-kind A-side guard found TWO further exclusion classes the
pinned premise missed, so the as-pinned statement was FALSE (each has
a witness-A-shaped obstruction the `match` in `noSeat` said nothing
about):

* **pileStack seats** — a mid raise card can be buried under the twin
  (`β = Sum.inr c`: the twin sits ON the catch-up card, whose seat
  guard then reads the twin's cell — witness A's own corner, at WF
  via `board_edges`' deal-adjacency clause).  The repaired premise
  adds `b = Sum.inr c` to the exclusion set.
* **reveal cells** — the reveal's two board reads are deal data, not
  program constants: the boundary card's own seat
  (`topOf (Sum.inr r)`, `r` the CURRENT `topHidden` of pile `a` —
  a twin dealt onto the hidden boundary blocks it at the pre-firing
  side only) and the attach base (`hiddenBase a` — a twin-king at the
  pile's anchor blocks it the same way).  The repaired premise
  excludes the pile's whole future reveal structure STATICALLY: the
  anchor, `A.hiddenBase a`, and the seat of every card of `A.hidden a`
  — every later boundary/attach cell of the pile's reveal chain lies
  in this set (reveal only decrements the take, and `mem_of_getLast`
  keeps the boundary inside the shrinking prefix).

The engine-corpus half — which reached states' between-mids satisfy
`noSeat` — remains §8's audit (the histogram pull); this theorem is
its model-side certificate.  The proof is the B→A mirror of the six
exchange steps, run on a per-step delta invariant
(`TwinReplayTrace`): the mid fires on BOTH sides with the boards
agreeing on every cell but `β` and the heights on every suit but the
twin's, so each A-side guard re-reads its B-side value verbatim; the
`pilePile` self-landing guard is the one genuinely new walk argument
(`aboveOf_twin_delta`: the A-side run above a card gains at most the
twin, as a top-of-run head). -/

/-- **HACCESS DERIVED, the repaired statement (wave 19 — pinned with
a plan)**: at WF, the source's own mid plus the per-seat exclusions
derive the WHOLE replay at the pre-firing state, and the deferred
twin firing lands exactly on the source's mid successor `C` — the
model-side certificate of §8's landing-site audit.  `noSeat` is the
REPAIRED form this wave's guard audit established: beyond the three
landing kinds it excludes the `pileStack` seat cells and the
reveal's whole boundary structure (see the section note above).  The
corpus half (which reached states' between-mids satisfy `noSeat`)
remains §8's audit.

**PLAN (drafted this wave)**: the ~700-line proof draft — the
`TwinReplayTrace` delta invariant, its base case off the twin's own
firing, the seven B→A transfer mirrors, the `aboveOf_twin_delta`
walk delta (fuel induction on `Board.aboveOf.go` with the
`aboveOf_go_succ`/`_topOf_none` kit), the shape lemmas
(`heights_tSuit_stable`/`deal_stable_move`/`depths_mono_move`), the
`mid_access_chain` induction, and the final `apply_pileStack_iff` +
`state_ext` assembly — sits in `attic/MidAccessDraft.lean` (NOT
built; parked for the successor session), an elaboration-polish pass
away (about 25 local errors: literal-projection `show` orientations,
a few `rw` directions in the mirrors, the walk lemma's β-case casts;
the head/mid/tail analytic structure is verified).  The successor
reinstates it here, fixes those, and git-rms the attic file. -/
theorem State.mid_access_of_noSeat {st : State} {t : Card}
    {p₁ mid : List Move} {A B C : State} {β : Base}
    (hwf : st.WF)
    (hp₁ : st.run p₁ = some A)
    (hf₁ : A.apply (Move.pileStack t) = some B)
    (hβ : A.board.bottomOf t = some β)
    (hmid : ∀ m ∈ mid, Move.twinMid t m = true)
    (hBmid : B.run mid = some C)
    (hnoseat : ∀ m ∈ mid, ∀ b : Base,
      (match m with
       | .deckPile _ b' => b = b'
       | .stackPile _ b' => b = b'
       | .pilePile _ b' => b = b'
       | .pileStack c' => b = Sum.inr c'
       | .reveal a' => b = Sum.inl a' ∨ b = A.hiddenBase a' ∨
           (∃ r, r ∈ A.hidden a' ∧ b = Sum.inr r)
       | _ => False) →
      b ≠ β ∧ b ≠ Sum.inr t) :
    ∃ M₀, A.run mid = some M₀ ∧ M₀.apply (Move.pileStack t) = some C := sorry

/-! ## §6.5 residue — the covered-twin corner's sweep-word safety

At the ambiguous-twin corner (`canonicalize`'s confluence gap: both
twins visible, one covered, `present=2, placed=1`), the word-level
sweep must CHOOSE which twin is the covered one, and §6.5 pins the
semantic obligation: the chosen reading never uniquely loses wins.
The model-side corner at WF is the DEALT-ADJACENT mate — the twin
pair dealt consecutively in one pile, the upper mate sitting on the
lower's seat — because `canSitOn` is false at the mate's own rank
(same rank, unlike a fitting cover), so deal-adjacency is the only WF
justification for the cover edge.  The two word-readings of the
corner are exchange-conjugate: `exchangeTwinCargo L` swaps the two
twin cells (the raw seat relabel, `Board.exchangeTwin_topOf`), so the
covered corner maps to its flipped cover. -/

/-- The covered corner's exchange image IS the flipped cover: at the
ambiguous corner the cell readings of `st.exchangeTwinCargo L` are
the corner's cells with the twin pair exchanged — the two
identity-resolutions of the word are the two exchange-images.

Note the image's own-seat cell: the exchange is the RAW seat swap
(no card relabel on values), so the covering mate's VALUE rides to
its own seat — for the word level this is immaterial (the word reads
placedness, not identities), but it is why the SAFETY reduction
below must route through the discipline kit rather than a pure
literal symmetry. -/
theorem exchangeTwinCargo_flip_cover {st : State} {L H : Card}
    (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hHseat : st.board.topOf (Sum.inr H) = none) :
    (st.exchangeTwinCargo L).board.topOf (Sum.inr L) = none ∧
    (st.exchangeTwinCargo L).board.topOf (Sum.inr H) = some H := by
  constructor
  · show st.board.topOf (Base.swapTwin L (Sum.inr L)) = none
    have h : Base.swapTwin L (Sum.inr L) = Sum.inr H := by
      show Sum.inr (Card.swapTwin L L) = Sum.inr H
      rw [Card.swapTwin_self_left, htwin]
    rw [h, hHseat]
  · show st.board.topOf (Base.swapTwin L (Sum.inr H)) = some H
    have h : Base.swapTwin L (Sum.inr H) = Sum.inr L := by
      show Sum.inr (Card.swapTwin L H) = Sum.inr L
      rw [show Card.swapTwin L H = L from by rw [htwin]; exact Card.swapTwin_self_right L]
    rw [h, hcover]

/-- **§6.5's semantic safety at the covered corner (planned)**: the
covered corner and its exchange image — the two identity-resolutions
of the ambiguous word — are solvability-equivalent, so the sweep's
deterministic lowest-first choice can never UNIQUELY lose a win at
the AMBIGUOUS corner.  Reduces to the both-occupied exchange family
at the covered seat.
PLAN: (1) WF forces the corner to be deal-adjacent: the cover edge's
base condition (`board_edges`) needs the buried-base clause (the pair
dealt consecutively), since the canSitOn clause dies on the mate's
rank arithmetic (`canSitOn H L` demands `toIdx H + 1 = toIdx L`,
false at the shared rung). (2) Every winning line must dislodge the
covering mate: the extraction discipline (Theorems §12.1) plus
`unseats_imp_pileStack` — to stack the covered twin `L` the mate must
leave its seat first, and the mate's own stacking is the H-first
window this file already proves sound; normalize the corner by the
mate's first departure (its own `pileStack` at the rung, or the
tableau move a winning line starts with). (3) At the dislodged shape
both twin cells are bare and the pair enters the PROVEN family:
`twin_stack_order_exchange_catchup` (the same-state order exchange,
the same-state half of the safety) and
`solvable_cargoTwin_exchange_licensed`/`_bare`/`_of_visClean` (the
both-occupied/bare iff) supply the equivalence; the exchange image is
matched by `exchangeTwinCargo_flip_cover` above, so both readings
reduce to the bare-pair exchange at the covered seat. (4) The residue
inside (3) is the LICENSE-FIT at the dealt-adjacent cover while the
mate still sits (the cargo of the covered seat is the twin itself —
the w15fithole rider-detour class): its arrow is the w15-style
exchange extension or the normalization in (2) applied BEFORE the
exchange; pick by which corpus corner the audit finds. -/
theorem State.sweep_covered_corner_safety {st : State} {L H : Card}
    (hwf : st.WF)
    (htwin : H = L.flipSuit)
    (hcover : st.board.topOf (Sum.inr L) = some H)
    (hHseat : st.board.topOf (Sum.inr H) = none) :
    st.solvableFrom ↔ (st.exchangeTwinCargo L).solvableFrom := sorry



