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
