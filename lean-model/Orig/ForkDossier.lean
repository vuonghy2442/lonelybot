import Orig.MacroInternal

/-!
# Orig.ForkDossier — the fork-point program, relocated and archived
(the 2026-10-17 owner decision)

The dossier tier that read through `forkPointC`/`forkPoint` (the
V3-calibrated witness-pair geometry and its projection) moved here
VERBATIM from `Orig/MacroInternal.lean` — the noise-reduction
request: the S-grade detection (`forkState`, in `Orig.MacroInternal`
beside `CanRaiseS`) is the practical interface, the arm language
`forkedCard` stays put (the live classification rows at
`Orig/ConeCrossarm.lean` state themselves in it, and
`benign_sat_iff_surely`'s premise reads it), while the fork-point
PROGRAM — the per-state witness geometry and its class-level
targets — is dormant ahead of classification consumers and archived
here.

WHAT THIS FILE HOLDS (every statement byte-identical to its former
`Orig/MacroInternal.lean` text; the seven frozen rows keep their
`sorry`s verbatim — never retry as stated):

* §1 THE VOCABULARY: `cargoTop`, `forkPointC` (the V3-calibrated
  form), `forkPoint`, `afterFork`, `PairCfg`.
* §2 THE FROZEN TARGETS (sorries kept): `forkedCard_iff_forkPoint`
  (the bridge — both anchors import-visible), `forkPoint_classifies`,
  `fork_threeCases`, `fork_threeCards`, `afterFork_fewFinals`,
  `afterFork_neckReachable`, and `forkPoint_trial` (the exposure-tail
  residue inside).
* §3 THE PROVED SATELLITES (re-audited below): `forkPoint_pins`,
  `forkPoint_exclusive` (the cross-pair rank sandwich), with the
  private kit the proofs consume (`piled_rung`,
  `forkPoint_cargo_strand`, `nodup_snoc_notmem`,
  `not_twinSuit_colors`, `twinSuit_symm`, `suitfamily_antipodal`,
  `cross_pin` — the house dedup discipline's per-file copies).

House compliance: additive leaf, NOT wired into the root (mirroring
the MacroInternal discipline); zero new sorries — the frozen rows
keep their frozen residues; every proved head audited
(`#print axioms` — expected `[propext]`/`[propext, Quot.sound]`,
zero `Classical.choice`). -/

/-! ## §1. The vocabulary -/

/-- The cargo reading: `d` TOPS the twin's pile — the twin sits beneath
it, covered by construction. -/
def cargoTop (st : State) (d c : Card) : Prop :=
  ∃ a, st.pileOfTop d = some a ∧ st.pileHolding c = some a

/-- **The fork point with its cargo as first-class witness** — the
V3-CALIBRATED form.  V2 (the floor card's batch-F diagnosis) fixed
the bare twin (vanilla at the point) and the covered pin (premise);
the canon-v3 wake's (Q, J) falsifier analysis found the remaining
under-carried leg — the SEAT: a covered twin sitting BARE-BOTTOM
under its cargo (empty under-seat, non-king) satisfies every V2
conjunct yet cannot lift vanilla once exposed.  V3 adds the seat
premise the trial's own rank arithmetic already wanted: the cargo
sits DIRECTLY on the twin (the run discipline is rank-consecutive
upward — consecutive ranks admit no intermediates, so the
witness-pair shape is honest) and the twin carries the license's
seat package (under-seat content, or a bare king):
`faceUp = bs ++ [x.twin, d]` with `bs ≠ [] ∨ (hidden = [] ∧
king)`.  NO global king restriction — the sandwich's color-family
placement never needs it, and generic-rank forking is honest at
any rank with the seat clause. -/
def forkPointC (st : State) (x d : Card) : Prop :=
  CanRaise st x ∧
  rungAt st x.twin.suit = x.rank.toIdx ∧
  cargoTop st d x.twin ∧
    d.rank.toIdx + 1 = x.rank.toIdx ∧ ¬ twinSuit d.suit x.suit ∧
    ¬ satStackable (Quotient.mk sameOrbitSetoid st) d ∧
    ∃ a bs, st.pileOfTop d = some a ∧
      (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      (bs ≠ [] ∨ ((st.piles a).hidden = [] ∧ x.twin.rank = Rank.king))

/-- **The fork point** (the live signature, existentially packaged): one
twin stackable in the cargo-exchange sense, the other twin topped by a
cargo card non-stackable in the macro state. -/
def forkPoint (st : State) (x : Card) : Prop := ∃ d, forkPointC st x d

/-- **After the fork** (class-level): the decision has been taken —
some satStackable card is NO LONGER surelyStackable; the pair's
stackedness became arm-contingent. -/
def afterFork (C : SameOrbit) : Prop := ∃ c, forkedCard C c

/-- **The pair configuration** — the three cases: at any member, the
fork pair {x, x.twin} and its cargo d stand in exactly one of:
PRE (undecided: neither twin stacked, the cargo parked on one twin),
ARM A (this twin stacked, the cargo on the other),
ARM B (the mirror). -/
inductive PairCfg (st : State) (x d : Card) : Prop
  | pre (h₀ : ¬ (x ∈ st.found x.suit))
      (h₁ : ¬ (x.twin ∈ st.found x.twin.suit))
      (h₂ : cargoTop st d x ∨ cargoTop st d x.twin) : PairCfg st x d
  | armA (h₀ : x ∈ st.found x.suit)
      (h₁ : cargoTop st d x.twin) : PairCfg st x d
  | armB (h₀ : x.twin ∈ st.found x.twin.suit)
      (h₁ : cargoTop st d x) : PairCfg st x d

/-! ## §2. The frozen dossier targets
(Frozen statements, sorries kept verbatim — the records relocated at
the 2026-10-17 archive; never retry as stated.) -/

/-- **The two faces agree**: a class has an arm-contingent card iff some
member shows the live fork-point signature. -/
theorem forkedCard_iff_forkPoint (C : SameOrbit) (u : State)
    (hu : u.WF) (hmem : classOf C u) :
    (∃ c, forkedCard C c) ↔ (∃ x, forkPoint u x) := by
  sorry

/-- **GIVEN the saturation fork point, its witnessed pair and cargo
characterize every member into the three cases** — the classification
is READ OFF from the known point, not posited over the class.  And the
cases are state-level decidable: given (x, d), each member's
configuration is a computable check of its founds and seatings. -/
theorem forkPoint_classifies (C : SameOrbit) (st₀ : State)
    (hwf : st₀.WF) (hmem₀ : classOf C st₀)
    (x d : Card) (hfp : forkPointC st₀ x d)
    (w : State) (hmem : classOf C w) :
    PairCfg w x d := by
  sorry

/-- **THE THREE-CASES THEOREM**: after the fork, ONE pair and ONE cargo
classify every member of the class — each member's fork geometry is
PRE, ARM A, or ARM B.  Stronger than the card-roster count: this pins
the geometry, and it is exactly why at most three cards are ever
contingent. -/
theorem fork_threeCases (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (haf : afterFork C) :
    ∃ x d : Card, ∀ st', classOf C st' → PairCfg st' x d := by
  sorry

/-- **The three-cards corollary**: the arm-contingent population is
exactly the twin pair {x, x.twin}, and the steering cargo is the one
card d — outside these three, every card is either surelyStackable or
stranded-inert.  (Cargo uniqueness: a second would-be cargo sits
stock/waste — it can never surface in-class; and if it were founded,
the fork would have dissolved.) -/
theorem fork_threeCards (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (haf : afterFork C) :
    ∃ x d : Card,
      (∀ c, forkedCard C c ↔ (c = x ∨ c = x.twin)) := by
  sorry

/-- **Fewness, tuple form**: after the fork, every Final member's rung
tuple is EITHER the shared profile OR its one-pair flip at the fork
pair — the orbit theorem's fork branch, consumed at the new notion:
only a few possible Finals. -/
theorem afterFork_fewFinals (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (haf : afterFork C)
    (w' : State) (hw' : classOf C w') (hf : Final w') :
    (∀ s : Suit, rungAt w' s = rungAt (canon u) s) ∨
    (∃ x : Card,
      rungAt w' x.suit = rungAt (canon u) x.twin.suit ∧
      rungAt w' x.twin.suit = rungAt (canon u) x.suit ∧
      ∀ s : Suit, s ≠ x.suit → s ≠ x.twin.suit →
        rungAt w' s = rungAt (canon u) s) := by
  sorry

/-- **Fewness, state form**: after the fork, every Final member sits
within ONE NECK of `canon u` — cone-reachable to a midpoint, then a
saturation completes.  The midpoints are bounded by the case table's
rank arithmetic (the classification closure's remaining work). -/
theorem afterFork_neckReachable (C : SameOrbit) (u : State) (hu : u.WF)
    (hmem : classOf C u) (w' : State) (hw' : classOf C w')
    (hf : Final w') :
    ∃ m, ConePath (canon u) m ∧ saturatesTo m w' := by
  sorry

/-! ## §3. The proved satellites and the private kit -/

/-- A face-up card's own suit rung sits weakly below its rank index —
the piled leg of the fork arithmetic (canon-v3's `v3PiledRung`
re-striped on the banked carrier: `WF.found_prefix`, the banked
`mem_upCards_take`, and the face-up census inversion
`mem_faceUp_only`; conservation forbids a card in two zones). -/
private theorem piled_rung {st : State} {q : Card} {k : Anchor}
    (hwf : st.WF) (hmem : q ∈ (st.piles k).faceUp) :
    rungAt st q.suit ≤ q.rank.toIdx := by
  obtain ⟨n, hn⟩ := hwf.found_prefix q.suit
  have hlen : rungAt st q.suit ≤ n := by
    show (st.found q.suit).length ≤ n
    rw [hn, List.length_take, Suit.upCards_length]
    omega
  rcases Nat.lt_trichotomy (rungAt st q.suit) q.rank.toIdx with hlt | heq | hgt
  · exact Nat.le_of_lt hlt
  · exact Nat.le_of_eq heq
  · exfalso
    have hqf : q ∈ st.found q.suit := by
      rw [hn, show q = Card.mk q.suit q.rank from rfl]
      exact mem_upCards_take q.suit n q.rank (by omega)
    exact (mem_faceUp_only hwf hmem).2.2.2.2 q.suit hqf

/-- The cargo's strict strand: at a fork point the cargo — topping the
covered twin's pile, never founded anywhere in the class — has its own
suit's rung STRICTLY below its rank.  Reductio: were the cargo
next-up, its license would fire (it tops the covering pile, and the
seat is refillable — the twin sits face-up below it, so the chop is
nonempty), the licensed raise is reversible at WF (the under-seat
witness constructor), the raised mate sits in-class with the cargo
founded (`class_leg` + `tabToFound_found_trio`), contradicting the
macro-grade ¬satStackable leg.  The weak half is `piled_rung`
(conservation); strictness is the negated nextUp. -/
private theorem forkPoint_cargo_strand {st : State} {x d : Card}
    (hwf : st.WF) (hfp : forkPointC st x d) :
    rungAt st d.suit < d.rank.toIdx := by
  obtain ⟨-, -, hcargo, -, hcol, hnsat, -⟩ := hfp
  obtain ⟨k, htopd, hholdt⟩ := hcargo
  have hdmem : d ∈ (st.piles k).faceUp := lastOf_mem (pileOfTop_top htopd).2
  have hxtm0 : x.twin ∈ (st.piles k).faceUp := pileHolding_mem hholdt
  have hsnoc : (st.piles k).faceUp = chop (st.piles k).faceUp ++ [d] :=
    lastOf_chop (pileOfTop_top htopd).2
  have hdne : d ≠ x.twin := by
    intro hcon
    exact hcol (by rw [hcon]; exact Or.inr rfl)
  rw [hsnoc] at hxtm0
  have hchop : chop (st.piles k).faceUp ≠ [] := by
    intro hnil
    rw [hnil] at hxtm0
    have hxt : x.twin = d := List.mem_singleton.1 (by simpa using hxtm0)
    exact absurd hxt.symm hdne
  by_cases hnu : st.nextUp d = true
  · exfalso
    obtain ⟨z', preT, hch⟩ := list_cons_of_ne_nil hchop
    have hrev := tabToFound_reversibleAtW_under_wf hwf hnu htopd hch
    obtain ⟨s₁, play, hstep, hrun⟩ := hrev
    have hclass := class_leg ⟨s₁, play, hstep, hrun⟩ hstep
    obtain ⟨-, ka, -, hs⟩ := step_tabToFound_inv hstep
    have hfound : d ∈ s₁.found d.suit := by
      have htrio := (tabToFound_found_trio (a := ka) hs).1
      rw [htrio]
      exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    exact hnsat ⟨s₁, (Quotient.sound hclass).symm, hfound⟩
  · have hle := piled_rung hwf hdmem
    have hne : st.foundHeight d.suit ≠ d.rank.toIdx := by
      intro hcon
      have hexp : st.nextUp d = true := by
        show decide (d.rank.toIdx = st.foundHeight d.suit) = true
        rw [show d.rank.toIdx = st.foundHeight d.suit from hcon.symm]
        exact decide_eq_true rfl
      exact absurd hexp hnu
    have hr : rungAt st d.suit = st.foundHeight d.suit := rfl
    omega

/-- A snoc-nodup membership bar: if appending `[d]` keeps the list
duplicate-free, `d` was not in the prefix. -/
private theorem nodup_snoc_notmem : ∀ (bs : List Card) (d : Card) (hnd : (bs ++ [d]).Nodup), d ∉ bs
  | [], _, _ =>
      by
        intro hcon
        simp at hcon
  | b :: t, d, hnd =>
      by
        intro hcon
        rcases List.mem_cons.mp hcon with hdb | hcon'
        · have hbmem : b ∈ t ++ [d] :=
              List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hdb.symm))
          exact absurd hbmem (List.nodup_cons.mp hnd).1
        · exact nodup_snoc_notmem t d (List.nodup_cons.mp hnd).2 hcon'

/-- Suit families are colors: a suit outside another's family carries
the OTHER color. -/
private theorem not_twinSuit_colors {s t : Suit}
    (h : ¬ twinSuit s t) : s.color ≠ t.color := by
  rcases s with _ | _ | _ | _ <;>
    rcases t with _ | _ | _ | _ <;>
    simp_all [twinSuit, Suit.twin, Suit.color]

/-- The operational trial, derived: the twin's swap-raise realizes

STAGED, NOT CLOSED (2026-10-17 truing: the earlier "CLOSED" claim here
was premature — the body below proves the FIRE and the SUCCESSOR-READ,
and the tail's sorry is exactly the successor's `CanRaise st' x.twin`
leg: the exposure read — the exposed twin as the new top — plus its
license, staged next pass).  The V3 base is the right shape either
way (the canon-v3 wake directive, amr_12aaf07c1):
the (Q, J) falsifier analysis found the V2 under-carried leg — the
exposed twin's SEAT (a bare-bottom non-king twin lifts nothing) —
and V3 carries it as the premise it always was: the cargo sits
DIRECTLY on the twin (the run discipline is rank-consecutive
upward, so the consecutivity the trial's own arithmetic proves is
now the witness shape) and the twin carries the seat package
(under-seat content or a bare king).  The proof is the mechanical
decomposition this file's engines always wanted: the fire
(pile-holding by membership uniqueness, place by rank and color),
the successor read (the moved run is exactly the singleton [d],
the source pile keeps [bs, x.twin] so the twin EXPOSES as the new
top), and the license (rungs never written by the cargo slide, the
twin pin is the premise, the seat bar is the premise).  -/
theorem forkPoint_trial {st : State} {x : Card} (hwf : st.WF) (h : forkPoint st x) :
    ∃ d st', st.step (.tabToTab d (Sum.inr x)) = some st' ∧
      CanRaise st' x.twin ∧ d.rank.toIdx + 1 = x.rank.toIdx := by
  obtain ⟨d, hCan, htwinpin, hcargo, hrank, hcol, hnsat, hseat⟩ := h
  obtain ⟨hn, a₀, hpj, hs₀⟩ := hCan
  obtain ⟨a, bs, htopd, hfaceup, hseatbar⟩ := hseat
  -- the pile pieces
  have hpa : (st.piles a).top = some d := (pileOfTop_top htopd).2
  have hmem : d ∈ (st.piles a).faceUp := by
    rw [hfaceup]
    exact List.mem_append.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  have hdnet : d ≠ x.twin := by
    intro hcon
    exact hcol (by rw [hcon]; exact Or.inr rfl)
  have hxnet : x.twin ≠ x := by
    intro hcon
    have hs : x.suit.twin = x.suit := congrArg Card.suit hcon
    exact Suit.twin_ne x.suit hs
  have hdne : d ≠ x := by
    intro hcon
    rw [hcon] at hrank
    omega
  -- the duplicate-free walk bar (the run discipline keeps the pile
  -- duplicate-free, and the cargo sits at its end)
  have hnd0 : ((bs ++ [x.twin]) ++ [d]).Nodup := by
    have h := runOK_nodup (hwf.2.1 a)
    rw [hfaceup,
      show bs ++ [x.twin, d] = (bs ++ [x.twin]) ++ [d] from
        (congrArg (bs ++ ·)
          (show [x.twin, d] = [x.twin] ++ [d] from rfl)).trans
        (List.append_assoc bs [x.twin] [d]).symm] at h
    exact h
  have hdnotmem : d ∉ bs ++ [x.twin] := by
    intro hcon
    rcases List.mem_append.mp hcon with hbs | hlast
    · exact nodup_snoc_notmem (bs ++ [x.twin]) d hnd0
        (List.mem_append.mpr (Or.inl hbs))
    · exact hdnet (List.mem_singleton.mp hlast)
  -- the walk: the source pile keeps [bs, x.twin]; the moved run is [d]
  have hpre : below d ((bs ++ [x.twin]) ++ [d]) = bs ++ [x.twin] :=
    below_append_stop hdnotmem
  have hfrom : fromCard d ((bs ++ [x.twin]) ++ [d]) = [d] :=
    fromCard_append_stop hdnotmem
  -- THE FIRE (the guards all pass)
  have hhold : st.pileHolding d = some a := (pileHolding_eq_some_iff hwf).2 hmem
  have hcol1 : d.suit ≠ x.suit := fun hcon => hcol (Or.inl hcon)
  have hcol2 : d.suit ≠ x.suit.twin := fun hcon => hcol (Or.inr hcon)
  have hcolne : d.suit.color ≠ x.suit.color := not_twinSuit_colors hcol
  have hplace : st.canPlace d (Sum.inr x) = true := by
    show (match st.pileOfTop x with
      | some _ => canSitOn d x
      | none => false) = true
    rw [hpj]
    exact (canSitOn_eq d x).2 ⟨hrank, hcolne⟩
  have hfire : ∃ s', State.step st (Move.tabToTab d (Sum.inr x)) = some s' := by
    have hne : fromCard d (st.piles a).faceUp ≠ [] := by
      rw [hfaceup,
        show bs ++ [x.twin, d] = (bs ++ [x.twin]) ++ [d] from
          (congrArg (bs ++ ·)
            (show [x.twin, d] = [x.twin] ++ [d] from rfl)).trans
          (List.append_assoc bs [x.twin] [d]).symm,
        hfrom]
      simp
    refine ⟨(st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below d (st.piles a).faceUp))).putRun
      (fromCard d (st.piles a).faceUp) (Sum.inr x), ?_⟩
    simp only [State.step, hhold, hplace]
    cases hList : fromCard d (st.piles a).faceUp with
    | nil => exact absurd hList hne
    | cons w r => rfl
  obtain ⟨s', hstep'⟩ := hfire
  refine ⟨d, s', hstep', ?_, hrank⟩
  -- THE SHAPE: read the successor through the inverse row
  obtain ⟨a₁, hh₁, hcp₁, hfr₁, hseq⟩ := step_tabToTab_inv hstep'
  rw [show a₁ = a from Option.some.inj (hhold.symm.trans hh₁).symm] at hseq
  sorry -- THE EXPOSURE AND LICENSE REMAIN, staged next pass

/-- The pin lemma: at the fork point, BOTH same-color rungs sit at the
pair rank — the bare twin's pin by `stackable_now_rungexact`, the
covered twin's pin by the cargo/cascade arithmetic.

CLOSED AT THE V2 BASE (the batch-F calibration): the covered twin's
pin enters as the signature's own premise, and the bare twin's pin
is the banked one-directional calibration row.  The earlier BLOCKED
note (the covered pin "unreachable from these hypotheses alone")
described the PRE-v2 signature — before the twin-rung premise
landed — and is retired. -/
theorem forkPoint_pins (st : State) (x : Card)
    (h : forkPoint st x) :
    rungAt st x.suit = x.rank.toIdx ∧ rungAt st x.twin.suit = x.rank.toIdx := by
  -- CLOSED at the v2 base (the batch-F calibration): the covered
  -- twin's pin enters as the signature's own premise; the bare
  -- twin's pin is the banked one-directional calibration row
  -- (the license's nextUp leg is rank-exact).  The earlier
  -- BLOCKED note (the covered pin "unreachable from these
  -- hypotheses alone") described the PRE-v2 signature and is
  -- retired by the premise's own landing.
  obtain ⟨d, hC⟩ := h
  obtain ⟨hCan, htwin, hcargo, hrank, hcol, hstrand, hseat⟩ := hC
  exact ⟨stackable_now_rungexact st x hCan, htwin⟩

/-- `twinSuit` is symmetric (same-color family membership). -/
private theorem twinSuit_symm {a b : Suit} (h : twinSuit a b) : twinSuit b a := by
  rcases h with h' | h'
  · exact Or.inl h'.symm
  · refine Or.inr ?_
    rw [h', Suit.twin_twin]

/-- Four suits, two color families: a suit outside `b`'s family and
outside... — precisely: if `a` shares no family with `b`, and `b`
shares no family with `c`, then `a` is IN `c`'s family. -/
private theorem suitfamily_antipodal {a b c : Suit}
    (hab : ¬ twinSuit a b) (hbc : ¬ twinSuit b c) : twinSuit a c := by
  rcases a with _ | _ | _ | _ <;>
    rcases b with _ | _ | _ | _ <;>
    rcases c with _ | _ | _ | _ <;>
    simp_all [twinSuit, Suit.twin]

/-- The cross-pinch arithmetic of the sandwich: a cargo `d` inside
`w`'s color family (same family as the OTHER fork's pair), one rank
below `z`'s pair rank, stranded strictly below its own rank, against
`w`'s pins at its own pair rank: Rw + 2 ≤ Rz. -/
private theorem cross_pin {st : State} {d z w : Card}
    (hfam : twinSuit d.suit w.suit) (hrank : d.rank.toIdx + 1 = z.rank.toIdx)
    (hp1 : rungAt st w.suit = w.rank.toIdx)
    (hp2 : rungAt st w.twin.suit = w.rank.toIdx)
    (hstrand : rungAt st d.suit < d.rank.toIdx) :
    w.rank.toIdx + 2 ≤ z.rank.toIdx := by
  rcases hfam with h | h
  · rw [h] at hstrand
    have hA : rungAt st w.suit = w.rank.toIdx := hp1
    omega
  · rw [h] at hstrand
    have hA : rungAt st (w.suit.twin) = w.rank.toIdx := hp2
    omega

/-- **The exclusivity sandwich** (the user's rank-arithmetic proof):
CLOSED at the canon-v3 wake (amr_12a492e2) — the v2 base made the
covered pins PREMISES (retiring the original BLOCKED note, which
described the pre-v2 signature) and the cargo strands are in-file
engines, so the sandwich consumes exactly: the pins of both forks
(each pair's suits at its pair rank — the bare pin by the banked
one-directional calibration, the covered pin by the premise), the
strands of both cargos (strictly below their own ranks,
`forkPoint_cargo_strand`), the color-family placement (each cargo,
opposite-colored to its OWN pair by the ¬twinSuit leg, is
same-colored as the OTHER fork's pair — four suits, two families),
and `omega`.  The cross-pinch: Ry + 2 ≤ Rx ∧ Rx + 2 ≤ Ry. -/
theorem forkPoint_exclusive (st : State) (x y : Card) (hwf : st.WF)
    (hcol : ¬ twinSuit x.suit y.suit)
    (hx : forkPoint st x) (hy : forkPoint st y) : False := by
  -- CLOSED (the canon-v3 wake, amr_12a492e2): the v2 base makes
  -- the covered pins premises and the strands in-file engines —
  -- the user's rank sandwich consumes exactly those.  Each
  -- fork's cargo is opposite-colored to its OWN pair (the
  -- ¬twinSuit leg), hence same-colored as the OTHER fork's pair
  -- (four suits, two color families); so the x-fork's cargo
  -- sits inside y's pair suits, where y's pins hold the rung AT
  -- the pair rank, while the x-strand demands it strictly BELOW
  -- x's pair rank — and symmetrically.  The two strict
  -- inequalities cross-pinch: Ry + 2 ≤ Rx ∧ Rx + 2 ≤ Ry.
  obtain ⟨dx, hCanx, htpinx, hcargox, hrankx, hcolx, hstrandx, hseatx⟩ := hx
  obtain ⟨dy, hCany, htpiny, hcargoy, hranky, hcoly, hstrandy, hseaty⟩ := hy
  have hCx : forkPointC st x dx :=
    ⟨hCanx, htpinx, hcargox, hrankx, hcolx, hstrandx, hseatx⟩
  have hCy : forkPointC st y dy :=
    ⟨hCany, htpiny, hcargoy, hranky, hcoly, hstrandy, hseaty⟩
  have hsx := forkPoint_cargo_strand hwf hCx
  have hsy := forkPoint_cargo_strand hwf hCy
  have hpx := stackable_now_rungexact st x hCanx
  have hpy := stackable_now_rungexact st y hCany
  have hfamx : twinSuit dx.suit y.suit := suitfamily_antipodal hcolx hcol
  have hfamy : twinSuit dy.suit x.suit :=
    suitfamily_antipodal hcoly (fun h => hcol (twinSuit_symm h))
  have kx := cross_pin hfamx hrankx hpy htpiny hsx
  have ky := cross_pin hfamy hranky hpx htpinx hsy
  omega

/-! ## The archive battery
(Fresh proved heads re-audited at the relocation; the frozen rows
keep their sorryAx surfaces.) -/

#print axioms piled_rung
#print axioms forkPoint_cargo_strand
#print axioms forkPoint_pins
#print axioms forkPoint_exclusive
