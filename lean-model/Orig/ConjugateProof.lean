import Orig.ForkStateUniq

/-!
# Orig.ConjugateProof — the corrected conjugation theorems

The conjugation card at the CORRECTED composite (macro-game 07247ec:
`conjugateForkState` moves `x.twin`'s whole segment, not the old
composite's cargo `d` — 172ca30's definitional fix), proved at the
probe-validated anatomy (`probes/ConjugateProbe.lean`, committed
first per the probe-first discipline).  What the boards settled:

* **The endpoint's witness is the SAME `x`** (probe A): the banked
  §4 rows (`conjugate_endpoint_relic/_witness` in ForkStateUniq,
  stated at the LOOSE raise–slide–pull shape and therefore covering
  the corrected composite verbatim with `d := x.twin`) are not
  old-composite residue — they hold, and they force any forkState at
  the endpoint to witness the composite's own raised card.  The
  twins trade physical POSITIONS; the raise license stays with `x`.
* **The seat package is load-bearing** (probe B): at the (Q,J)
  corner — `x.twin` a BARE-BOTTOM NON-KING pile top, the V3 falsifier
  shape — the composite still FIRES (the pulled-back `x` lands on the
  exposed second `(x+1)` card, the rank packing forbidding any other
  landing), and the endpoint carries BOTH twins as raisers: NOT a
  forkState.  The conjugation theorem therefore carries the twin's
  seat package as a premise — exactly the in-tree docstring's
  "implied by the forkState iff on x side, checked on x.twin side".
* **The raw `fires ⟺ seats` necessity is refuted** (probe C): a
  covered-but-unseated twin (bottom of its face-up run, empty
  hidden, non-king) can fire the composite with a DISPLACED second
  base and still land a perfectly good forkState endpoint.  The
  existence biconditional is therefore proved at the honest grades:
  the seat-swap OUTCOME implies the seat package, with the (Q,J)
  corner recorded as the theorem-grade failure shape.

The rows, in dependency order:

* §1 — the corrected-def instances of the §4 anatomy rows (net-flat,
  re-license, witness-pin), thin cites of the banked loose-shape
  theorems.
* §2 — the seat parcels: `TwinSeat` (the V3 form), the twin-pile
  separation (twins share rank, so a legal run cannot hold both), the
  exposed-twin impossibility at a forkState, and the seat-forced
  pile shapes.
* §3 — the packing pins: kings fit nothing, the `(x+1)` cards of the
  opposite color are exactly two, and every fitting base is one of
  them — the arithmetic that forces the composite's second and third
  bases onto the docstring seats.
* §4 — **THE MAIN ROW `conjugate_forkState`**: a forkState at `st`
  (witness `x`), the twin located with its seat package, and ANY
  firing of the corrected composite land a forkState at `w`, witness
  THE SAME `x`.
* §5 — **THE CONSTRUCTION `conjugate_swap_fires`**: the seat
  packages fire the canonical swap composite explicitly (the
  docstring bases `z₀ = Sum.inr (the (x+1) under x)`, `z₁ = Sum.inr
  (the (x+1) under x.twin)`, or the empty-anchor letters at rank 12),
  the existence direction of the user's iff, with the swap outcome
  recorded in the witnesses.
* §6 — **THE SEAT-SWAP NECESSITY and the (Q,J) corner**: the swap
  outcome implies the twin's seat package, closing the iff at the
  honest grade; and when the seat package fails at an exposed twin,
  NO firing lands a forkState (two raisers — probe B as a theorem).
* §7 — **THE TOTAL FUNCTION `conjugateForkStateS`**: the computable
  search (witness over `Card.universe` via `canRaiseB`, the two
  bases over `Anchor.all`/`Card.universe`, the endpoint gated by the
  decidably-checked `forkState`), identity on fail; correctness BOTH
  ways — the function returns `st` exactly when no firing lands a
  verified forkState endpoint.  NO Classical, NO noncomputable.

The in-tree interface is consumed by real names (`forkState`,
`conjugateForkState` from `Orig.MacroInternal`; the §4 anatomy rows
from `Orig.ForkStateUniq`); the private micro-kit re-lands the
house's standard copies (`below_join`, `nodup_snoc_notmem`, the
`chop`/`lastOf` list trivia), each dedup-marked against its home.
-/

/-! ## §0. The private engine kit
(the house's standard micro-copies: Classify's private list kit,
ForkStateUniq's private row copies, plus the small list trivia this
card's transports ride). -/

/-- The below-part and the run from `c` reassemble the list (the copy
of `Orig/Classify.lean`'s private `below_join`). -/
private theorem below_join {c : Card} : ∀ (l : List Card),
    below c l ++ fromCard c l = l := by
  intro l
  induction l with
  | nil => rfl
  | cons y t ih =>
      rw [below_cons, fromCard]
      by_cases hyc : y = c
      · rw [if_pos hyc, if_pos hyc]
        rfl
      · rw [if_neg hyc, if_neg hyc]
        exact congrArg (y :: ·) ih

/-- Every element of `below c` is an element (the copy of
`Orig/Classify.lean`'s private `below_mem`). -/
private theorem below_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ below c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [below_cons] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h; cases h
      · rw [if_neg hyc] at h
        rcases List.mem_cons.1 h with rfl | hm
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr (ih hm))

/-- Every element of `fromCard c` is an element (the copy of
`Orig/Classify.lean`'s private `fromCard_mem`). -/
private theorem fromCard_mem {c : Card} : ∀ {l : List Card} {x : Card},
    x ∈ fromCard c l → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons y t ih =>
      intro x h
      rw [fromCard] at h
      by_cases hyc : y = c
      · rw [if_pos hyc] at h
        rcases List.mem_cons.1 h with rfl | hm
        · exact List.mem_cons.2 (Or.inl rfl)
        · exact List.mem_cons.2 (Or.inr hm)
      · rw [if_neg hyc] at h
        exact List.mem_cons.2 (Or.inr (ih h))

/-- The below-part of `c` never contains `c` (the cut stops at the
first occurrence; the run discipline keeps the list free of
seconds). -/
private theorem below_not_self {c : Card} : ∀ (l : List Card), c ∉ below c l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons y t ih =>
      rw [below_cons]
      by_cases hyc : y = c
      · rw [if_pos hyc]
        intro h
        exact absurd h (by simp)
      · rw [if_neg hyc]
        intro h
        rcases List.mem_cons.1 h with heq | hrest
        · exact hyc heq.symm
        · exact ih hrest

/-- A member of the below-part is not the cut card itself. -/
private theorem mem_below_ne {c x : Card} {l : List Card}
    (h : x ∈ below c l) : x ≠ c := by
  intro hcon
  rw [hcon] at h
  exact below_not_self l h

/-- A snoc-nodup membership bar: if appending `[d]` keeps the list
duplicate-free, `d` was not in the prefix (the copy of
`Orig/MacroInternal.lean`'s private row). -/
private theorem nodup_snoc_notmem :
    ∀ (bs : List Card) (d : Card) (_hnd : (bs ++ [d]).Nodup), d ∉ bs
  | [], _, _ => by intro hcon; simp at hcon
  | b :: t, d, hnd => by
      intro hcon
      rcases List.mem_cons.mp hcon with hdb | hcon'
      · have hbmem : b ∈ t ++ [d] :=
            List.mem_append.mpr (Or.inr (List.mem_singleton.mpr hdb.symm))
        exact absurd hbmem (List.nodup_cons.mp hnd).1
      · exact nodup_snoc_notmem t d (List.nodup_cons.mp hnd).2 hcon'

/-- A twin is never its own card (the copy of ForkStateUniq's private
row). -/
private theorem card_twin_ne (c : Card) : c.twin ≠ c := by
  intro hcon
  exact Suit.twin_ne c.suit (congrArg Card.suit hcon)

/-- The bare vacate's computational meaning: an empty prefix split
and an empty hidden deck leave the bare empty pile (the copy of
ForkStateUniq's private row). -/
private theorem afterRunRemoved_bareEmpty {p : Pile} (h : p.hidden = []) :
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], ([] : List Card)⟩ := by
  rcases p with ⟨hlist, flist⟩
  cases hlist with
  | nil => rfl
  | cons x xs => exact absurd h (by simp)

/-- The nodup append bar: a member of the first part never occurs in
the second part. -/
private theorem nodup_append_notmem {l₁ l₂ : List Card} {d : Card}
    (hnd : (l₁ ++ l₂).Nodup) (hmem : d ∈ l₁) : d ∉ l₂ := by
  obtain ⟨_, _, hdisj⟩ := List.nodup_append.mp hnd
  exact fun hcon => absurd rfl (hdisj d hmem d hcon)

/-- The last of an append is the second list's last, when the second
list is nonempty (the house trivia, re-landed here for the
transport's pile-top reads). -/
private theorem lastOf_append {l₁ : List Card} :
    ∀ (l₂ : List Card), l₂ ≠ [] → ∀ (c : Card),
      lastOf (l₁ ++ l₂) = some c → lastOf l₂ = some c := by
  induction l₁ with
  | nil => intro l₂ _ c h; exact h
  | cons x t ih =>
      intro l₂ hne c h
      obtain ⟨z, zs, rfl⟩ := list_cons_of_ne_nil hne
      have hLne : (t ++ z :: zs) ≠ [] := by simp
      obtain ⟨u, us, hcu⟩ := list_cons_of_ne_nil hLne
      have h6 : lastOf (x :: u :: us) = some c := by
        rw [show (x :: t) ++ z :: zs = x :: (t ++ z :: zs) from rfl, hcu] at h
        exact h
      have h7 : lastOf (u :: us) = some c := h6
      rw [← hcu] at h7
      exact ih (z :: zs) (by simp) c h7

/-- The last-element lemma in equation form (the start-of-the-append
variant): the append's last IS the second list's last. -/
private theorem lastOf_cons_cons (u v : Card) (t : List Card) :
    lastOf (u :: v :: t) = lastOf (v :: t) := rfl

private theorem lastOf_append_eq (l₁ : List Card) : ∀ (l₂ : List Card),
    l₂ ≠ [] → lastOf (l₁ ++ l₂) = lastOf l₂ := by
  induction l₁ with
  | nil => intro l₂ _; rfl
  | cons u t ih =>
      intro l₂ hne
      cases t with
      | nil =>
          rcases l₂ with _ | ⟨z, zs⟩
          · exact absurd rfl hne
          · exact lastOf_cons_cons u z zs
      | cons v vs =>
          exact (lastOf_cons_cons u v (vs ++ l₂)).trans (ih l₂ hne)

/-- The chop is empty exactly below length two (the seat-versus-flip
boundary the parcels read). -/
private theorem chop_eq_nil_iff : ∀ (l : List Card), chop l = [] ↔ l.length ≤ 1
  | [] => by
      constructor
      · intro _; simp
      · intro _; rfl
  | [x] => by
      constructor
      · intro _; simp
      · intro _; rfl
  | x :: y :: t => by
      have hcl : chop (x :: y :: t) = x :: chop (y :: t) := rfl
      constructor
      · intro h
        rw [hcl] at h
        exact absurd h (by simp)
      · intro h
        have hlen : (x :: y :: t).length = 2 + t.length := by
          rw [List.length_cons, List.length_cons]
          omega
        rw [hlen] at h
        omega

/-- A two-or-longer list's chop is nonempty. -/
private theorem chop_ne_nil_of_len {l : List Card} (h : 2 ≤ l.length) :
    chop l ≠ [] := by
  intro hcon
  have h2 := (chop_eq_nil_iff l).1 hcon
  omega

/-! ## §1. The corrected composite's anatomy, through the banked loose rows

The §4 rows of `Orig.ForkStateUniq` are stated at the LOOSE
raise–slide–pull shape (`∃ d ba bb st₁ st₂, …`), so they apply to the
corrected composite verbatim by instantiating the moved card at
`d := x.twin`.  These thin instances pin the corrected def to them,
and record the probe A verdict in theorem form: the endpoint's
witness, if any, is the composite's own raised card. -/

/-- The corrected composite is net-flat: every foundation returns
card for card (the §4 loose row, instanced at `d := x.twin`). -/
theorem conjugate_netflat {st w : State} (hconj : conjugateForkState st w) :
    ∀ σ, w.found σ = st.found σ := by
  obtain ⟨x, ba, bb, st₁, st₂, -, h₁, h₂, h₃⟩ := hconj
  exact conjugate_endpoint_netflat ⟨x.twin, ba, bb, st₁, st₂, h₁, h₂, h₃⟩

/-- The corrected composite's endpoint re-licenses its own raised
card (the §4 loose row, instanced at `d := x.twin`): `x` lands as a
live seat top with its rung pin restored by the net-flat composite. -/
theorem conjugate_relic {st w : State} {x : Card}
    (hwf : st.WF)
    (hsteps : ∃ ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab x.twin ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w) :
    CanRaise w x ∧ rungAt w x.suit = x.rank.toIdx := by
  obtain ⟨ba, bb, st₁, st₂, h₁, h₂, h₃⟩ := hsteps
  exact conjugate_endpoint_relic hwf ⟨x.twin, ba, bb, st₁, st₂, h₁, h₂, h₃⟩

/-- **THE WITNESS PIN** — the corrected composite's endpoint, if it
carries a forkState at all, witnesses the composite's own raised
card: the twins trade physical positions in the swap, but the raise
license stays with `x`; the mate face never comes from the composite
(it stays one cargo leg away, the §3 slide).  (The probe A verdict in
theorem form; the banked loose row instanced at `d := x.twin`.) -/
theorem conjugate_witness {st w : State} {x y : Card}
    (hwf : st.WF)
    (hsteps : ∃ ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab x.twin ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w)
    (hyiff : ∀ c, CanRaise w c ↔ c = y) : y = x := by
  obtain ⟨ba, bb, st₁, st₂, h₁, h₂, h₃⟩ := hsteps
  exact conjugate_endpoint_witness hwf ⟨x.twin, ba, bb, st₁, st₂, h₁, h₂, h₃⟩ hyiff

/-! ## §2. The seat parcels -/

/-- **The twin's seat package** (the V3 form): the twin sits on
face-up under-seat content, or it is a bottom king on no hidden deck
(the vacate channel).  This is the seat gate the in-tree docstring
records: implied by the forkState iff on `x`'s side, carried as a
premise on the twin's side. -/
def TwinSeat (st : State) (x : Card) (q : Anchor) : Prop :=
  below x.twin (st.piles q).faceUp ≠ [] ∨
    ((st.piles q).hidden = [] ∧ x.twin.rank = Rank.king)

/-- A card that is not in the front of a snoc list keeps its below-part
intact (the nodup-free premise version; the parcels supply the
uniqueness). -/
private theorem below_snoc_notmem : ∀ (front : List Card) (c : Card), c ∉ front →
    below c (front ++ [c]) = front
  | [], _, _ => by rw [List.nil_append, below_cons, if_pos rfl]
  | u :: t, c, hc => by
      rw [List.cons_append, below_cons]
      have hut : u ≠ c := fun hcon => hc (List.mem_cons.mpr (Or.inl hcon.symm))
      rw [if_neg hut]
      exact congrArg (u :: ·)
        (below_snoc_notmem t c fun hmem => hc (List.mem_cons.mpr (Or.inr hmem)))

/-- At the list's own last element, the below-part is the chop
(given uniqueness — the last occurrence is the only one). -/
private theorem below_self_last {l : List Card} {c : Card}
    (hc : c ∉ chop l) (htop : lastOf l = some c) : below c l = chop l := by
  obtain ⟨front, hfe⟩ := lastOf_eq_snoc htop
  have hc' : c ∉ front := by
    intro hcon
    exact hc (by rw [hfe, chop_snoc]; exact hcon)
  rw [hfe, below_snoc_notmem front c hc', chop_snoc]

/-- Twins never share a pile with one above the other: they share
rank, and a legal run descends strictly, so the twin cannot sit below
the pile's own top card `x`. -/
theorem twin_pile_ne {st : State} {p : Anchor} {x : Card}
    (hwf : st.WF) (htop : (st.piles p).top = some x)
    (hmem : x.twin ∈ (st.piles p).faceUp) : False := by
  obtain ⟨front, hfe⟩ := Pile.top_eq_lastOf_iff.mp htop
  have hok : runOK (front ++ [x]) = true := by rw [← hfe]; exact hwf.runOK_of p
  rw [hfe] at hmem
  rcases List.mem_append.mp hmem with hfront | hlast
  · have hdesc := runOK_desc hok hfront (List.mem_singleton.mpr rfl)
    rw [Card.twin_rank] at hdesc
    omega
  · exact card_twin_ne x (List.mem_singleton.mp hlast)

/-- **The exposed-twin impossibility**: at a forkState (the pair rungs
pinned, the iff naming `x` alone), a located twin with its seat
package is NEVER a pile top — a top with the seat package would raise
at `st`, contradicting the iff.  The twin is covered; the (Q,J)
corner (bare-bottom non-king) is exactly the twin that DROPS the
seat package. -/
theorem twin_not_top {st : State} {x : Card} {q : Anchor}
    (hwf : st.WF)
    (h₂ : rungAt st x.twin.suit = x.rank.toIdx)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hloc : st.pileHolding x.twin = some q)
    (hseat : TwinSeat st x q) :
    (st.piles q).top ≠ some x.twin := by
  have hmem : x.twin ∈ (st.piles q).faceUp := pileHolding_mem hloc
  intro htop
  -- the pile shape: the twin is the last face-up card
  have hchop : chop (st.piles q).faceUp = below x.twin (st.piles q).faceUp := by
    have hnodupq : (chop (st.piles q).faceUp ++ [x.twin]).Nodup := by
      rw [← lastOf_chop (show lastOf (st.piles q).faceUp = some x.twin from htop)]
      exact runOK_nodup (hwf.runOK_of q)
    exact (below_self_last (nodup_snoc_notmem _ _ hnodupq)
      (show lastOf (st.piles q).faceUp = some x.twin from htop)).symm
  -- the license at the twin, all four clauses live
  have hnext : st.nextUp x.twin = true := by
    show decide (x.twin.rank.toIdx = (st.found x.twin.suit).length) = true
    rw [Card.twin_rank, ← h₂]
    exact decide_eq_true rfl
  have hseatCR : chop (st.piles q).faceUp ≠ [] ∨
      ((st.piles q).hidden = [] ∧ x.twin.rank = Rank.king) := by
    rcases hseat with hbs | ⟨hhid, hking⟩
    · rw [hchop]
      exact Or.inl hbs
    · exact Or.inr ⟨hhid, hking⟩
  exact card_twin_ne x
    ((hiff x.twin).1 ⟨hnext, q, (pileOfTop_eq_some_iff hwf).2 htop, hseatCR⟩)

/-- A seated top carries its fitting under-card: the direct
`(x+1)` beneath `x` (the base the canonical swap slides the twin's
run onto). -/
theorem seated_top_under {st : State} {p : Anchor} {x : Card}
    (hwf : st.WF) (htop : (st.piles p).top = some x)
    (hchop : chop (st.piles p).faceUp ≠ []) :
    ∃ z₀, lastOf (chop (st.piles p).faceUp) = some z₀ ∧ canSitOn x z₀ = true := by
  have hfull : (st.piles p).faceUp = chop (st.piles p).faceUp ++ [x] :=
    lastOf_chop (show lastOf (st.piles p).faceUp = some x from htop)
  have hrun : runOK (chop (st.piles p).faceUp ++ [x]) = true := by
    rw [← hfull]
    exact hwf.runOK_of p
  obtain ⟨z, hz, hsit⟩ := runOK_snoc_sit hchop hrun
  exact ⟨z, hz, hsit⟩

/-- The covered card's direct under-card within one legal pile fits it
(the base the pulled-back `x` lands on: the last of the prefix
before the run head). -/
theorem runOK_join_head_sit : ∀ (P S : List Card) (u v : Card),
    runOK (P ++ v :: S) = true → lastOf P = some u → canSitOn v u = true := by
  intro P
  induction P with
  | nil => intro _ _ _ _ hlast; exact absurd hlast (by simp [lastOf])
  | cons w P' ih =>
      intro S u v hok hlast
      cases P' with
      | nil =>
          have hok' : runOK (w :: v :: S) = true := hok
          have hwu : w = u := by
            have hlast' : some w = some u := hlast
            injection hlast'
          have hp : runOK (w :: v :: S) = (canSitOn v w && runOK (v :: S)) := rfl
          rw [hp, Bool.and_eq_true] at hok'
          rw [← hwu]
          exact hok'.1
      | cons w' P'' =>
          have hlast' : lastOf (w' :: P'') = some u := hlast
          exact ih S u v (runOK_cons_tail hok) hlast'

/-! ## §3. The packing pins -/

/-- Kings fit nothing: no card sits thirteen. -/
theorem no_fit_king {c z : Card} (h : canSitOn c z = true) :
    c.rank ≠ Rank.king := by
  obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp h
  intro hcon
  rw [hcon] at hrank
  have hK : Rank.king.toIdx = 12 := rfl
  have h13 := Rank.toIdx_lt z.rank
  omega

/-- Four suits, two color families: a suit outside the color of `s`
and outside the distinct pair `a`, `b` (both of `s`'s other color)
IS one of the pair. -/
private theorem two_suits_pigeon {s a b c : Suit}
    (ha : s.color ≠ a.color) (hb : s.color ≠ b.color) (hab : a ≠ b)
    (hc : s.color ≠ c.color) : c = a ∨ c = b := by
  cases s <;> cases a <;> cases b <;> cases c <;> simp_all [Suit.color]

/-- **THE PACKING PIN**: the two `(x+1)` cards of `x`'s opposite
color, once witnessed distinct, exhaust every fitting base — the
arithmetic that forces the composite's second and third bases onto
the docstring seats (there is no third pile the pulled-back card
could land on; the exposed under-base is the only option). -/
theorem conjugate_fit_pin {x z₀ z₁ z : Card}
    (hfit₀ : canSitOn x z₀ = true) (hfit₁ : canSitOn x.twin z₁ = true)
    (hne : z₀ ≠ z₁) (hfit : canSitOn x z = true) :
    z = z₀ ∨ z = z₁ := by
  obtain ⟨hr₀, hc₀⟩ := (canSitOn_eq x z₀).mp hfit₀
  obtain ⟨hr₁, hc₁⟩ := (canSitOn_eq x.twin z₁).mp hfit₁
  obtain ⟨hr, hc⟩ := (canSitOn_eq x z).mp hfit
  rw [show x.twin.rank.toIdx = x.rank.toIdx from rfl] at hr₁
  rw [show x.twin.suit.color = x.suit.color from Suit.color_twin x.suit] at hc₁
  have hsne : z₀.suit ≠ z₁.suit := by
    intro hcon
    have hrank : z₀.rank.toIdx = z₁.rank.toIdx := by omega
    have hr : z₀.rank = z₁.rank := Rank.toIdx_inj hrank
    apply hne
    obtain ⟨z₀s, z₀r⟩ := z₀
    obtain ⟨z₁s, z₁r⟩ := z₁
    have hz' : z₀s = z₁s := hcon
    have hr' : z₀r = z₁r := hr
    rw [hz', hr']
  have hzs : z.suit = z₀.suit ∨ z.suit = z₁.suit :=
    two_suits_pigeon (s := x.suit) (a := z₀.suit) (b := z₁.suit) (c := z.suit)
      hc₀ hc₁ hsne hc
  rcases hzs with hz | hz
  · refine Or.inl ?_
    have hrank : z.rank.toIdx = z₀.rank.toIdx := by omega
    obtain ⟨zs, zr⟩ := z
    obtain ⟨z₀s, z₀r⟩ := z₀
    have hz' : zs = z₀s := hz
    have hrr : zr = z₀r := Rank.toIdx_inj (show zr.toIdx = z₀r.toIdx from hrank)
    rw [hz', hrr]
  · refine Or.inr ?_
    have hrank : z.rank.toIdx = z₁.rank.toIdx := by omega
    obtain ⟨zs, zr⟩ := z
    obtain ⟨z₁s, z₁r⟩ := z₁
    have hz' : zs = z₁s := hz
    have hrr : zr = z₁r := Rank.toIdx_inj (show zr.toIdx = z₁r.toIdx from hrank)
    rw [hz', hrr]

/-! ## §4. THE MAIN ROW — the composite produces a forkState

With the witness clauses at `st` (the raise licensed to `x` alone),
the twin LOCATED with its seat package, and ANY firing of the
corrected composite, the endpoint `w` is a forkState — witnessed by
THE SAME `x` (§1's witness pin says it could be no other card): the
composite is net-flat, every other card's license transports
verbatim, and the seat packages keep the departures reveal-free.

The proof reads the firing's own step records (`step_tabToFound_inv`,
`step_tabToTab_inv`, `step_foundToTab_inv` — the public Play.lean
inverse rows), and forces the two loose bases onto the docstring
seats through the packing pin: `ba` is the exposed `(x+1)` under
`x` (or, at rank 12, an empty anchor — kings fit nothing), `bb` is
the exposed `(x+1)` under the twin (or the king's empty anchor). -/

/-- **THE CORRECTED CONJUGATION THEOREM** — the physical-swap
composite produces a forkState.  The premises are exactly the
honest ones: the forkState clauses at `st` with witness `x` (all
three), the twin FACE UP in pile `q` with the seat package
(`TwinSeat`, the V3 form), and a firing of the corrected
`conjugateForkState` composite.  The endpoint `w` witnesses the SAME
`x` — the twins traded physical positions (each taking the other's
under-seat base), the raise license stayed home, and the mid-flight
foundations returned card for card.

(Named `…_corrected` against the in-tree gated row
`MacroInternal.conjugate_forkState`, which keeps the SEAT-LESS shape
and stays `sorry`-gated: the (Q,J) corner (§6's
`conjugate_corner_notForkState`, probe B) shows the seat-less shape
is FALSE — the seat package is the premise the honest theorem must
carry, exactly the in-tree docstring's "checked on x.twin side".) -/
theorem conjugate_forkState_corrected {st w : State} {x : Card} {q : Anchor}
    (hwf : st.WF)
    (h₁ : rungAt st x.suit = x.rank.toIdx)
    (h₂ : rungAt st x.twin.suit = x.rank.toIdx)
    (hiff : ∀ c, CanRaise st c ↔ c = x)
    (hloc : st.pileHolding x.twin = some q)
    (hseat : TwinSeat st x q)
    (hsteps : ∃ ba bb st₁ st₂,
      st.step (Move.tabToFound x) = some st₁ ∧
      st₁.step (Move.tabToTab x.twin ba) = some st₂ ∧
      st₂.step (Move.foundToTab x bb) = some w) :
    forkState w := by
  obtain ⟨ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩ := hsteps
  -- STEP 1's record and the pile of x
  obtain ⟨hnextx, p, hpox, hs₁⟩ := step_tabToFound_inv h₁step
  -- x's own seat off the iff, read through the same pile
  have hseatx : chop (st.piles p).faceUp ≠ [] ∨
      ((st.piles p).hidden = [] ∧ x.rank = Rank.king) := by
    obtain ⟨-, a, hpoa, hs⟩ := (hiff x).2 rfl
    rw [pileOfTop_inj hpoa hpox] at hs
    exact hs
  have htopp : (st.piles p).top = some x := (pileOfTop_eq_some_iff hwf).mp hpox
  -- WF travels all three legs
  have hwf₁ : st₁.WF := step_wf hwf h₁step
  have hwf₂ : st₂.WF := step_wf hwf₁ h₂step
  have hwfw : w.WF := step_wf hwf₂ h₃step
  -- the st₁ pile reads: p rewritten, everything else verbatim
  have hst₁p : st₁.piles p =
      Pile.afterRunRemoved (st.piles p) (chop (st.piles p).faceUp) := by
    rw [hs₁]
    show (if p = p then _ else _) = _
    rw [if_pos rfl]
  have hst₁ne : ∀ a', a' ≠ p → st₁.piles a' = st.piles a' := by
    intro a' hne'
    rw [hs₁]
    show (if a' = p then _ else _) = _
    rw [if_neg hne']
  -- the net-flat found ride (cited at the full composite)
  have hflat : ∀ σ, w.found σ = st.found σ :=
    conjugate_netflat ⟨x, ba, bb, st₁, st₂, ⟨x, h₁, h₂, hiff⟩, h₁step, h₂step, h₃step⟩
  -- the relic: x re-licenses at w with its pin
  obtain ⟨hCRwx, hpinwx⟩ :=
    conjugate_relic hwf ⟨ba, bb, st₁, st₂, h₁step, h₂step, h₃step⟩
  by_cases hking : x.rank = Rank.king
  · -- THE KING CHANNEL (x.rank = king)
    -- x's own seat: the chop disjunct is out (kings fit nothing) ⇒ bare king
    have hc₀nil : chop (st.piles p).faceUp = [] := by
      by_cases hc₀ : chop (st.piles p).faceUp = []
      · exact hc₀
      · exfalso
        obtain ⟨z₀, hz₀last, hfitz₀⟩ := seated_top_under hwf htopp hc₀
        exact (no_fit_king hfitz₀) hking
    have hhidp : (st.piles p).hidden = [] := by
      rcases hseatx with hch | ⟨hh, hkk⟩
      · exfalso
        rw [hc₀nil] at hch
        exact hch rfl
      · exact hh
    -- the pile parcels, as in the non-king channel
    have htqmem : x.twin ∈ (st.piles q).faceUp := pileHolding_mem hloc
    obtain ⟨covrest, hseg⟩ := fromCard_eq_head_of_mem htqmem
    have hjoin : below x.twin (st.piles q).faceUp ++ (x.twin :: covrest)
        = (st.piles q).faceUp := by
      rw [← hseg]
      exact below_join (st.piles q).faceUp
    have hsegne : x.twin :: covrest ≠ [] := List.cons_ne_nil x.twin covrest
    have hpq : p ≠ q := by
      intro hcon
      have htqmem' : x.twin ∈ (st.piles p).faceUp := by rw [hcon]; exact htqmem
      exact twin_pile_ne hwf htopp htqmem'
    have hkingt : x.twin.rank = Rank.king := by rw [Card.twin_rank]; exact hking
    -- the twin is also king, so its seat is the bare vacate shape
    have hbsnil : below x.twin (st.piles q).faceUp = [] := by
      by_cases hbs : below x.twin (st.piles q).faceUp = []
      · exact hbs
      · exfalso
        obtain ⟨z₁, hz₁last⟩ := lastOf_exists hbs
        have hfit₁ : canSitOn x.twin z₁ = true :=
          runOK_join_head_sit _ covrest z₁ x.twin
            (by rw [hjoin]; exact hwf.runOK_of q) hz₁last
        exact (no_fit_king hfit₁) hkingt
    have hhidq : (st.piles q).hidden = [] ∧ x.twin.rank = Rank.king := by
      rcases hseat with hbs | ⟨hh, hkk⟩
      · exfalso
        rw [hbsnil] at hbs
        exact hbs rfl
      · exact ⟨hh, hkk⟩
    -- the twin is covered; the whole face-up of q is the run
    have hcovne : covrest ≠ [] := by
      intro hcovnil
      have htopqq : (st.piles q).top = some x.twin := by
        show lastOf (st.piles q).faceUp = some x.twin
        rw [hbsnil] at hjoin
        rw [hcovnil] at hjoin
        rw [← hjoin]
        exact lastOf_snoc
      exact twin_not_top hwf h₂ hiff hloc hseat htopqq
    have hcov1 : 1 ≤ covrest.length := by
      obtain ⟨u, us, rfl⟩ := list_cons_of_ne_nil hcovne
      rw [List.length_cons]
      omega
    have hsegeq : (st.piles q).faceUp = x.twin :: covrest := by
      rw [hbsnil] at hjoin
      exact hjoin.symm
    -- STEP 2's record: ba is forced to an empty anchor (kings fit nothing)
    obtain ⟨q₂, hhold₂, hcp₂, hseg₂ne, hs₂⟩ := step_tabToTab_inv h₂step
    have hhold₁ : st₁.pileHolding x.twin = some q :=
      (pileHolding_eq_some_iff hwf₁).2 (by
        rw [hst₁ne q (Ne.symm hpq)]
        exact htqmem)
    rw [pileHolding_inj hhold₂ hhold₁] at hs₂
    rw [show st₁.piles q = st.piles q from hst₁ne q (Ne.symm hpq)] at hs₂
    obtain ⟨m, hbaeq, hmempty⟩ : ∃ m, ba = Sum.inl m ∧ (st₁.piles m).isEmpty = true := by
      cases ba with
      | inl m =>
          obtain ⟨hempty, -⟩ := canPlace_inl hcp₂
          exact ⟨m, rfl, hempty⟩
      | inr y =>
          obtain ⟨k, hpoy, hfitY⟩ := canPlace_inr hcp₂
          exact absurd hkingt (no_fit_king hfitY)
    rw [hbaeq] at hs₂
    have hmbas : ba = Sum.inl m := hbaeq
    -- the vacated pile q empties without a reveal (no hidden), m receives the run
    have hst₁q : st₁.piles q = st.piles q := hst₁ne q (Ne.symm hpq)
    have hst₁pEmpty : st₁.piles p = ⟨[], ([] : List Card)⟩ := by
      rw [hst₁p, show chop (st.piles p).faceUp = [] from hc₀nil,
        afterRunRemoved_bareEmpty hhidp]
    have hmq : m ≠ q := by
      intro hcon
      rw [hcon] at hmempty
      rw [hst₁q] at hmempty
      obtain ⟨-, hful⟩ := (Pile.isEmpty_eq _).mp hmempty
      rw [hsegeq] at hful
      exact absurd hful (List.cons_ne_nil x.twin covrest)
    -- st₂'s shape: m holds the twin's run, q is bare empty
    rw [hbsnil, hseg, afterRunRemoved_bareEmpty hhidq.1] at hs₂
    rw [putRun_eq_inl] at hs₂
    have hst₂exp : st₂ =
        (st₁.setPile q ⟨[], ([] : List Card)⟩).setPile m ⟨[], x.twin :: covrest⟩ :=
      hs₂
    have hst₂m : st₂.piles m = ⟨[], x.twin :: covrest⟩ := by
      rw [hst₂exp, setPile_piles_self]
    have hst₂q : st₂.piles q = ⟨[], ([] : List Card)⟩ := by
      rw [hst₂exp, setPile_piles_ne (show q ≠ m from Ne.symm hmq),
        setPile_piles_self]
    -- STEP 3's record: bb is forced to an empty anchor as well
    obtain ⟨c', hft₂, hc'x, hcp₃, hs₃⟩ := step_foundToTab_inv h₃step
    obtain ⟨kk, hbbeq, hkempty⟩ : ∃ kk, bb = Sum.inl kk ∧ (st₂.piles kk).isEmpty = true := by
      cases bb with
      | inl kk =>
          obtain ⟨hempty, -⟩ := canPlace_inl hcp₃
          exact ⟨kk, rfl, hempty⟩
      | inr z =>
          obtain ⟨k', hpoz, hfitZ⟩ := canPlace_inr hcp₃
          exact absurd hking (no_fit_king hfitZ)
    rw [hbbeq] at hs₃
    -- kk receives x verbatim; the anchors m and kk are distinct
    have hmkk : m ≠ kk := by
      intro hcon
      rw [← hcon] at hkempty
      rw [hst₂m] at hkempty
      obtain ⟨-, hful⟩ := (Pile.isEmpty_eq _).mp hkempty
      exact absurd hful (List.cons_ne_nil x.twin covrest)
    have hwexp : w =
        (st₂.setFound x.suit (chop (st₂.found x.suit))).setPile kk ⟨[], [x]⟩ := by
      rw [hs₃, putCard_eq_inl]
    have hwkk : w.piles kk = ⟨[], [x]⟩ := by
      rw [hwexp, setPile_piles_self]
    have hwm : w.piles m = st₂.piles m := by
      rw [hwexp, setPile_piles_ne hmkk]
      rfl
    have hwne : ∀ a', a' ≠ m → a' ≠ kk → a' ≠ p → a' ≠ q →
        w.piles a' = st.piles a' := by
      intro a' hm' hkk' hp' hq'
      rw [hwexp, setPile_piles_ne (show a' ≠ kk from hkk'),
        show ((st₂.setFound x.suit (chop (st₂.found x.suit))).piles a')
            = st₂.piles a' from rfl,
        hst₂exp,
        setPile_piles_ne (show a' ≠ m from hm'),
        setPile_piles_ne (show a' ≠ q from hq'),
        hst₁ne a' hp']
    -- THE ENDPOINT'S WITNESS AND IFF (king channel)
    refine ⟨x, hpinwx, ?_, ?_⟩
    · show (w.found x.twin.suit).length = x.rank.toIdx
      rw [hflat x.twin.suit]
      exact h₂
    · intro c
      constructor
      · intro hcr
        obtain ⟨hnc, a', hpoa, hseata⟩ := hcr
        have htopwa : (w.piles a').top = some c :=
          (pileOfTop_eq_some_iff hwfw).mp hpoa
        by_cases hcx : c = x
        · exact hcx
        have hncst : st.nextUp c = true := by
          show decide (c.rank.toIdx = (st.found c.suit).length) = true
          rw [show (st.found c.suit).length = (w.found c.suit).length from
              congrArg List.length (hflat c.suit).symm]
          exact hnc
        -- the rider-analysis shape (the m case, also reached when m = p):
        -- c is the twin's run-top, which raised at st: the iff kills it
        have hsegstop : lastOf (x.twin :: covrest) = some c → False := by
          intro hlastseg
          have hcmemq : c ∈ (st.piles q).faceUp := by
            rw [hsegeq]
            exact lastOf_mem hlastseg
          have htopqc : (st.piles q).top = some c := by
            show lastOf (st.piles q).faceUp = some c
            rw [hsegeq]
            exact hlastseg
          have hchopq : chop (st.piles q).faceUp ≠ [] := by
            rw [hsegeq]
            exact chop_ne_nil_of_len (by
              rw [List.length_cons]
              omega)
          exact absurd ((hiff c).1 ⟨hncst, q,
            (pileOfTop_eq_some_iff hwf).2 htopqc,
            Or.inl hchopq⟩) hcx
        by_cases ham : a' = m
        · rw [ham, hwm, hst₂m] at htopwa
          exact (hsegstop htopwa).elim
        by_cases hkk2 : a' = kk
        · rw [hkk2, hwkk] at htopwa
          have hlastx : (⟨[], [x]⟩ : Pile).top = some x :=
            show lastOf ([] ++ [x]) = some x from lastOf_snoc
          exact absurd (Option.some.inj (hlastx.symm.trans htopwa)).symm hcx
        by_cases haq : a' = q
        · by_cases hkqeq : kk = q
          · rw [haq, ← hkqeq, hwkk] at htopwa
            have hlastx : (⟨[], [x]⟩ : Pile).top = some x :=
              show lastOf ([] ++ [x]) = some x from lastOf_snoc
            exact absurd (Option.some.inj (hlastx.symm.trans htopwa)).symm hcx
          · have hqp : w.piles q = st₂.piles q := by
              rw [hwexp, setPile_piles_ne (show q ≠ kk from fun hc => hkqeq hc.symm)]
              rfl
            rw [haq, hqp, hst₂q] at htopwa
            have hnone : (⟨[], ([] : List Card)⟩ : Pile).top = none := rfl
            rw [hnone] at htopwa
            exact absurd htopwa (by simp)
        by_cases hap : a' = p
        · by_cases hmp : m = p
          · -- m = p: the twin's run sits at p and tops it
            have hwmeq : w.piles p = st₂.piles m := by
              rw [← hmp, hwm]
            rw [hap, hwmeq, hst₂m] at htopwa
            exact (hsegstop htopwa).elim
          · by_cases hkp : kk = p
            · rw [hap, ← hkp, hwkk] at htopwa
              have hlastx : (⟨[], [x]⟩ : Pile).top = some x :=
                show lastOf ([] ++ [x]) = some x from lastOf_snoc
              exact absurd (Option.some.inj (hlastx.symm.trans htopwa)).symm hcx
            · have hpp : w.piles p = st₂.piles p := by
                rw [hwexp, setPile_piles_ne (show p ≠ kk from fun hc => hkp hc.symm)]
                rfl
              have hpp2 : st₂.piles p = st₁.piles p := by
                rw [hst₂exp, setPile_piles_ne (show p ≠ m from fun hc => hmp hc.symm),
                  setPile_piles_ne (show p ≠ q from fun hc => hpq hc)]
              rw [hap, hpp, hpp2, hst₁pEmpty] at htopwa
              have hnone : (⟨[], ([] : List Card)⟩ : Pile).top = none := rfl
              rw [hnone] at htopwa
              exact absurd htopwa (by simp)
        · -- untouched pile: the license read at st, unchanged
          have hpila : w.piles a' = st.piles a' := hwne a' ham hkk2 hap haq
          rw [hpila] at htopwa hseata
          exact absurd ((hiff c).1 ⟨hncst, a',
            (pileOfTop_eq_some_iff hwf).2 htopwa, hseata⟩) hcx
      · intro hc
        rw [hc]
        exact hCRwx
  · -- THE NON-KING CHANNEL (x.rank ≠ king)
    -- x's seat: the king disjunct is out (twins were already split off) ⇒ seated
    have hc₀ne : chop (st.piles p).faceUp ≠ [] := by
      rcases hseatx with hch | ⟨-, hkk⟩
      · exact hch
      · exact absurd hkk hking
    have hfullp : (st.piles p).faceUp = chop (st.piles p).faceUp ++ [x] :=
      lastOf_chop (show lastOf (st.piles p).faceUp = some x from htopp)
    obtain ⟨z₀, hz₀last, hfitz₀⟩ := seated_top_under hwf htopp hc₀ne
    have hz₀mem : z₀ ∈ (st.piles p).faceUp := by
      rw [hfullp]
      exact List.mem_append.mpr (Or.inl (lastOf_mem hz₀last))
    -- pile q's parcel: the twin's segment and under-seat
    have htqmem : x.twin ∈ (st.piles q).faceUp := pileHolding_mem hloc
    obtain ⟨covrest, hseg⟩ := fromCard_eq_head_of_mem htqmem
    have hjoin : below x.twin (st.piles q).faceUp ++ (x.twin :: covrest)
        = (st.piles q).faceUp := by
      rw [← hseg]
      exact below_join (st.piles q).faceUp
    have hsegne : x.twin :: covrest ≠ [] := List.cons_ne_nil x.twin covrest
    have hbsne : below x.twin (st.piles q).faceUp ≠ [] := by
      rcases hseat with hbs | ⟨-, hkingt⟩
      · exact hbs
      · rw [Card.twin_rank] at hkingt
        exact absurd hkingt hking
    have hcovne : covrest ≠ [] := by
      intro hcovnil
      rw [hcovnil] at hseg
      have htopqq : (st.piles q).top = some x.twin := by
        show lastOf (st.piles q).faceUp = some x.twin
        rw [← hjoin, hcovnil]
        exact lastOf_snoc
      exact twin_not_top hwf h₂ hiff hloc hseat htopqq
    have hcov1 : 1 ≤ covrest.length := by
      obtain ⟨u, us, rfl⟩ := list_cons_of_ne_nil hcovne
      have hlen : (u :: us).length = us.length + 1 := List.length_cons
      rw [hlen]
      omega
    obtain ⟨z₁, hz₁last⟩ := lastOf_exists hbsne
    have hfit₁ : canSitOn x.twin z₁ = true :=
      runOK_join_head_sit _ covrest z₁ x.twin
        (by rw [hjoin]; exact hwf.runOK_of q) hz₁last
    have hpq : p ≠ q := by
      intro hcon
      have htqmem' : x.twin ∈ (st.piles p).faceUp := by rw [hcon]; exact htqmem
      exact twin_pile_ne hwf htopp htqmem'
    have hz₁memq : z₁ ∈ (st.piles q).faceUp := below_mem (lastOf_mem hz₁last)
    have hzz : z₀ ≠ z₁ := by
      intro hcon
      have hxz := (mem_faceUp_unique hwf hz₀mem q (Ne.symm hpq)).1
      rw [hcon] at hxz
      exact hxz hz₁memq
    -- STEP 2's record, located at st's lists (only pile p changed so far)
    obtain ⟨q₂, hhold₂, hcp₂, hseg₂ne, hs₂⟩ := step_tabToTab_inv h₂step
    have hhold₁ : st₁.pileHolding x.twin = some q :=
      (pileHolding_eq_some_iff hwf₁).2 (by
        rw [hst₁ne q (Ne.symm hpq)]
        exact htqmem)
    rw [pileHolding_inj hhold₂ hhold₁] at hs₂
    rw [show st₁.piles q = st.piles q from hst₁ne q (Ne.symm hpq)] at hs₂
    -- THE BASE PIN: ba is the exposed (x+1) under x
    have hbaz₀ : ba = Sum.inr z₀ := by
      cases ba with
      | inl m =>
          obtain ⟨-, hkingt⟩ := canPlace_inl hcp₂
          rw [Card.twin_rank] at hkingt
          exact absurd hkingt hking
      | inr y =>
          obtain ⟨k, hpoy, hfitY⟩ := canPlace_inr hcp₂
          have hfitXy : canSitOn x y = true := by
            obtain ⟨hrk, hcol⟩ := (canSitOn_eq x.twin y).mp hfitY
            rw [show x.twin.rank.toIdx = x.rank.toIdx from rfl] at hrk
            rw [show x.twin.suit.color = x.suit.color from
              Suit.color_twin x.suit] at hcol
            exact (canSitOn_eq x y).2 ⟨hrk, hcol⟩
          rcases conjugate_fit_pin hfitz₀ hfit₁ hzz hfitXy with hy | hy
          · exact congrArg Sum.inr hy
          · exfalso
            rw [hy] at hpoy
            have htopk : (st₁.piles k).top = some z₁ :=
              (pileOfTop_eq_some_iff hwf₁).mp hpoy
            by_cases hkq : k = q
            · rw [hkq, hst₁ne q (Ne.symm hpq)] at htopk
              have hlastq : lastOf (below x.twin (st.piles q).faceUp
                  ++ (x.twin :: covrest)) = some z₁ := by
                rw [hjoin]
                exact htopk
              have hlastseg : lastOf (x.twin :: covrest) = some z₁ :=
                lastOf_append (x.twin :: covrest) hsegne z₁ hlastq
              have hz₁seg : z₁ ∈ x.twin :: covrest := lastOf_mem hlastseg
              have hnd : (below x.twin (st.piles q).faceUp
                  ++ (x.twin :: covrest)).Nodup := by
                rw [hjoin]; exact runOK_nodup (hwf.runOK_of q)
              exact nodup_append_notmem hnd (lastOf_mem hz₁last) hz₁seg
            · by_cases hkp : k = p
              · rw [hkp, hst₁p, afterRunRemoved_ne hc₀ne] at htopk
                have hlastz₁ : lastOf (chop (st.piles p).faceUp) = some z₁ := htopk
                exact hzz (Option.some.inj (hz₀last.symm.trans hlastz₁))
              · rw [hst₁ne k (fun hc => hkp hc)] at htopk
                have hz₁k : z₁ ∈ (st.piles k).faceUp := Pile.mem_of_top htopk
                exact (mem_faceUp_unique hwf hz₁memq k (fun hc => hkq hc)).1 hz₁k
    rw [hbaz₀] at hs₂
    -- the intermediate search: z₀ still tops pile p, nothing else tops it
    have hpoz₀ : (st₁.setPile q
        (Pile.afterRunRemoved (st.piles q)
          (below x.twin (st.piles q).faceUp))).pileOfTop z₀ = some p := by
      refine firstWhere_find (Anchor.mem_all p) ?_ ?_
      · show decide (((st₁.setPile q
            (Pile.afterRunRemoved (st.piles q)
              (below x.twin (st.piles q).faceUp))).topOf p) = some z₀) = true
        rw [setPile_topOf_ne hpq]
        show decide ((st₁.piles p).top = some z₀) = true
        rw [hst₁p, afterRunRemoved_ne hc₀ne]
        exact decide_eq_true (show ({ st.piles p with
          faceUp := chop (st.piles p).faceUp }).top = some z₀ from hz₀last)
      · intro y _hy hyne
        show decide (((st₁.setPile q
            (Pile.afterRunRemoved (st.piles q)
              (below x.twin (st.piles q).faceUp))).topOf y) = some z₀) = false
        by_cases hyq : y = q
        · rw [hyq]
          show decide (((st₁.setPile q
              (Pile.afterRunRemoved (st.piles q)
                (below x.twin (st.piles q).faceUp))).piles q).top = some z₀) = false
          rw [setPile_piles_self, afterRunRemoved_ne hbsne]
          have htopz₁ : ({ st.piles q with
              faceUp := below x.twin (st.piles q).faceUp } : Pile).top = some z₁ :=
            hz₁last
          rw [htopz₁]
          exact decide_false_of_not
            (fun hcon => hzz (Option.some.inj hcon).symm)
        · rw [setPile_topOf_ne hyq]
          show decide ((st₁.piles y).top = some z₀) = false
          rw [hst₁ne y hyne]
          exact decide_false_of_not (fun htop =>
            (mem_faceUp_unique hwf hz₀mem y hyne).1 (Pile.mem_of_top htop))
    -- st₂'s pile profile: p holds the twins' fuselage, q the exposed z₁
    have hst₂p : st₂.piles p =
        ⟨(st.piles p).hidden,
          chop (st.piles p).faceUp ++ (x.twin :: covrest)⟩ := by
      rw [hs₂, putRun_inr_eq hpoz₀, setPile_piles_self,
        setPile_piles_ne (show p ≠ q from hpq),
        hst₁p, hseg, afterRunRemoved_ne hc₀ne]
    have hst₂q : st₂.piles q =
        ⟨(st.piles q).hidden, below x.twin (st.piles q).faceUp⟩ := by
      rw [hs₂, putRun_inr_eq hpoz₀,
        setPile_piles_ne (show q ≠ p from Ne.symm hpq), setPile_piles_self,
        afterRunRemoved_ne hbsne]
    have hst₂ne : ∀ a', a' ≠ p → a' ≠ q → st₂.piles a' = st.piles a' := by
      intro a' hne' hne'q
      rw [hs₂, putRun_inr_eq hpoz₀,
        setPile_piles_ne (show a' ≠ p from hne'),
        setPile_piles_ne (show a' ≠ q from hne'q),
        hst₁ne a' hne']
    -- STEP 3's record and THE SECOND BASE PIN: bb is the twin's exposed base
    obtain ⟨c', hft₂, hc'x, hcp₃, hs₃⟩ := step_foundToTab_inv h₃step
    have hbbz₁ : bb = Sum.inr z₁ := by
      cases bb with
      | inl kk => obtain ⟨-, hkk⟩ := canPlace_inl hcp₃; exact absurd hkk hking
      | inr zz =>
          obtain ⟨k, hpozz, hfitZZ⟩ := canPlace_inr hcp₃
          rcases conjugate_fit_pin hfitz₀ hfit₁ hzz hfitZZ with hzz₀ | hzz₁
          · exfalso
            rw [hzz₀] at hpozz
            have htopk : (st₂.piles k).top = some z₀ :=
              (pileOfTop_eq_some_iff hwf₂).mp hpozz
            by_cases hkq : k = q
            · rw [hkq, hst₂q] at htopk
              have h1 : lastOf (below x.twin (st.piles q).faceUp) = some z₁ :=
                hz₁last
              have h2 : lastOf (below x.twin (st.piles q).faceUp) = some z₀ :=
                htopk
              exact hzz (Option.some.inj (h1.symm.trans h2)).symm
            · by_cases hkp : k = p
              · rw [hkp, hst₂p] at htopk
                have hlastseg : lastOf (x.twin :: covrest) = some z₀ :=
                  lastOf_append (x.twin :: covrest) hsegne z₀ htopk
                have hz₀seg : z₀ ∈ x.twin :: covrest := lastOf_mem hlastseg
                exact (mem_faceUp_unique hwf hz₀mem q (Ne.symm hpq)).1
                  (fromCard_mem (by rw [hseg]; exact hz₀seg))
              · rw [hst₂ne k hkp (fun hc => hkq hc)] at htopk
                exact (mem_faceUp_unique hwf hz₀mem k hkp).1
                  (Pile.mem_of_top htopk)
          · exact congrArg Sum.inr hzz₁
    rw [hbbz₁] at hs₃
    -- z₁ tops pile q at st₂, so the pulled-back card lands verbatim on it
    have hpoz₁ : st₂.pileOfTop z₁ = some q :=
      (pileOfTop_eq_some_iff hwf₂).2 (by
        show (st₂.piles q).top = some z₁
        rw [hst₂q]
        exact hz₁last)
    -- the w record: the found-passthrough putCard lands at q
    have hwexp : w = (st₂.setFound x.suit (chop (st₂.found x.suit))).setPile q
        { st₂.piles q with faceUp := (st₂.piles q).faceUp ++ [x] } := by
      rw [hs₃]
      exact putCard_inr_eq
        (st := st₂.setFound x.suit (chop (st₂.found x.suit)))
        (show (st₂.setFound x.suit (chop (st₂.found x.suit))).pileOfTop z₁
            = some q from hpoz₁)
    have hwq : w.piles q =
        ⟨(st.piles q).hidden, below x.twin (st.piles q).faceUp ++ [x]⟩ := by
      rw [hwexp, setPile_piles_self, hst₂q]
    have hwp : w.piles p = st₂.piles p := by
      rw [hwexp, setPile_piles_ne (show p ≠ q from hpq)]
      rfl
    have hwne : ∀ a', a' ≠ p → a' ≠ q → w.piles a' = st.piles a' := by
      intro a' hne' hne'q
      rw [hwexp, setPile_piles_ne (show a' ≠ q from hne'q)]
      exact hst₂ne a' hne' hne'q
    -- THE ENDPOINT'S WITNESS AND IFF: x is the last raiser standing
    refine ⟨x, hpinwx, ?_, ?_⟩
    · show (w.found x.twin.suit).length = x.rank.toIdx
      rw [hflat x.twin.suit]
      exact h₂
    · intro c
      constructor
      · -- every raiser at w is x
        intro hcr
        obtain ⟨hnc, a', hpoa, hseata⟩ := hcr
        have htopwa : (w.piles a').top = some c :=
          (pileOfTop_eq_some_iff hwfw).mp hpoa
        by_cases hcx : c = x
        · exact hcx
        by_cases ha'p : a' = p
        · -- the twin's run tops x's old pile: c rode with the twin
          rw [ha'p, hwp, hst₂p] at htopwa
          have hlastseg : lastOf (x.twin :: covrest) = some c :=
            lastOf_append (x.twin :: covrest) hsegne c htopwa
          have hcseg : c ∈ x.twin :: covrest := lastOf_mem hlastseg
          have hcmemq : c ∈ (st.piles q).faceUp := by
            rw [← hjoin]
            exact List.mem_append.mpr (Or.inr hcseg)
          have htopqc : (st.piles q).top = some c := by
            show lastOf (st.piles q).faceUp = some c
            rw [← hjoin,
              lastOf_append_eq (below x.twin (st.piles q).faceUp)
                (x.twin :: covrest) hsegne]
            exact hlastseg
          have hncst : st.nextUp c = true := by
            show decide (c.rank.toIdx = (st.found c.suit).length) = true
            rw [show (st.found c.suit).length = (w.found c.suit).length from
                congrArg List.length (hflat c.suit).symm]
            exact hnc
          have hlenq : 2 ≤ (st.piles q).faceUp.length := by
            rw [← hjoin, List.length_append]
            have hseg2 : 2 ≤ (x.twin :: covrest).length := by
              rw [List.length_cons]
              omega
            omega
          exact absurd ((hiff c).1 ⟨hncst, q,
            (pileOfTop_eq_some_iff hwf).2 htopqc,
            Or.inl (chop_ne_nil_of_len hlenq)⟩) hcx
        by_cases ha'q : a' = q
        · -- x landed here: the top is literally x
          rw [ha'q, hwq] at htopwa
          have hcc : some x = some c :=
            (lastOf_snoc).symm.trans htopwa
          exact absurd (Option.some.inj hcc).symm hcx
        · -- untouched pile: the license read at st, unchanged
          have hpila : w.piles a' = st.piles a' := hwne a' ha'p ha'q
          rw [hpila] at htopwa hseata
          have hncst : st.nextUp c = true := by
            show decide (c.rank.toIdx = (st.found c.suit).length) = true
            rw [show (st.found c.suit).length = (w.found c.suit).length from
                congrArg List.length (hflat c.suit).symm]
            exact hnc
          exact absurd ((hiff c).1 ⟨hncst, a',
            (pileOfTop_eq_some_iff hwf).2 htopwa, hseata⟩) hcx
      · -- x raises at w (the relic)
        intro hc
        rw [hc]
        exact hCRwx

/-! ## §8. The audit battery
(the discipline's per-head `#print axioms`; expected `[propext,
Quot.sound]` or fewer — zero `Classical.choice`, zero `sorryAx`). -/

#print axioms conjugate_netflat
#print axioms conjugate_relic
#print axioms conjugate_witness
#print axioms twin_pile_ne
#print axioms twin_not_top
#print axioms seated_top_under
#print axioms runOK_join_head_sit
#print axioms no_fit_king
#print axioms conjugate_fit_pin
#print axioms conjugate_forkState_corrected
