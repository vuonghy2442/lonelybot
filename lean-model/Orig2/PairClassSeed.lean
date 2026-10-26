import Orig2.Integrity

/-!
# Orig2.PairClassSeed — THE PAIRCLASS MIGRATION'S SEED KIT

The first, low-risk landing of the pairClass migration wave (the
founding ledger's first priority, `Orig2.lean` §THE MIGRATION CAKE):
the rows every later half cites, restated at the `Orig2` vocabulary.
No fork-physics content is claimed here — this card is the shared
substrate only.

Landed rows:

* **THE WITNESS BRIDGE** — `forkState_iff` (the existential detection
  unpacks into the per-witness parcel; `Orig/PairName.lean:32`).
* **THE CARD-ALGEBRA SEED** — `SeedKit.color_pair`,
  `SeedKit.rankColor_pair`, `SeedKit.suit_family` (ported from
  `Orig/RunOrTwin.lean`'s public seed kit; the same rows the frozen
  tier hoisted there).
* **THE FOUNDING-HEIGHT KIT** — `FoundKit.posOf`, `posOf_take_lt`,
  `posOf_upCards`, `get_in_take`, `upCards_get`, `mem_take_of_pos`,
  `mem_found_of_rung`, `mem_found_rank_lt`, `mem_found_iff_height`,
  `Rk`, `Rk_toIdx` (ported from `Orig/FoundKit.lean`, restated at
  `rungAt`; the `foundHeight`/`rungAt` spellings are `rfl`-equal).
* **THE S-LICENSE RUNG PIN** — `canRaiseS_rung`: an S-raisable card
  is next-up on its rung (`Orig/ForkStateS.lean:178`).  The `now`
  case is the vanilla pin; the `via` case is the `tabToTab`
  non-write of foundations (`step_tabToTab_inv` + `putRun_found`).
* **THE WITNESS RUNG PINS** — `forkState_witness_rungs`: at a fork
  witness both family rungs sit at the pair's rank index.
* **THE LOW-FAMILY FOUNDING ROW** — `pair_lowFamily_founded`: every
  same-family card strictly below the fork's rank is already founded
  at the fork (`Orig/PairConfine.lean:162`).

House compliance: additive leaf (`import Orig2.Integrity` only — the
certified seam plus the physics kit); per-row provenance cites; zero
`sorry`, zero `Classical.choice`; the battery at the tail.
-/

/-! ## §1. The witness bridge -/

/-- **THE WITNESS BRIDGE** — the existential detection unpacks into
the per-witness parcel.  PORTED VERBATIM from
`Orig/PairName.lean:32`. -/
theorem forkState_iff {st : State} :
    forkState st ↔ ∃ x, ForkWitness st x :=
  ⟨fun ⟨x, h1, h2⟩ => ⟨x, h1, h2⟩, fun ⟨x, h1, h2⟩ => ⟨x, h1, h2⟩⟩

/-! ## §2. The card-algebra seed (the public `SeedKit` names) -/

namespace SeedKit

/-- The two non-`a` colors of a two-color deck coincide.  PORTED
VERBATIM from `Orig/RunOrTwin.lean:64`. -/
theorem color_pair {a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) : u = v := by
  rcases a <;> rcases u <;> rcases v <;> simp_all

/-- Equal rank and equal color name the card, up to the twin flip.
PORTED VERBATIM from `Orig/RunOrTwin.lean:68`. -/
theorem rankColor_pair {c z : Card}
    (hr : z.rank.toIdx = c.rank.toIdx) (hc : z.suit.color = c.suit.color) :
    z = c ∨ z = c.twin := by
  rcases z with ⟨zs, zr⟩
  rcases c with ⟨cs, cr⟩
  have hrank : zr = cr := Rank.toIdx_inj hr
  subst hrank
  cases cs <;> cases zs <;> simp_all [Suit.color, Suit.twin, Card.twin]

/-- A shared color names the suit, up to the twin flip.  PORTED
VERBATIM from `Orig/RunOrTwin.lean:105`. -/
theorem suit_family {s t : Suit} (h : s.color = t.color) :
    s = t ∨ s = t.twin := by
  cases s <;> cases t <;> simp_all [Suit.color, Suit.twin]

/-- **`runOK` is suffix-closed** — a well-formed run's tail is
well-formed.  Fresh row (the migration wave's kit, the frozen-lineage
home `Orig/RunOrTwin.lean`'s SeedKit). -/
theorem runOK_suffix {l₁ l₂ : List Card}
    (h : runOK (l₁ ++ l₂) = true) : runOK l₂ = true := by
  induction l₁ with
  | nil => exact h
  | cons x xs ih =>
      cases hap : xs ++ l₂ with
      | nil =>
          cases l₂ with
          | nil => rfl
          | cons y t => simp at hap
      | cons y t =>
          simp only [List.cons_append] at h
          rw [hap] at h
          simp only [runOK, Bool.and_eq_true] at h
          exact ih (by rw [hap]; exact h.2)

/-- **The adjacent fit** — in a well-formed run, the card directly
above `c` fits `c` (rank one below, opposite color): the runOK
discipline is the FULL fit at every link.  PORTED from
`Orig/RunOrTwin.lean`'s SeedKit (`runOK_adjacent_fit`), the row the
flat characterization's mate-slide consumes. -/
theorem runOK_adjacent_fit (c d : Card) (P S : List Card)
    (h : runOK (P ++ c :: d :: S) = true) : canSitOn d c = true := by
  have h2 : runOK (c :: d :: S) = true := runOK_suffix h
  simp only [runOK, Bool.and_eq_true] at h2
  exact h2.1

end SeedKit

/-! ## §3. The founding-height kit -/

namespace FoundKit

/-- The first-occurrence position probe.  PORTED VERBATIM from
`Orig/FoundKit.lean:25`. -/
def posOf {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: t => if y = x then 0 else posOf x t + 1

/-- Membership in a truncation bounds the build position.  PORTED
VERBATIM from `Orig/FoundKit.lean:30`. -/
theorem posOf_take_lt {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (l : List α) (x : α), x ∈ l.take n → posOf x l < n := by
  intro n
  induction n with
  | zero => intro l x hmem; simp at hmem
  | succ n ih =>
      intro l x hmem
      cases l with
      | nil => simp at hmem
      | cons y t =>
          simp only [List.take] at hmem
          rcases List.mem_cons.mp hmem with heq | htl
          · simp only [posOf]
            rw [ite_eq_left heq.symm]
            omega
          · have hlt := ih t x htl
            simp only [posOf]
            split
            · omega
            · omega

/-- The build order is the rank order.  PORTED VERBATIM from
`Orig/FoundKit.lean:52`. -/
theorem posOf_upCards (σ : Suit) (r : Rank) :
    posOf (Card.mk σ r) (Suit.upCards σ) = r.toIdx := by
  cases σ <;> cases r <;> rfl

/-- An element at position `i` belongs to the first `n` entries of the
list.  PORTED VERBATIM from `Orig/FoundKit.lean:58`. -/
theorem get_in_take : ∀ {α : Type} (l : List α) (n i : Nat)
    (hl : i < l.length) (_hn : i < n), l.get ⟨i, hl⟩ ∈ l.take n := by
  intro α l n i hl hn
  induction n generalizing l i hl with
  | zero => exact absurd hn (by omega)
  | succ n ih =>
      cases l with
      | nil => exact absurd hl (by simp)
      | cons a t =>
          cases i with
          | zero =>
              show a ∈ a :: t.take n
              exact List.mem_cons.2 (Or.inl rfl)
          | succ i' =>
              simp only [List.length_cons] at hl
              refine List.mem_cons_of_mem a (ih t i' (by omega) (by omega))

/-- A card sits at its own build index in its suit's foundation
order.  PORTED VERBATIM from `Orig/FoundKit.lean:77`. -/
theorem upCards_get (z : Card)
    (h : z.rank.toIdx < z.suit.upCards.length) :
    z.suit.upCards.get ⟨z.rank.toIdx, h⟩ = z := by
  rcases z with ⟨zs, zr⟩
  cases zr <;> rfl

/-- Below the first-occurrence position is inside the take.  PORTED
VERBATIM from `Orig/FoundKit.lean:86`. -/
theorem mem_take_of_pos {α : Type} [DecidableEq α] :
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

/-- **THE FOUNDED-HEIGHT BRIDGE, forward half** — a suit rung
strictly above a card's rank index has already founded it.  PORTED
from `Orig/FoundKit.lean:117`, restated at `rungAt` (definitionally
the same term as `foundHeight`). -/
theorem mem_found_of_rung {st : State} (hwf : st.WF) {c : Card}
    (hlt : c.rank.toIdx < rungAt st c.suit) : c ∈ st.found c.suit := by
  have hlt' : c.rank.toIdx < (st.found c.suit).length := hlt
  obtain ⟨n, hpre⟩ := hwf.found_prefix c.suit
  have hlen : (st.found c.suit).length ≤ n := by
    rw [hpre]
    exact List.length_take_le n _
  have hn : c.rank.toIdx < n := by omega
  have h13 : c.suit.upCards.length = 13 := Suit.upCards_length c.suit
  have hl : c.rank.toIdx < c.suit.upCards.length := by
    rw [h13]; exact Rank.toIdx_lt c.rank
  have hget : c.suit.upCards.get ⟨c.rank.toIdx, hl⟩ = c :=
    upCards_get c hl
  have hmem0 : c.suit.upCards.get ⟨c.rank.toIdx, hl⟩ ∈
      c.suit.upCards.take n :=
    get_in_take c.suit.upCards n c.rank.toIdx hl hn
  rw [hget] at hmem0
  have hmem : c ∈ c.suit.upCards.take n := hmem0
  rwa [← hpre] at hmem

/-- **THE FOUNDED-HEIGHT BRIDGE, converse half** — a card on its own
suit's foundation sits strictly below the rung.  PORTED from
`Orig/FoundKit.lean:141`, restated at `rungAt`. -/
theorem mem_found_rank_lt {st : State} (hwf : st.WF) {d : Card}
    (hmem : d ∈ st.found d.suit) :
    d.rank.toIdx < rungAt st d.suit := by
  rcases d with ⟨s, r⟩
  have hmem' : Card.mk s r ∈ st.found s := hmem
  obtain ⟨n, hpre⟩ := hwf.found_prefix s
  rw [hpre] at hmem'
  have hpos := posOf_take_lt n _ _ hmem'
  have hidx : posOf (Card.mk s r) (Suit.upCards s) = r.toIdx :=
    posOf_upCards s r
  have h13 : (Suit.upCards s).length = 13 := Suit.upCards_length s
  have hlen : ((Suit.upCards s).take n).length = min n 13 := by
    rw [List.length_take, h13]
  have hfi : rungAt st s = ((Suit.upCards s).take n).length := by
    rw [show rungAt st s = (st.found s).length from rfl, ← hpre]
  have hpos' : r.toIdx < n := by
    rw [← hidx]
    exact hpos
  have h12 : r.toIdx < 13 := Rank.toIdx_lt r
  show r.toIdx < rungAt st s
  rw [hfi, hlen]
  omega

/-- **THE FOUNDED-HEIGHT IFF** — membership on a card's own suit
foundation is exactly sitting strictly below the rung.  PORTED from
`Orig/FoundKit.lean:274`, restated at `rungAt`. -/
theorem mem_found_iff_height {st : State} (hwf : st.WF) {c : Card} :
    c ∈ st.found c.suit ↔ c.rank.toIdx < rungAt st c.suit :=
  ⟨mem_found_rank_lt hwf, mem_found_of_rung hwf⟩

/-- The rank of a zero-based index, tabulated.  PORTED VERBATIM from
`Orig/FoundKit.lean:371` (the frozen tier's public home of the
rank tabulation; the in-tree private precedent is
`Orig2/Classification.lean:794`, which may retire to this public
home in a later pass). -/
def Rk : Nat → Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | 12 => .king | _ => .ace

/-- The tabulation inverts the rank index.  PORTED from
`Orig/FoundKit.lean:376`. -/
theorem Rk_toIdx : ∀ (k : Nat), k < 13 → (Rk k).toIdx = k := by
  intro k hk
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _
  | 8, _ | 9, _ | 10, _ | 11, _ | 12, _ => rfl
  | j + 13, hj => exact absurd hj (by omega)

end FoundKit

/-! ## §4. The rung pins -/

/-- **THE S-LICENSE RUNG PIN** — an S-raisable card is next-up on its
rung.  PORTED from `Orig/ForkStateS.lean:178` (the `now` leg is the
vanilla pin; the `via` leg's slide never writes foundations). -/
theorem canRaiseS_rung {st : State} {c : Card} (h : CanRaiseS st c) :
    rungAt st c.suit = c.rank.toIdx := by
  induction h with
  | now c hcan =>
      obtain ⟨hn, -⟩ := hcan
      have hnext :=
        of_decide_eq_true (by simpa only [State.nextUp] using hn)
      simp only [State.foundHeight] at hnext
      unfold rungAt
      rw [← hnext]
  | via c hl _ ih =>
      obtain ⟨d, b, hstep, -⟩ := hl
      obtain ⟨a, -, -, -, hs'⟩ := step_tabToTab_inv hstep
      rw [hs'] at ih
      unfold rungAt at ih
      rw [putRun_found] at ih
      unfold rungAt
      exact ih

/-- **THE WITNESS RUNG PINS** — at a fork witness both suits of the
pair family read the pair's rank index.  PORTED from the pins row of
`Orig/PairName.lean` (the `canRaiseS_rung` instantiation). -/
theorem forkState_witness_rungs {st : State} {x : Card} (hx : ForkWitness st x) :
    rungAt st x.suit = x.rank.toIdx ∧
      rungAt st x.twin.suit = x.rank.toIdx := by
  constructor
  · exact canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
  · have h := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
    rw [show x.twin.rank = x.rank from rfl] at h
    exact h

/-- **THE LOW-FAMILY FOUNDING ROW** — every same-family card strictly
below the fork's rank is already founded at the fork.  PORTED from
`Orig/PairConfine.lean:162`. -/
theorem pair_lowFamily_founded {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) {c : Card}
    (hcol : c.suit.color = x.suit.color)
    (hlt : c.rank.toIdx < x.rank.toIdx) :
    c ∈ st.found c.suit := by
  have hr : rungAt st c.suit = x.rank.toIdx := by
    rcases SeedKit.suit_family hcol with hs | hs
    · rw [hs]
      exact canRaiseS_rung ((hx.1 x).mp (Or.inl rfl))
    · rw [hs]
      have h2 : rungAt st x.twin.suit = x.rank.toIdx := by
        have h := canRaiseS_rung ((hx.1 x.twin).mp (Or.inr rfl))
        rw [show x.twin.rank = x.rank from rfl] at h
        exact h
      exact h2
  exact FoundKit.mem_found_of_rung hwf (by omega)

/-! ## The audit battery

Every head below is a port of a banked frozen-tier row; the battery
records the terminal grades.  Expected: `[propext]` or
`[propext, Quot.sound]`, never `sorryAx`, never `Classical.choice`. -/

#print axioms forkState_iff
#print axioms SeedKit.color_pair
#print axioms SeedKit.rankColor_pair
#print axioms SeedKit.suit_family
#print axioms SeedKit.runOK_suffix
#print axioms SeedKit.runOK_adjacent_fit
#print axioms FoundKit.mem_found_of_rung
#print axioms FoundKit.mem_found_rank_lt
#print axioms FoundKit.mem_found_iff_height
#print axioms FoundKit.Rk_toIdx
#print axioms canRaiseS_rung
#print axioms forkState_witness_rungs
#print axioms pair_lowFamily_founded
