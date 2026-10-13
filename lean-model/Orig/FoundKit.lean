import Orig.Integrity

/-!
# Orig.FoundKit — THE FOUNDING-HEIGHT KIT (the shared-kit leaf)

The hoist-down landing (2026-10-13): the founding-height machinery
re-homed from `Orig/PairConfine.lean`'s namespace to a stratum leaf
beside the kernel, so that EVERY chapter — including those below
PairConfine (SlabEquiv, Dominance, PairClassZones) — cites ONE home
and the per-file `pcz_`/`sequ_`/private `posOf` copies retire.  The
names are unchanged (`namespace FoundKit`): every existing cite in
the tree resolves as before, and no consumer rewrites at all.

Proof note: the forward bridge is re-derived in the LOW-cone shape
(Dominance's self-contained template — `WF.found_prefix` + core
List lemmas), NOT via `rung_found_prefix` (which lives in
`Orig/MacroInternal.lean`, above this leaf in the import DAG).
-/

namespace FoundKit

/-- The first-occurrence position probe. -/
def posOf {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: t => if y = x then 0 else posOf x t + 1

/-- Membership in a truncation bounds the build position. -/
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

/-- The build order is the rank order. -/
theorem posOf_upCards (σ : Suit) (r : Rank) :
    posOf (Card.mk σ r) (Suit.upCards σ) = r.toIdx := by
  cases σ <;> cases r <;> rfl

/-- An element at position `i` belongs to the first `n` entries of the
list. -/
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
order. -/
theorem upCards_get (z : Card)
    (h : z.rank.toIdx < z.suit.upCards.length) :
    z.suit.upCards.get ⟨z.rank.toIdx, h⟩ = z := by
  rcases z with ⟨zs, zr⟩
  cases zr <;> rfl

/-- **THE FOUNDED-HEIGHT BRIDGE, forward half** — a suit rung (a.k.a.
`foundHeight`, the high cone's `rungAt` — same term up to a `rfl`)
strictly above a card's rank index has already founded it.  Proof in
the low-cone shape (no `rung_found_prefix`): `WF.found_prefix` + the
take-length pin + the kit's own `get_in_take`/`upCards_get`.
`st.foundHeight s = (st.found s).length` by `rfl`. -/
theorem mem_found_of_rung {st : State} (hwf : st.WF) {c : Card}
    (hlt : c.rank.toIdx < st.foundHeight c.suit) : c ∈ st.found c.suit := by
  have hrw : st.foundHeight c.suit = (st.found c.suit).length := rfl
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
suit's foundation sits strictly below the rung.  (Low-cone proof: the
`posOf` bound against the existential take-length, closed by `omega`
over the `min`-form — the one genuinely fresh proof of this landing.) -/
theorem mem_found_rank_lt {st : State} (hwf : st.WF) {d : Card}
    (hmem : d ∈ st.found d.suit) :
    d.rank.toIdx < st.foundHeight d.suit := by
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
  have hfi : st.foundHeight s = ((Suit.upCards s).take n).length := by
    have h1 : st.foundHeight s = (st.found s).length := rfl
    rw [h1, ← hpre]
  show r.toIdx < st.foundHeight s
  have h12 : r.toIdx < 13 := Rank.toIdx_lt r
  omega

/-- **THE FOUNDED-HEIGHT IFF** — the founding-membership bridge as one
line: a card is on its own suit's foundation exactly when its rank
index sits strictly under the foundation's height.  (Stated in the
low cone's `foundHeight`; the high cone's `rungAt` cites unify by the
`rfl` bridge.) -/
theorem mem_found_iff_height {st : State} (hwf : st.WF) {c : Card} :
    c ∈ st.found c.suit ↔ c.rank.toIdx < st.foundHeight c.suit :=
  ⟨mem_found_rank_lt hwf, mem_found_of_rung hwf⟩

end FoundKit

/-! ## The audit battery -/

#print axioms FoundKit.mem_found_of_rung
#print axioms FoundKit.mem_found_rank_lt
#print axioms FoundKit.mem_found_iff_height
