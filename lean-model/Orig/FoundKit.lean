import Orig.Integrity
import Orig.Combine
import Orig.Reach

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

/-- Below the first-occurrence position is inside the take (lifted
from Dominance's private `mem_take_of_pos`; the corollary
`mem_upCards_take` rides it). -/
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

/-- The take saturates: at-or-past the list's length it is the whole
list (the `take_all` core lacks; the take/drop mono family's
overflow companion). -/
theorem take_ge_len : ∀ {α : Type} (l : List α) (k : Nat),
    l.length ≤ k → l.take k = l := by
  intro α l k
  induction k generalizing l with
  | zero =>
      intro h
      cases l with
      | nil => rfl
      | cons a t => exact absurd h (by simp)
  | succ k ih =>
      cases l with
      | nil => simp [List.take]
      | cons a t =>
          intro h
          have htle : t.length ≤ k := by
            simp only [List.length_cons] at h
            omega
          rw [List.take_succ_cons, ih t htle]

/-- Equal foundation heights give equal foundation CONTENT (the leaf's
copy of the congruence row, length-spelled; retires CanV3's private
`fiber_founds_eq` and delegates MacroInternal's `rung_found_congr`).
Low-cone proof: both founds are takes of the same build order, and
equal take-lengths pin the take indices up to the full-13 overflow. -/
theorem found_congr (u v : State) (hu : u.WF) (hv : v.WF) (s : Suit)
    (h : (u.found s).length = (v.found s).length) :
    u.found s = v.found s := by
  obtain ⟨n, hn⟩ := hu.found_prefix s
  obtain ⟨m, hm⟩ := hv.found_prefix s
  rw [hn, hm]
  have h13 : (s.upCards).length = 13 := Suit.upCards_length s
  have hln : ((s.upCards).take n).length = min n 13 := by
    rw [List.length_take, h13]
  have hlm : ((s.upCards).take m).length = min m 13 := by
    rw [List.length_take, h13]
  have hmin : ((s.upCards).take n).length = ((s.upCards).take m).length := by
    rw [← hn, ← hm]
    exact h
  by_cases h1 : 13 ≤ n
  · rw [take_ge_len (s.upCards) n (by rw [h13]; omega)] at hmin
    by_cases h2 : 13 ≤ m
    · rw [take_ge_len (s.upCards) n (by rw [h13]; omega)]
      rw [take_ge_len (s.upCards) m (by rw [h13]; omega)]
    · exact absurd hmin (by rw [hlm]; omega)
  · by_cases h2 : 13 ≤ m
    · rw [take_ge_len (s.upCards) m (by rw [h13]; omega)] at hmin
      exact absurd hmin.symm (by rw [hln]; omega)
    · have hnm : n = m := by omega
      rw [hnm]

theorem shuffle_wf (s : State) : ∀ {play : List Move} {w : State},
    ShufflePlayW s play w → s.WF → w.WF := by
  intro play w h
  induction h with
  | nil u => intro hwfs; exact hwfs
  | @cons s₀ m s₁ rest w₀ hrev hstep hrest ih =>
      intro hwfs
      exact ih (step_wf hwfs hstep)

/-- **THE FIVE-ZONE CENSUS** — at a WF state every card sits in
exactly one of the five zones (lifted from the retired per-file
copies `sequ_zone_residency`/`conf_zone_residency`; OriginLock's
`lock_zone_residency` delegates here).  The conserved deck being
somewhere-at-all, made a lemma. -/
theorem zone_residency (st : State) (hwf : st.WF) (d : Card) :
    (∃ s, d ∈ st.found s) ∨ (∃ k, d ∈ (st.piles k).hidden) ∨
    (∃ k, d ∈ (st.piles k).faceUp) ∨ d ∈ st.stock ∨ d ∈ st.waste := by
  have h1 : st.cardCount d = 1 := hwf.cardCount_eq (Card.mem_universe d)
  unfold State.cardCount at h1
  cases hL : ((st.zones.flatMap id).filter fun x => decide (x = d)) with
  | nil =>
      rw [hL] at h1
      simp at h1
  | cons x xs =>
      have hxmem : x ∈ (st.zones.flatMap id).filter
          (fun x => decide (x = d)) := by
        rw [hL]
        exact List.mem_cons_self ..
      obtain ⟨hxeq, hxz⟩ := List.mem_filter.mp hxmem
      have hxd : x = d := of_decide_eq_true hxz
      obtain ⟨z, hz, hdz⟩ := List.mem_flatMap.mp hxeq
      have hdzd : d ∈ z := by rw [← hxd]; exact hdz
      have hspl : st.zones = (Suit.all.map st.found) ++
          ((Anchor.all.map fun a =>
            (st.piles a).hidden ++ (st.piles a).faceUp) ++
            [st.stock, st.waste]) := rfl
      rw [hspl] at hz
      rcases List.mem_append.mp hz with hA | hB
      · obtain ⟨s, -, hzs⟩ := List.mem_map.mp hA
        exact Or.inl ⟨s, by rw [← hzs] at hdzd; exact hdzd⟩
      · rcases List.mem_append.mp hB with hC | hD
        · obtain ⟨k, -, hzk⟩ := List.mem_map.mp hC
          rw [← hzk] at hdzd
          rcases List.mem_append.mp hdzd with hH | hF
          · exact Or.inr (Or.inl ⟨k, hH⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨k, hF⟩))
        · rcases List.mem_cons.mp hD with hS | hW
          · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
            rw [← hS]
            exact hdzd
          · rw [List.mem_singleton] at hW
            refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
            rw [← hW]
            exact hdzd

/-- **THE FOUNDED-HEIGHT IFF** — the founding-membership bridge as one
line: a card is on its own suit's foundation exactly when its rank
index sits strictly under the foundation's height.  (Stated in the
low cone's `foundHeight`; the high cone's `rungAt` cites unify by the
`rfl` bridge.) -/
theorem mem_found_iff_height {st : State} (hwf : st.WF) {c : Card} :
    c ∈ st.found c.suit ↔ c.rank.toIdx < st.foundHeight c.suit :=
  ⟨mem_found_rank_lt hwf, mem_found_of_rung hwf⟩

/-- Membership in a take is membership in the list (lifted from the
retired `sequ_mem_of_take`). -/
theorem mem_of_take : ∀ {α : Type} (l : List α) (n : Nat) {x : α},
    x ∈ l.take n → x ∈ l := by
  intro α l n
  induction n generalizing l with
  | zero =>
      intro x h
      simp [List.take] at h
  | succ n ih =>
      intro x h
      cases l with
      | nil => simp [List.take] at h
      | cons a t =>
          rw [List.take_succ_cons] at h
          rcases List.mem_cons.mp h with he | hrest
          · subst he; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem a (ih t hrest)

/-- Membership in a drop is membership in the list (lifted from the
retired `sequ_mem_of_drop`). -/
theorem mem_of_drop {α : Type} : ∀ (l : List α) (n : Nat) {x : α},
    x ∈ l.drop n → x ∈ l := by
  intro l n
  induction n generalizing l with
  | zero =>
      intro x h
      exact h
  | succ n ih =>
      intro x h
      cases l with
      | nil => simp [List.drop] at h
      | cons a t =>
          simp only [List.drop] at h
          exact List.mem_cons_of_mem a (ih t h)

/-- **THE DEAL-SPLITTER** (the draw's recycle/deal membership row —
lifted from the retired four-copy family (sequ/conf/lock/seat
`dealUpTo_mem`); a member of the list lands in the dealt half or
stays in the remainder). -/
theorem dealUpTo_mem (d : Card) :
    ∀ (k : Nat) (l : List Card),
      d ∈ l → d ∈ (State.dealUpTo k l).1 ∨ d ∈ (State.dealUpTo k l).2 := by
  intro k
  induction k with
  | zero => intro l hd; exact Or.inr hd
  | succ k ih =>
      intro l hd
      cases l with
      | nil => exact absurd hd (by simp)
      | cons x xs =>
          by_cases hdx : x = d
          · subst hdx
            left
            simp only [State.dealUpTo]
            exact List.mem_cons_self ..
          · rcases List.mem_cons.mp hd with heq | htl
            · exact absurd heq (fun hcon => hdx hcon.symm)
            · rcases ih xs htl with h1 | h2
              · left
                simp only [State.dealUpTo]
                exact List.mem_cons.mpr (Or.inr h1)
              · right
                simp only [State.dealUpTo]
                exact h2

/-- The dealt half only holds existing stock. -/
theorem dealUpTo_mem_take {d : Card} (k : Nat) (l : List Card)
    (h : d ∈ (State.dealUpTo k l).1) : d ∈ l := by
  rw [dealUpTo_eq_take_drop k l] at h
  exact mem_of_take l k h

/-- The remaining half only holds existing stock. -/
theorem dealUpTo_mem_drop {d : Card} (k : Nat) (l : List Card)
    (h : d ∈ (State.dealUpTo k l).2) : d ∈ l := by
  rw [dealUpTo_eq_take_drop k l] at h
  exact mem_of_drop l k h

/-- A foundation row holds only its own suit's cards (lifted from the
retired `sequ_found_suit`; OriginLock's `lock_found_suit` twin also
retires against this row). -/
theorem found_suit {st : State} (hwf : st.WF) {c : Card} {s : Suit}
    (hmem : c ∈ st.found s) : c.suit = s := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  rw [hn] at hmem
  have hmem2 : c ∈ s.upCards := mem_of_take _ _ hmem
  obtain ⟨r, -, hmk⟩ := List.mem_map.mp hmem2
  subst hmk
  rfl

/-- The rank of a zero-based index, tabulated (lifted from the
retired per-file makers — Classify's `Rk`, OriginLock's `lockRk`,
PairClassZones' `pczRk`; the strike retires the copies). -/
def Rk : Nat → Rank
  | 0 => .ace | 1 => .two | 2 => .three | 3 => .four | 4 => .five | 5 => .six
  | 6 => .seven | 7 => .eight | 8 => .nine | 9 => .ten | 10 => .jack | 11 => .queen
  | 12 => .king | _ => .ace

theorem Rk_toIdx : ∀ (k : Nat), k < 13 → (Rk k).toIdx = k := by
  intro k hk
  match k with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | 6 => rfl
  | 7 => rfl
  | 8 => rfl
  | 9 => rfl
  | 10 => rfl
  | 11 => rfl
  | 12 => rfl
  | j + 13 => exact absurd hk (by omega)

/-- The take never outgrows the list (lifted from the retired
`pcz_take_len_le` mini-induction — core's `List.length_take_le`
states the `≤ n` form, not this `≤ l.length` form). -/
theorem take_len_le : ∀ {α : Type} (l : List α) (n : Nat),
    (l.take n).length ≤ l.length := by
  intro α l n
  induction n generalizing l with
  | zero => cases l <;> simp [List.take]
  | succ n ih =>
      cases l with
      | nil => simp [List.take]
      | cons a t =>
          simp only [List.take, List.length_cons]
          have h2 := ih t
          omega

/-- The rung never passes the build order's length (WF's prefix is a
bounded take). -/
theorem rung_le {st : State} (hwf : st.WF) (σ : Suit) :
    st.foundHeight σ ≤ 13 := by
  obtain ⟨n, hpre⟩ := hwf.found_prefix σ
  have h1 : ((σ.upCards).take n).length ≤ (σ.upCards).length :=
    take_len_le _ _
  have h13 : (σ.upCards).length = 13 := Suit.upCards_length σ
  have hb : st.foundHeight σ = ((σ.upCards).take n).length := by
    have h2 : st.foundHeight σ = (st.found σ).length := rfl
    rw [h2, hpre]
  rw [hb]
  rw [h13] at h1
  exact h1

end FoundKit

/-! ## The audit battery -/

#print axioms FoundKit.mem_found_of_rung
#print axioms FoundKit.mem_found_rank_lt
#print axioms FoundKit.mem_found_iff_height
#print axioms FoundKit.mem_of_take
#print axioms FoundKit.mem_of_drop
#print axioms FoundKit.found_suit
#print axioms FoundKit.Rk_toIdx
#print axioms FoundKit.take_len_le
#print axioms FoundKit.rung_le
#print axioms FoundKit.get_in_take
#print axioms FoundKit.upCards_get
#print axioms FoundKit.mem_take_of_pos
#print axioms FoundKit.take_ge_len
#print axioms FoundKit.found_congr
#print axioms FoundKit.shuffle_wf
#print axioms FoundKit.zone_residency
#print axioms FoundKit.dealUpTo_mem
#print axioms FoundKit.dealUpTo_mem_take
#print axioms FoundKit.dealUpTo_mem_drop
