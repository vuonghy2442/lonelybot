import Orig.OrphanSeat
import Orig.PairConfine

/-!
# Orig.CrossFamilyStatic — THE ORPHAN-SEAT CARD (the cross-family static kill)

The cross-family axis's three corner residues share one STATIC kill
that never prices the journey's epochs: the census debts, the one-leg
transfer machinery, and the material-competition routes are all
unnecessary for the interlock.  The insight: the routes chased the
SATURATION-PINNED COVERS (rank `r−1` cards), but the contradiction
lives one stratum DEEPER, on the ORPHAN card — a card whose
foundation-residency flips between the twojourney endpoints does not
need a legal seat at any pop EPOCH; it needs a seat at the END, and
the far fork's saturation has already consumed every seat it could
take.

* The named residue **`cross_orphan_seat`** lives in
  `Orig/OrphanSeat.lean` since the dedup-hoist (the upward door's
  backward route in `Orig/PairConfine` consumes the same residue, and
  this file's `Orig.PairConfine` import forbids the residue living
  here); this card consumes it by import, statement byte-identical
  to the original landing.
* §1 **`cross_orphan_kill`** — THE STATIC KILL (proved): two
  separated-color forks joined by a witness shuffle, the second
  fork's cover suit reading at least TWO below `r₂` at the second
  fork — then the ORPHAN card (rank index `r₂ − 2`, of the cover's
  suit) is founded at the first fork (the first family's low row,
  `pair_lowFamily_founded`) yet exiled from its foundation at the
  second (the founded-membership bridge against the deep read), so by
  the residue it sits face-up at the second fork on a BELOW-NEIGHBOR
  of the SECOND fork's family one below its rank — and the second
  fork saturates every such card into its foundations
  (`pair_lowFamily_founded` there), while face-up and founded cannot
  coexist (`mem_faceUp_only`).  `False`.

CONSUMED BY `Orig/CrossFamily.lean`: each of its three corner
residues (`cross_equal_rank_kick`, `cross_strata_consec`,
`cross_strata_gap`) closes by one call of §2's kill; their hypothesis
packages carry exactly the needed premises, so no driver rework.  The
regime-sensitivity is exact: the kill engages precisely the rank
orders the class symmetry lets through (`r₂ ≤ r₁`), the orphan's
below-cell sits strictly beneath the second fork's pinned stratum,
and no census hypothesis is consulted.

House compliance: additive leaf (`import Orig.PairConfine` only); fresh
private kit copies per the dedup discipline; the one named residue
carries its route in its docstring; every fresh head audited.
-/

/-! ## §0. The private kit (per-file copies, the house dedup discipline) -/

/-- The rank of a given index: every index below 13 is some rank's
`toIdx` (the 13-cell enumeration; `cases` chains rewrite the bound
hypothesis at each level, the final arm closing by `omega`). -/
private theorem xstat_rank_of_idx {n : Nat} (hn : n < 13) :
    ∃ r : Rank, r.toIdx = n := by
  cases n with
  | zero => exact ⟨Rank.ace, rfl⟩
  | succ n1 =>
    cases n1 with
    | zero => exact ⟨Rank.two, rfl⟩
    | succ n2 =>
      cases n2 with
      | zero => exact ⟨Rank.three, rfl⟩
      | succ n3 =>
        cases n3 with
        | zero => exact ⟨Rank.four, rfl⟩
        | succ n4 =>
          cases n4 with
          | zero => exact ⟨Rank.five, rfl⟩
          | succ n5 =>
            cases n5 with
            | zero => exact ⟨Rank.six, rfl⟩
            | succ n6 =>
              cases n6 with
              | zero => exact ⟨Rank.seven, rfl⟩
              | succ n7 =>
                cases n7 with
                | zero => exact ⟨Rank.eight, rfl⟩
                | succ n8 =>
                  cases n8 with
                  | zero => exact ⟨Rank.nine, rfl⟩
                  | succ n9 =>
                    cases n9 with
                    | zero => exact ⟨Rank.ten, rfl⟩
                    | succ n10 =>
                      cases n10 with
                      | zero => exact ⟨Rank.jack, rfl⟩
                      | succ n11 =>
                        cases n11 with
                        | zero => exact ⟨Rank.queen, rfl⟩
                        | succ n12 =>
                          cases n12 with
                          | zero => exact ⟨Rank.king, rfl⟩
                          | succ m => exfalso; omega

/-- Two colors that both differ from a third agree (the copy of
`Orig/CrossFamily.lean`'s private `xfam_color_pair`, itself the copy
of `Orig/RunOrTwin.lean`'s private `color_pair`). -/
private theorem xstat_color_pair {a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) :
    u = v := by
  rcases a <;> rcases u <;> rcases v <;> simp_all

/-! The take-position kit (the copies of `Orig/Dominance.lean`'s
private helper and its converse, exactly as `Orig/CrossFamily.lean`'s
§0 carried its own: the build order is the rank order, membership in
a bounded take bounds the first-occurrence position). -/

/-- The position of `x` in `l` (its first-occurrence index). -/
private def xstat_posOf {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: t => if y = x then 0 else xstat_posOf x t + 1

/-- Membership in a bounded take bounds the first-occurrence
position. -/
private theorem xstat_mem_take_pos {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (l : List α) (x : α), x ∈ l.take n → xstat_posOf x l < n := by
  intro n
  induction n with
  | zero =>
      intro l x hmem
      simp [List.take] at hmem
  | succ n ih =>
      intro l x hmem
      cases l with
      | nil => simp [List.take] at hmem
      | cons y t =>
          rw [List.take_succ_cons] at hmem
          by_cases hyx : y = x
          · have hp : xstat_posOf x (y :: t) = 0 := by
              show (if y = x then 0 else xstat_posOf x t + 1) = 0
              rw [if_pos hyx]
            omega
          · have hp : xstat_posOf x (y :: t) = xstat_posOf x t + 1 := by
              show (if y = x then 0 else xstat_posOf x t + 1) = _
              rw [if_neg hyx]
            have hmem' : x ∈ t.take n := by
              rcases List.mem_cons.1 hmem with he | hrest
              · exact absurd he.symm hyx
              · exact hrest
            have hlt := ih t x hmem'
            omega

/-- The build order is the rank order. -/
private theorem xstat_posOf_upCards (σ : Suit) (r : Rank) :
    xstat_posOf (Card.mk σ r) (Suit.upCards σ) = r.toIdx := by
  cases σ <;> cases r <;> rfl

/-- **THE FOUNDED-MEMBERSHIP BRIDGE** — a card on its own suit's
foundation sits strictly below the foundation's top (the copy of
`Orig/CrossFamily.lean`'s private `xfam_mem_found_rank_lt`: the
founded prefix is the build order's take). -/
private theorem xstat_mem_found_rank_lt {st : State} (hwf : st.WF) {d : Card}
    (hmem : d ∈ st.found d.suit) :
    d.rank.toIdx < rungAt st d.suit := by
  rcases d with ⟨s, r⟩
  have hmem' : Card.mk s r ∈ st.found s := hmem
  have hpre := rung_found_prefix st hwf s
  rw [hpre] at hmem'
  have hpos : xstat_posOf (Card.mk s r) (Suit.upCards s) < rungAt st s :=
    xstat_mem_take_pos _ _ _ hmem'
  have hidx := xstat_posOf_upCards s r
  show r.toIdx < rungAt st s
  omega

/-! ## §1. The static kill (the residue consumed by import) -/

/-- **THE ORPHAN KILL** — the cross-family interlock's static core.
Two separated-color forks joined by one witness shuffle (`hcol`:
different pairs entirely), the second fork's rank weakly below the
first's (`hle`: the regime the class symmetry lets through), and the
deep x-suit pin at the second fork (`hdeep`: some x-family suit `σ`
— in the consuming corners, the twin-cover `d₂`'s own suit read
through its `nextUp = false` pin — reads at least two below `r₂`):
the ORPHAN card (rank index `r₂ − 2` of suit `σ`) is founded at the
first fork (the first family's low row) yet exiled at the second
(the founded-membership bridge against the deep read), so by the
residue it sits face-up on the second fork's tableau, seated under
the fit lattice on a BELOW-NEIGHBOR of the SECOND fork's color family
one below its rank — and the second fork's saturation founds EVERY
such card (`pair_lowFamily_founded`), against the face-up/founded
disjointness of `mem_faceUp_only`.  The full census debt machinery of
the old routes is never consulted. -/
theorem cross_orphan_kill {st₁ st₂ : State} (hwf₁ : st₁.WF) (hwf₂ : st₂.WF)
    {τ : List Move} (hτ : ShufflePlayW st₁ τ st₂)
    {x y : Card} (hx : ForkWitness st₁ x) (hy : ForkWitness st₂ y)
    (hcol : y.suit.color ≠ x.suit.color)
    (hle : y.rank.toIdx ≤ x.rank.toIdx)
    (σ : Suit) (hσcol : σ.color = x.suit.color)
    (hdeep : rungAt st₂ σ + 2 ≤ y.rank.toIdx) :
    False := by
  -- the deep read forces r₂ ≥ 2 (foundations are never negative)
  have hy2 : 2 ≤ y.rank.toIdx := by omega
  -- the orphan's rank index exists
  have hidx : y.rank.toIdx - 2 < 13 := by
    have hy13 := Rank.toIdx_lt y.rank
    omega
  obtain ⟨r', hr'⟩ := xstat_rank_of_idx hidx
  obtain ⟨e, hesuit, heidx, henk⟩ : ∃ e : Card,
      e.suit = σ ∧ e.rank.toIdx + 2 = y.rank.toIdx ∧ e.rank ≠ Rank.king := by
    refine ⟨Card.mk σ r', rfl, ?_, ?_⟩
    · show r'.toIdx + 2 = y.rank.toIdx
      omega
    · show r' ≠ Rank.king
      intro hc
      rw [hc] at hr'
      have hk12 : Rank.king.toIdx = 12 := rfl
      have hy13 := Rank.toIdx_lt y.rank
      omega
  -- the orphan is x-family
  have hecol : e.suit.color = x.suit.color := by
    rw [hesuit]
    exact hσcol
  -- the orphan is FOUNDED at the first fork (the first family's low row)
  have hmem₁ : e ∈ st₁.found e.suit :=
    pair_lowFamily_founded hwf₁ hx hecol (by omega)
  -- the orphan is EXILED from its foundation at the second fork
  have hout₁ : e ∉ st₂.found e.suit := by
    intro hcon
    have hlt := xstat_mem_found_rank_lt hwf₂ hcon
    rw [hesuit] at hlt
    omega
  -- the residue reads the end-state seat: a face-up pile a, a face-up
  -- below-neighbor b, and the fit
  obtain ⟨a, b, hemem, hbmem, hfit⟩ :=
    cross_orphan_seat hwf₁ hτ henk hmem₁ hout₁
  -- the fit names b: rank one above the orphan (r₂ − 1), opposite color
  obtain ⟨hbr, hbc⟩ := (canSitOn_eq e b).mp hfit
  -- b names the SECOND fork's family
  have hxne : x.suit.color ≠ b.suit.color := by
    rw [← hecol]
    exact hbc
  have hbycol : b.suit.color = y.suit.color :=
    xstat_color_pair hxne (Ne.symm hcol)
  -- the second fork's saturation founds EVERY such card — b included
  have hmem₂ : b ∈ st₂.found b.suit :=
    pair_lowFamily_founded hwf₂ hy hbycol (by omega)
  -- face-up and founded cannot coexist at a WF state
  exact (mem_faceUp_only hwf₂ hbmem).2.2.2.2 b.suit hmem₂

/-! ## The audit battery

`#print axioms` per fresh head: the private kit rows (the rank
enumeration, the color pair, the take-position copies, the
founded-membership bridge) are zero-`sorry` and read
`[propext, Quot.sound]`-grade (banked chain only); the named residue
`cross_orphan_seat` carries this file's single `sorryAx`; the kill
`cross_orphan_kill` inherits exactly that and NOTHING else — so each
consuming corner of `Orig/CrossFamily.lean` trades its own research-
grade chase for this one mechanical residue. -/

#print axioms xstat_rank_of_idx
#print axioms xstat_color_pair
#print axioms xstat_mem_take_pos
#print axioms xstat_posOf_upCards
#print axioms xstat_mem_found_rank_lt
#print axioms cross_orphan_seat
#print axioms cross_orphan_kill
