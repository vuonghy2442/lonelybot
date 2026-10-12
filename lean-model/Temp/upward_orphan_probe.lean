import Orig.OrphanSeat

/-!
# Temp/upward_orphan_probe — THE BACKWARD-ORPHAN READ OF THE CROSSING DOOR

The exploration probe for the upward axis's circumvention: the whole
crossing-door complex (hop chain, freeze, census debts, oscillation
ledger) is bypassed by running the orphan-seat residue BACKWARD off
the door state.  (The residue itself is the hoisted
`Orig/OrphanSeat.lean` head, consumed here directly; the
PairConfine-level low row is restated as the named seam `probe_plow`
with its exact in-tree statement — `Orig/PairConfine.lean`'s proved
`pair_lowFamily_founded` — while the live rebuilds are in flight.)

THE ARGUMENT (all steps proved below except the three named seams):

1. THE DOOR EXCLUSION — at the door state `u` the elevated member is
   FOUNDED (its suit's rung walked past the fork rank) and the firing
   member is a bare pile TOP (its own step guard), so the fork's
   twin-cover `d` — whose only legal below-cards are the two pair
   members — cannot sit face-up anywhere at `u`.
2. THE ZONE CLOSURE — not face-up, not hidden (hidden lists are pinned
   along witness journeys), not stocked/wasted (the union never gains)
   ⇒ `d` FOUNDED at `u` ⇒ `rung_u(d.suit) ≥ r`.
3. THE ORPHAN — `e := (d.suit, r − 2)` is founded at `u` (the rung is
   past `r`) yet EXILED at the fork (the cover pin reads its rung at
   most `r − 2` there) — and the door state rides the same class, so
   a witness journey BACK to the fork exists.
4. THE SEAT RESIDUE (backward) — `cross_orphan_seat` seats `e` face-up
   at the FORK on a fitting below-neighbor `b₂` of the first fork's
   family one below its rank — and the fork saturates every such card
   into its foundations.  Face-up and founded cannot coexist.

SEAMS (the only sorries — each with its route in the docstring):
`probe_union` (the stock/waste union never gains along a play),
`probe_roam` (a seated non-king card keeps a fitting below-neighbor),
`probe_topclash` (a firing card's bare top and a sitter above it
contradict).  Everything else is proved from banked public rows and
per-file copies.
-/

/-! ## §0. The per-file kit (paste copies; every proof banked-green elsewhere) -/

/-- The rank of a given index (the 13-cell enumeration; the exfalso
keeps `omega` off non-arithmetic goals, staying `Classical.choice`-free). -/
private theorem p_rank_of_idx {n : Nat} (hn : n < 13) :
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
                          | succ mm => exfalso; omega

/-- Two colors that both differ from a third agree. -/
private theorem p_color_pair {a u v : Color} (h1 : a ≠ u) (h2 : a ≠ v) :
    u = v := by
  rcases a <;> rcases u <;> rcases v <;> simp_all

/-- **THE DECK CENSUS** — the cards of one rank and one color are
exactly the twin pair. -/
private theorem p_rankColor_pair {c z : Card}
    (hr : z.rank.toIdx = c.rank.toIdx) (hc : z.suit.color = c.suit.color) :
    z = c ∨ z = c.twin := by
  rcases z with ⟨zs, zr⟩
  rcases c with ⟨cs, cr⟩
  have hrank : zr = cr := Rank.toIdx_inj hr
  subst hrank
  cases cs <;> cases zs <;> simp_all [Suit.color, Suit.twin, Card.twin]

/-- An element at position `i` belongs to the first `n` entries when
`i < n` (the copy of `Orig/PairConfine.lean`'s private row). -/
private theorem p_get_in_take : ∀ {α : Type} (l : List α) (n i : Nat)
    (hl : i < l.length) (hn : i < n), l.get ⟨i, hl⟩ ∈ l.take n := by
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

/-- Membership in a bounded take bounds the position (the copy of the
take-position kit). -/
private def p_posOf {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: t => if y = x then 0 else p_posOf x t + 1

private theorem p_mem_take_pos {α : Type} [DecidableEq α] :
    ∀ (n : Nat) (l : List α) (x : α), x ∈ l.take n → p_posOf x l < n := by
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
          · have hp : p_posOf x (y :: t) = 0 := by
              show (if y = x then 0 else p_posOf x t + 1) = 0
              rw [if_pos hyx]
            omega
          · have hp : p_posOf x (y :: t) = p_posOf x t + 1 := by
              show (if y = x then 0 else p_posOf x t + 1) = _
              rw [if_neg hyx]
            have hmem' : x ∈ t.take n := by
              rcases List.mem_cons.1 hmem with he | hrest
              · exact absurd he.symm hyx
              · exact hrest
            have hlt := ih t x hmem'
            omega

/-- Membership in a take is membership in the list. -/
private theorem p_take_sub {α : Type} : ∀ (n : Nat) (l : List α) (x : α),
    x ∈ l.take n → x ∈ l := by
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
          rcases List.mem_cons.1 hmem with rfl | hrest
          · exact List.mem_cons.2 (Or.inl rfl)
          · exact List.mem_cons.2 (Or.inr (ih t x hrest))

/-- A card sits at its own build index in its suit's foundation order. -/
private theorem p_upCards_get (z : Card)
    (h : z.rank.toIdx < z.suit.upCards.length) :
    z.suit.upCards.get ⟨z.rank.toIdx, h⟩ = z := by
  rcases z with ⟨zs, zr⟩
  cases zr <;> rfl

private theorem p_posOf_upCards (σ : Suit) (r : Rank) :
    p_posOf (Card.mk σ r) (Suit.upCards σ) = r.toIdx := by
  cases σ <;> cases r <;> rfl

/-- **THE FOUNDED-BRIDGE** — a suit rung strictly above a card's rank
index has already founded it. -/
private theorem p_mem_found_of_rung {st : State} (hwf : st.WF) {c : Card}
    (hlt : c.rank.toIdx < rungAt st c.suit) : c ∈ st.found c.suit := by
  have hpre := rung_found_prefix st hwf c.suit
  have h13 : c.suit.upCards.length = 13 := Suit.upCards_length c.suit
  have hget : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ = c :=
    p_upCards_get c (by rw [h13]; exact Rank.toIdx_lt c.rank)
  have hmem0 : c.suit.upCards.get ⟨c.rank.toIdx, by
      rw [h13]; exact Rank.toIdx_lt c.rank⟩ ∈
      c.suit.upCards.take (rungAt st c.suit) :=
    p_get_in_take _ _ _ (show c.rank.toIdx < c.suit.upCards.length by
      rw [h13]; exact Rank.toIdx_lt c.rank) hlt
  rw [hget] at hmem0
  have hmem : c ∈ c.suit.upCards.take (rungAt st c.suit) := hmem0
  rwa [← hpre] at hmem

/-- **THE FOUNDED-MEMBERSHIP BRIDGE** — a founded card sits strictly
below its suit's current rung. -/
private theorem p_mem_found_rank_lt {st : State} (hwf : st.WF) {d : Card}
    (hmem : d ∈ st.found d.suit) :
    d.rank.toIdx < rungAt st d.suit := by
  rcases d with ⟨s, r⟩
  have hmem' : Card.mk s r ∈ st.found s := hmem
  have hpre := rung_found_prefix st hwf s
  rw [hpre] at hmem'
  have hpos : p_posOf (Card.mk s r) (Suit.upCards s) < rungAt st s :=
    p_mem_take_pos _ _ _ hmem'
  have hidx := p_posOf_upCards s r
  show r.toIdx < rungAt st s
  omega

/-- The five-zone census: at any WF state every card sits in a zone
(the copy of `Orig/PairConfine.lean`'s private row). -/
private theorem p_zone_residency (st : State) (hwf : st.WF) (d : Card) :
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

/-! ## §1. The four named seams -/

/-- **SEAM 0b — THE γ-FAMILY LOW ROW**, restated with its exact
in-tree signature (`Orig/PairConfine.lean`'s PROVED
`pair_lowFamily_founded`): every same-family card of rank index
strictly below a fork's is already founded there. -/
theorem probe_plow {st : State} (hwf : st.WF) {x : Card}
    (hx : ForkWitness st x) {c : Card}
    (hcol : c.suit.color = x.suit.color)
    (hlt : c.rank.toIdx < x.rank.toIdx) :
    c ∈ st.found c.suit := by
  sorry

/-- **SEAM 1 — THE UNION NEVER GAINS**: along a witness play the
stock/waste world keeps to itself (draws permute it internally via
`draw_unfold` + the `dealUpTo` membership rows; the waste legs only
shrink it and never ride witness journeys; tab/found/cargo legs never
write the zone). -/
theorem probe_union {st u : State} {τ : List Move}
    (hτ : ShufflePlayW st τ u) {d : Card}
    (h : d ∈ u.stock ∨ d ∈ u.waste) : d ∈ st.stock ∨ d ∈ st.waste := by
  sorry

/-- **SEAM 2 — THE ROAMING SEAT**: a non-king card that starts the
journey SEATED on a fitting face-up below-neighbor is, at the end,
either nowhere face-up or still seated on a fitting face-up
below-neighbor.  ROUTE: the seat residue's own below-identity
induction in the roam form — founding spells are vacuous, every
re-landing of a non-king reseeds on a face-up top (`canPlace` inr),
cargo keeps the run-internal below-neighbor, and no card ever departs
from under another (face-up lists change only by suffix chops and
appends), so the below-card never becomes hidden. -/
theorem probe_roam {st u : State} (hwf : st.WF) {τ : List Move}
    (hτ : ShufflePlayW st τ u) {d : Card} (hnk : d.rank ≠ Rank.king)
    (hseed : ∃ a bs z, (st.piles a).faceUp = bs ++ [z, d] ∧
      canSitOn d z = true) :
    (∃ a L z R, (u.piles a).faceUp = L ++ z :: d :: R ∧
      canSitOn d z = true) ∨
      (∀ a, d ∉ (u.piles a).faceUp) := by
  sorry

/-- **SEAM 3 — THE TOP CLASH**: a pile TOP cannot have a card seated
directly above it.  ROUTE: `State.pileOfTop_eq_some_iff` +
`Pile.top_eq_lastOf_iff` read the top's pile as `front ++ [z]`; the
seating list `L ++ z :: d :: R` puts cards after `z` (at least `d`),
contradicting the last-element read via the `lastOf` append rows, the
`R ≠ []` arm closing by `runOK_nodup` double-membership. -/
theorem probe_topclash {u : State} (hwfu : u.WF) {z d : Card}
    (hpo : ∃ Q, u.pileOfTop z = some Q)
    (hpkg : ∃ a L R, (u.piles a).faceUp = L ++ z :: d :: R) :
    False := by
  sorry

/-! ## §2. The assembly -/

/-- **THE BACKWARD-ORPHAN KILL OF THE CROSSING DOOR** — the full
upward-door circumvention, proved modulo the three seams above and
`Orig.CrossFamilyStatic.lean`'s orphan-seat residue.  The door package
is exactly the banked `crossing_door_exists` output shape; `hdcover` is
the fork's `pair_cover_pins` twin-cover package; `hback` is the
class-return journey from the door state to the fork. -/
theorem upward_orphan_kill {st u s₁ : State} (hwf : st.WF) (hwfu : u.WF)
    {π ρ : List Move}
    (hjourney : ShufflePlayW st π u) (hback : ShufflePlayW u ρ st)
    {x d m m' : Card}
    (hx : ForkWitness st x)
    (hpair : (m = x ∧ m' = x.twin) ∨ (m = x.twin ∧ m' = x))
    (hfire : State.step u (Move.tabToFound m') = some s₁)
    (helev : rungAt u m.suit > x.rank.toIdx)
    (hdcover : ∃ a bs, (st.piles a).faceUp = bs ++ [x.twin, d] ∧
      canSitOn d x.twin = true)
    (hdcol : d.suit.color ≠ x.suit.color)
    (hdnext : st.nextUp d = false)
    (hdpin : rungAt st d.suit + 1 ≤ x.rank.toIdx) :
    False := by
  obtain ⟨A, bsA, hshape, hfit⟩ := hdcover
  obtain ⟨hdrankT, hdcolT⟩ := (canSitOn_eq d x.twin).mp hfit
  rw [Card.twin_rank] at hdrankT
  -- d's color is off the fork family (via the twin's color copy)
  have hxtc : x.twin.suit.color = x.suit.color := by
    rw [Card.twin_suit, Suit.color_twin]
  rw [hxtc] at hdcolT
  -- d is face-up at the fork
  have hdmemST : d ∈ (st.piles A).faceUp := by
    rw [hshape]
    exact List.mem_append.2 (Or.inr (List.mem_cons.2
      (Or.inr (List.mem_cons.2 (Or.inl rfl)))))
  -- d is never a king (its rank index +1 = the fork index ≤ 12)
  have hdred := Rank.toIdx_lt x.rank
  have hdnk : d.rank ≠ Rank.king := by
    intro hcon
    have hk12 : Rank.king.toIdx = 12 := rfl
    rw [hcon] at hdrankT
    omega
  -- the deep st pin: the cover suit's rung reads at most r − 2
  -- the rung/foundHeight defeq bridge
  have hbridge : rungAt st d.suit = st.foundHeight d.suit := rfl
  have hneR : d.rank.toIdx ≠ rungAt st d.suit := by
    intro hc0
    have htrue : st.nextUp d = true := by
      show decide (d.rank.toIdx = st.foundHeight d.suit) = true
      rw [hc0, hbridge]
      exact decide_eq_true rfl
    rw [htrue] at hdnext
    simp at hdnext
  have hdeepst : rungAt st d.suit + 2 ≤ x.rank.toIdx := by omega
  -- THE HIDDEN BAR (shared): hidden lists pinned along the journey
  have hnothid : ∀ k, d ∉ (u.piles k).hidden := by
    intro k hcon
    have hp := shuffle_hiddenPinned hjourney k
    rw [hp] at hcon
    by_cases hk : k = A
    · rw [hk] at hcon
      exact (mem_faceUp_only hwf hdmemST).2.1 hcon
    · exact ((mem_faceUp_only hwf hdmemST).1 k hk).1 hcon
  -- The two door orders are symmetric; each block is self-contained.
  rcases hpair with ⟨hm, hm'⟩ | ⟨hm, hm'⟩
  · have hms : x = m := hm.symm
    subst hms
    have hms' : x.twin = m' := hm'.symm
    subst hms'
    -- the elevated member x is founded at u
    have hmFound : x ∈ u.found x.suit :=
      p_mem_found_of_rung hwfu (by omega)
    rcases probe_roam hwf hjourney hdnk ⟨A, bsA, x.twin, hshape, hfit⟩ with
      ⟨a₂, L, b, R, hpkg, hbfit⟩ | haway
    · -- THE SEATED KILL: the roam gives d a fitting below at u
      obtain ⟨hbr, hbc⟩ := (canSitOn_eq d b).mp hbfit
      have hbx : b.suit.color = x.suit.color := p_color_pair hbc hdcolT
      have hbCell : b = x ∨ b = x.twin := p_rankColor_pair (by omega) hbx
      have hbmem : b ∈ (u.piles a₂).faceUp := by
        rw [hpkg]
        exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      rcases hbCell with hb1 | hb1
      · -- b = x: the elevated member is founded, not face-up
        have hxmem : x ∈ (u.piles a₂).faceUp := hb1 ▸ hbmem
        exact ((mem_found_unique hwfu hmFound).1 a₂).2 hxmem
      · -- b = x.twin: the FIRING card — its own guard bars sitters
        subst hb1
        obtain ⟨-, Q, hpoQ, -⟩ := step_tabToFound_inv hfire
        exact probe_topclash hwfu ⟨Q, hpoQ⟩ ⟨a₂, L, R, hpkg⟩
    · -- THE AWAY KILL: the zone census forces d founded at u
      rcases p_zone_residency u hwfu d with ⟨s, hdFu⟩ | ⟨k, hh⟩ |
        ⟨k, hfa⟩ | hstock | hwaste
      · -- founded in suit s: the prefix read identifies s = d.suit
        have hsub := rung_found_prefix u hwfu s
        have htake : d ∈ s.upCards.take (rungAt u s) := by
          rw [← hsub]
          exact hdFu
        have hdlist : d ∈ s.upCards := p_take_sub _ _ _ htake
        have hsuit : s = d.suit := by
          rcases d with ⟨ds, dr⟩
          obtain ⟨r', -, hEq⟩ := List.mem_map.mp hdlist
          injection hEq with h1 _
        have hdF2 : d ∈ u.found d.suit := hsuit ▸ hdFu
        -- the rung read: d founded ⇒ its index below the rung
        have hRungUp : d.rank.toIdx < rungAt u d.suit :=
          p_mem_found_rank_lt hwfu hdF2
        -- the orphan card e := (d.suit, r − 2) exists and is no king
        have hx13 := Rank.toIdx_lt x.rank
        have heidx : x.rank.toIdx - 2 < 13 := by omega
        obtain ⟨rk, hrk⟩ := p_rank_of_idx heidx
        have hefound : rk.toIdx + 2 = x.rank.toIdx := by omega
        -- e is founded at u (the rung is past r ≥ rk + 2)
        have heF : Card.mk d.suit rk ∈ u.found d.suit := by
          refine p_mem_found_of_rung hwfu ?_
          show rk.toIdx < rungAt u d.suit
          omega
        -- e is exiled at the fork (the deep pin)
        have heN : Card.mk d.suit rk ∉ st.found d.suit := by
          intro hcon
          have hlt := p_mem_found_rank_lt hwf hcon
          have hlt2 : rk.toIdx < rungAt st d.suit :=
            show rk.toIdx < rungAt st d.suit from hlt
          omega
        -- THE SEAT RESIDUE, BACKWARD: u ⇒ st
        obtain ⟨P, b₂, hemem2, hb₂mem, hfit2⟩ :=
          cross_orphan_seat hwfu hback (e := Card.mk d.suit rk)
            (by
              show (Card.mk d.suit rk).rank ≠ Rank.king
              intro hcon
              have hc2 : rk = Rank.king := hcon
              rw [hc2] at hrk
              have hk12 : Rank.king.toIdx = 12 := rfl
              omega) heF heN
        -- the conclusion-kill at the FORK
        obtain ⟨hbr2, hbc2⟩ :=
          (canSitOn_eq (Card.mk d.suit rk) b₂).mp hfit2
        have hbr3 : rk.toIdx + 1 = b₂.rank.toIdx :=
          show rk.toIdx + 1 = b₂.rank.toIdx from hbr2
        have hbx2 : b₂.suit.color = x.suit.color :=
          p_color_pair hbc2 hdcolT
        have hb₂F : b₂ ∈ st.found b₂.suit :=
          probe_plow hwf hx hbx2 (by omega)
        exact (mem_faceUp_only hwf hb₂mem).2.2.2.2 b₂.suit hb₂F
      · exact hnothid k hh
      · exact haway k hfa
      · rcases probe_union hjourney (Or.inl hstock) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS
      · rcases probe_union hjourney (Or.inr hwaste) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS
  · have hms : x.twin = m := hm.symm
    subst hms
    have hms' : x = m' := hm'.symm
    subst hms'
    -- the elevated member x.twin is founded at u
    have htwinr : x.twin.rank.toIdx = x.rank.toIdx :=
      congrArg Rank.toIdx (Card.twin_rank x)
    have hmFound : x.twin ∈ u.found x.twin.suit :=
      p_mem_found_of_rung hwfu (by omega)
    rcases probe_roam hwf hjourney hdnk ⟨A, bsA, x.twin, hshape, hfit⟩ with
      ⟨a₂, L, b, R, hpkg, hbfit⟩ | haway
    · obtain ⟨hbr, hbc⟩ := (canSitOn_eq d b).mp hbfit
      have hbx : b.suit.color = x.suit.color := p_color_pair hbc hdcolT
      have hbCell : b = x ∨ b = x.twin := p_rankColor_pair (by omega) hbx
      have hbmem : b ∈ (u.piles a₂).faceUp := by
        rw [hpkg]
        exact List.mem_append.2 (Or.inr (List.mem_cons.2 (Or.inl rfl)))
      rcases hbCell with hb1 | hb1
      · -- b = x: the FIRING card — its own guard bars sitters
        subst hb1
        obtain ⟨-, Q, hpoQ, -⟩ := step_tabToFound_inv hfire
        exact probe_topclash hwfu ⟨Q, hpoQ⟩ ⟨a₂, L, R, hpkg⟩
      · -- b = x.twin: the elevated member is founded, not face-up
        have hxmem : x.twin ∈ (u.piles a₂).faceUp := hb1 ▸ hbmem
        exact ((mem_found_unique hwfu hmFound).1 a₂).2 hxmem
    · rcases p_zone_residency u hwfu d with ⟨s, hdFu⟩ | ⟨k, hh⟩ |
        ⟨k, hfa⟩ | hstock | hwaste
      · have hsub := rung_found_prefix u hwfu s
        have htake : d ∈ s.upCards.take (rungAt u s) := by
          rw [← hsub]
          exact hdFu
        have hdlist : d ∈ s.upCards := p_take_sub _ _ _ htake
        have hsuit : s = d.suit := by
          rcases d with ⟨ds, dr⟩
          obtain ⟨r', -, hEq⟩ := List.mem_map.mp hdlist
          injection hEq with h1 _
        have hdF2 : d ∈ u.found d.suit := hsuit ▸ hdFu
        have hRungUp : d.rank.toIdx < rungAt u d.suit :=
          p_mem_found_rank_lt hwfu hdF2
        have hx13 := Rank.toIdx_lt x.rank
        have heidx : x.rank.toIdx - 2 < 13 := by omega
        obtain ⟨rk, hrk⟩ := p_rank_of_idx heidx
        have hefound : rk.toIdx + 2 = x.rank.toIdx := by omega
        have heF : Card.mk d.suit rk ∈ u.found d.suit := by
          refine p_mem_found_of_rung hwfu ?_
          show rk.toIdx < rungAt u d.suit
          omega
        have heN : Card.mk d.suit rk ∉ st.found d.suit := by
          intro hcon
          have hlt := p_mem_found_rank_lt hwf hcon
          have hlt2 : rk.toIdx < rungAt st d.suit :=
            show rk.toIdx < rungAt st d.suit from hlt
          omega
        obtain ⟨P, b₂, hemem2, hb₂mem, hfit2⟩ :=
          cross_orphan_seat hwfu hback (e := Card.mk d.suit rk)
            (by
              show (Card.mk d.suit rk).rank ≠ Rank.king
              intro hcon
              have hc2 : rk = Rank.king := hcon
              rw [hc2] at hrk
              have hk12 : Rank.king.toIdx = 12 := rfl
              omega) heF heN
        obtain ⟨hbr2, hbc2⟩ :=
          (canSitOn_eq (Card.mk d.suit rk) b₂).mp hfit2
        have hbr3 : rk.toIdx + 1 = b₂.rank.toIdx :=
          show rk.toIdx + 1 = b₂.rank.toIdx from hbr2
        have hbx2 : b₂.suit.color = x.suit.color :=
          p_color_pair hbc2 hdcolT
        have hb₂F : b₂ ∈ st.found b₂.suit :=
          probe_plow hwf hx hbx2 (by omega)
        exact (mem_faceUp_only hwf hb₂mem).2.2.2.2 b₂.suit hb₂F
      · exact hnothid k hh
      · exact haway k hfa
      · rcases probe_union hjourney (Or.inl hstock) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS
      · rcases probe_union hjourney (Or.inr hwaste) with hS | hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.1 hS
        · exact (mem_faceUp_only hwf hdmemST).2.2.2.1 hS

/-! ## The audit battery -/

#print axioms p_rank_of_idx
#print axioms p_color_pair
#print axioms p_rankColor_pair
#print axioms p_mem_found_of_rung
#print axioms p_mem_found_rank_lt
#print axioms p_zone_residency
#print axioms probe_union
#print axioms probe_roam
#print axioms probe_topclash
#print axioms upward_orphan_kill
