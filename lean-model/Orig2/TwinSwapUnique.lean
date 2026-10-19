import Orig2.TwinRelabel
import Orig2.Integrity
import Orig2.Chart

/-!
# Orig2.TwinSwapUnique — the WF strict twin swap target is the relabeling

THE HEADLINE: at a `WF` state `s` whose twins `x` and `x.twin` both sit
face up on the tableau, are rider-free, and whose strict twin-swap
target `v` is itself `WF`, the target is exactly the relabeling state
`State.relabelTwin x s`.  This is the missing bridge from the
existential strict letter (`SwappableIn`) to the relabeling swap
(`sameOrbitSetoid.r s (State.relabelTwin x s)`).

THE `v.WF` GATE IS NECESSARY (and is the only repair needed): the
strict letter fixes only the seat readout and the non-face-up zones.
It does not fix the face-up *contents*.  If `c` is any face-up bottom
card with `c ≠ x` and `c ≠ x.twin`, appending one more copy of `c` to
`c`'s face-up run leaves `pileHolding c` unchanged and leaves
`below c` empty, hence leaves every `seatOf` readout unchanged — all
the strict-letter clauses still hold (start from the relabeling state
and append the duplicate) — but the resulting state is not the
relabeling.  The added duplicate is exactly a card-count failure, so
`v.WF` (or the weaker `∀ c, v.cardCount c = 1`) rules it out.  The
`_counts` row below is the minimal-gate form.

The proof rides the chart round trip: `v` and the relabeling state `w`
agree on every seat, the hidden decks, the foundations, the pool, the
cut, and the draw quantum; occurrence uniqueness then pins `v = w`.
The relabeling side's occurrence uniqueness is transported by the
private count kit (`cardCount_relabel`).

House compliance: new file only; zero `sorry`; zero
`Classical.choice`.
-/

/-! ## §1. The count kit for the relabeling -/

/-- The transposition is injective (it is an involution). -/
private theorem card_relabelTwin_injective (x : Card) :
    Function.Injective (Card.relabelTwin x) := by
  intro a b h
  have := congrArg (Card.relabelTwin x) h
  simpa [card_relabelTwin_involutive] using this

/-- A list off the pair is fixed by the transposition. -/
private theorem map_relabel_eq_self {x : Card} :
    ∀ {l : List Card}, x ∉ l → x.twin ∉ l →
      l.map (Card.relabelTwin x) = l
  | [], _, _ => rfl
  | c :: t, hx, ht => by
      have hcx : c ≠ x := fun h => hx (h ▸ List.mem_cons_self)
      have hct : c ≠ x.twin := fun h => ht (h ▸ List.mem_cons_self)
      rw [List.map_cons, card_relabelTwin_ne hcx hct]
      rw [map_relabel_eq_self (x := x)
        (fun hm => hx (List.mem_cons_of_mem c hm))
        (fun hm => ht (List.mem_cons_of_mem c hm))]

/-- The zones list is mapped by the transposition. -/
private theorem zones_relabel (x : Card) (st : State) :
    (State.relabelTwin x st).zones =
      st.zones.map (List.map (Card.relabelTwin x)) := by
  simp only [State.zones, State.relabelTwin, List.map_map, List.map_append,
    List.map_cons, List.map_nil, Function.comp_def]

/-- Flattening commutes with mapping a list of lists. -/
private theorem flatMap_map_id_relabel (x : Card) :
    ∀ zs : List (List Card),
      (zs.map (List.map (Card.relabelTwin x))).flatMap id =
        (zs.flatMap id).map (Card.relabelTwin x)
  | [] => rfl
  | z :: zs => by
      simp only [List.map_cons, List.flatMap_cons]
      rw [flatMap_map_id_relabel x zs, List.map_append]
      rfl

/-- Filtering a mapped list by a mapped value. -/
private theorem filter_map_relabel (x c : Card) :
    ∀ l : List Card,
      ((l.map (Card.relabelTwin x)).filter
          (fun y => decide (y = Card.relabelTwin x c))).length =
        (l.filter (fun y => decide (y = c))).length
  | [] => rfl
  | y :: t => by
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      by_cases hyc : y = c
      · have hτ : Card.relabelTwin x y = Card.relabelTwin x c := by rw [hyc]
        rw [decide_eq_true hyc, decide_eq_true hτ, ite_eq_left rfl,
          ite_eq_left rfl, List.length_cons, List.length_cons,
          filter_map_relabel x c t]
      · have hτ : Card.relabelTwin x y ≠ Card.relabelTwin x c :=
          fun h => hyc (card_relabelTwin_injective x h)
        rw [decide_eq_false hyc, decide_eq_false hτ]
        exact filter_map_relabel x c t

/-- The card count transports through the transposition. -/
private theorem cardCount_relabel (x : Card) (st : State) (c : Card) :
    (State.relabelTwin x st).cardCount (Card.relabelTwin x c) = st.cardCount c := by
  unfold State.cardCount
  rw [zones_relabel, flatMap_map_id_relabel, filter_map_relabel]

/-- A seated card is face up somewhere. -/
private theorem mem_faceUp_of_seat {st : State} {c : Card} {b : Base}
    (h : seatOf st c = some b) : ∃ a, c ∈ (st.piles a).faceUp := by
  unfold seatOf at h
  cases hh : st.pileHolding c with
  | none =>
      rw [hh] at h
      exact absurd h (by simp)
  | some a => exact ⟨a, pileHolding_mem hh⟩

/-- A face-up card is absent from every hidden deck, the stock, the
waste, and every foundation (occurrence uniqueness at `WF`). -/
private theorem off_zones_of_seat {st : State} (hwf : st.WF) {c : Card}
    (hse : ∃ b, seatOf st c = some b) :
    (∀ a, c ∉ (st.piles a).hidden) ∧ c ∉ st.stock ∧ c ∉ st.waste ∧
      ∀ s, c ∉ st.found s := by
  obtain ⟨b, hb⟩ := hse
  obtain ⟨a, hmem⟩ := mem_faceUp_of_seat hb
  obtain ⟨hother, hown, hstock, hwaste, hfound⟩ := mem_faceUp_only hwf hmem
  refine ⟨?_, hstock, hwaste, hfound⟩
  intro a'
  by_cases ha : a' = a
  · subst ha
    exact hown
  · exact (hother a' ha).1

/-! ## §2. The uniqueness row -/

/-- **THE MINIMAL-GATE FORM** — a strict twin-swap target whose card
census is still one-per-card is exactly the relabeling. -/
theorem eq_relabelTwin_of_twinPairSwapStrict_counts {s v : State} {x : Card}
    (hwf : s.WF)
    (hcntv : ∀ c, v.cardCount c = 1)
    (hx : ∃ b, seatOf s x = some b)
    (hxt : ∃ b, seatOf s x.twin = some b)
    (hrx : ∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x))
    (hrt : ∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin))
    (h : twinPairSwapStrict s v x) :
    v = State.relabelTwin x s := by
  obtain ⟨hvx, hvt, hvother, hbf, hff, hstock, hwaste, _hcut⟩ := h
  obtain ⟨hxhid, hxst, hxwa, hxfo⟩ := off_zones_of_seat hwf hx
  obtain ⟨hxthid, hxtst, hxtwa, hxtfo⟩ := off_zones_of_seat hwf hxt
  let w : State := State.relabelTwin x s
  have hcw : ∀ c, w.cardCount c = 1 := by
    intro c
    have hc := cardCount_relabel x s (Card.relabelTwin x c)
    rw [card_relabelTwin_involutive] at hc
    rw [show w.cardCount c = (State.relabelTwin x s).cardCount c from rfl, hc]
    exact hwf.2.2.1 (Card.relabelTwin x c) (Card.mem_universe _)
  have hseat : ∀ y, seatOf v y = seatOf w y := by
    intro y
    by_cases hyx : y = x
    · rw [hyx, hvx, state_relabelTwin_seat_x hwf]
    · by_cases hyt : y = x.twin
      · rw [hyt, hvt, state_relabelTwin_seat_twin hwf]
      · rw [hvother y hyx hyt,
          show seatOf w y = seatOf s y from
            state_relabelTwin_seat_other hwf hyx hyt hrx hrt]
  have hwstock : w.stock = s.stock := by
    show (State.relabelTwin x s).stock = s.stock
    rw [state_relabelTwin_stock, map_relabel_eq_self hxst hxtst]
  have hwwaste : w.waste = s.waste := by
    show (State.relabelTwin x s).waste = s.waste
    rw [state_relabelTwin_waste, map_relabel_eq_self hxwa hxtwa]
  have hwhidden : ∀ a, (w.piles a).hidden = (s.piles a).hidden := by
    intro a
    show ((State.relabelTwin x s).piles a).hidden = (s.piles a).hidden
    rw [state_relabelTwin_piles_hidden, map_relabel_eq_self (hxhid a) (hxthid a)]
  have hwfound : ∀ su, w.found su = s.found su := by
    intro su
    show (State.relabelTwin x s).found su = s.found su
    rw [state_relabelTwin_found, map_relabel_eq_self (hxfo su) (hxtfo su)]
  have hwdraw : w.drawStep = s.drawStep := by
    show (State.relabelTwin x s).drawStep = s.drawStep
    rw [state_relabelTwin_drawStep]
  have hhidden : ∀ a, (v.piles a).hidden = (w.piles a).hidden := by
    intro a
    rw [← hbf.1 a, hwhidden a]
  have hds : v.drawStep = w.drawStep := by
    rw [← hbf.2, hwdraw]
  have hfound : foundsFixed v w := by
    intro su
    rw [← hff su, hwfound su]
  have hpool : drawPool v = drawPool w := by
    unfold drawPool
    rw [hwstock, hwwaste, ← hstock, ← hwaste]
  have hcut : cutOf v = cutOf w := by
    unfold cutOf
    rw [hwstock, ← hstock]
  exact chart_round_trip_core v w hcntv hcw
    ⟨hseat, ⟨hhidden, hds⟩, hfound, hpool, hcut⟩

/-- **THE HEADLINE (WF-gated)** — at a rider-free, both-seated `WF`
state, a `WF` strict twin-swap target is exactly the relabeling state.

NOTE: the `hwv : v.WF` hypothesis is necessary; the ungated statement
is false (see the file docstring for the duplicate-bottom-card
counterexample).  The minimal gate is `∀ c, v.cardCount c = 1`
(`eq_relabelTwin_of_twinPairSwapStrict_counts`). -/
theorem eq_relabelTwin_of_twinPairSwapStrict {s v : State} {x : Card}
    (hwf : s.WF)
    (hwv : v.WF)
    (hx : ∃ b, seatOf s x = some b)
    (hxt : ∃ b, seatOf s x.twin = some b)
    (hrx : ∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x))
    (hrt : ∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin))
    (h : twinPairSwapStrict s v x) :
    v = State.relabelTwin x s :=
  eq_relabelTwin_of_twinPairSwapStrict_counts hwf
    (fun c => hwv.2.2.1 c (Card.mem_universe c)) hx hxt hrx hrt h

/-! ## §3. The gate is necessary — a kernel-checked counterexample

The ungated statement is FALSE.  The witness below is a 52-card `WF`
state `s` with three singleton piles: `x = ♠Q`, `x.twin = ♣Q`, and a
third face-up card `c = ♦K`; the rest of the deck is the stock.  The
relabeling `w = State.relabelTwin x s` is a strict twin-swap target.
The state `v` is `w` with one extra copy of `c` appended to `c`'s
face-up run.  `c` is still the first occurrence in that run, so
`pileHolding c` and `below c` are unchanged; no other card's `below`
prefix changes, hence `seatOf v = seatOf w`.  Every other strict
letter field is likewise unchanged, so `twinPairSwapStrict s v x`
holds, while `v ≠ w` (`v`'s pile `p2` has two cards, `w`'s has one).
The failure is exactly the card-count clause of `WF`. -/

namespace TwinSwapCounter

def x : Card := ⟨Suit.spade, Rank.queen⟩

def c : Card := ⟨Suit.diamond, Rank.king⟩

def rest : List Card :=
  Card.universe.filter (fun z => z ≠ x ∧ z ≠ x.twin ∧ z ≠ c)

def s : State :=
  { found := fun _ => []
    piles := fun a => match a with
      | .p0 => { hidden := [], faceUp := [x] }
      | .p1 => { hidden := [], faceUp := [x.twin] }
      | .p2 => { hidden := [], faceUp := [c] }
      | _ => { hidden := [], faceUp := [] }
    stock := rest
    waste := []
    drawStep := 1 }

theorem s_wf : s.WF := by
  refine ⟨?_, ?_, ?_, by decide⟩
  · intro su
    exact ⟨0, rfl⟩
  · intro a
    cases a <;> decide
  · intro card _
    rcases card with ⟨su, r⟩
    cases su <;> cases r <;> decide

theorem s_hrx : ∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x) := by
  intro y _
  rcases y with ⟨su, r⟩
  cases su <;> cases r <;> decide

theorem s_hrt : ∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin) := by
  intro y _
  rcases y with ⟨su, r⟩
  cases su <;> cases r <;> decide

theorem s_hx : ∃ b, seatOf s x = some b := ⟨Sum.inl Anchor.p0, by decide⟩

theorem s_hxt : ∃ b, seatOf s x.twin = some b :=
  ⟨Sum.inl Anchor.p1, by decide⟩

def w : State := State.relabelTwin x s

def v : State :=
  { w with
    piles := fun a => if a = Anchor.p2 then
        ({ hidden := [], faceUp := [c, c] } : Pile)
      else w.piles a }

theorem seat_v_w : ∀ y, seatOf v y = seatOf w y := by
  intro y
  rcases y with ⟨su, r⟩
  cases su <;> cases r <;> decide

theorem strict : twinPairSwapStrict s v x := by
  have hw := twinPairSwapStrict_relabelTwin (st := s) (x := x)
    s_wf s_hx s_hxt s_hrx s_hrt
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hw
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [seat_v_w x]
    exact h1
  · rw [seat_v_w x.twin]
    exact h2
  · intro y hyx hyt
    rw [seat_v_w y]
    exact h3 y hyx hyt
  · refine ⟨?_, ?_⟩
    · intro a
      cases a <;> decide
    · decide
  · intro su
    cases su <;> decide
  · decide
  · decide
  · rw [show cutOf s = s.stock.length from rfl,
      show cutOf v = v.stock.length from rfl]
    decide

/-- The literal (un-gated) statement, with no `v.WF` and no card-count
hypothesis, is refuted at the concrete witness above. -/
theorem not_ungated :
    ¬ (∀ {s v : State} {x : Card},
        s.WF →
        (∃ b, seatOf s x = some b) →
        (∃ b, seatOf s x.twin = some b) →
        (∀ y, y ≠ x → seatOf s y ≠ some (Sum.inr x)) →
        (∀ y, y ≠ x.twin → seatOf s y ≠ some (Sum.inr x.twin)) →
        twinPairSwapStrict s v x →
        v = State.relabelTwin x s) := by
  intro H
  have hv := H s_wf s_hx s_hxt s_hrx s_hrt strict
  have hface := congrArg (fun st : State => (st.piles Anchor.p2).faceUp) hv
  exact absurd hface (by decide)

end TwinSwapCounter

/-! ## §4. Audit battery -/

#print axioms eq_relabelTwin_of_twinPairSwapStrict_counts
#print axioms eq_relabelTwin_of_twinPairSwapStrict
#print axioms TwinSwapCounter.not_ungated
