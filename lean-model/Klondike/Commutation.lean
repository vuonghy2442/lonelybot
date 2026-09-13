import Klondike.Move
import Klondike.Relabel

/-!
# The theorem farm, part 3: commutation

Split from `Klondike/Theorems.lean` (mechanical file split, proofs unchanged):
the blindness kit, the cursor-blindness API, the fine commutation kit, the
draw-commitment machinery, and `commute_of_disjoint_touch`.
-/

/-! ## 3. Commutation — C-IND and C13

Coarse layer: component-disjoint moves commute unconditionally (draw
and reveal are the clean instance — the engine's ~92% measured
draw·reveal landscape is an interleaving artifact, not game structure).
Fine layer: disjoint touch-sets — the "type-ball interaction lemma"
the ledger names as C13's premise.
-/

/-- The four state components. -/
inductive Component : Type where
  | tableau | foundations | hidden | stock
  deriving DecidableEq, Repr

/-- Which components a move reads/writes. -/
def Move.comps : Move → List Component
  | .draw => [.stock]
  | .reveal _ => [.tableau, .hidden]
  | .deckPile _ _ => [.stock, .tableau]
  | .deckStack _ => [.stock, .foundations]
  | .pileStack _ => [.tableau, .foundations]
  | .stackPile _ _ => [.tableau, .foundations]
  | .pilePile _ _ => [.tableau]

/-! ### The blindness kit — the commutation workhorse

A move's guards read only their own components, so replacing the fields
a move never reads preserves its outcome up to those fields: the
stock/heights-blind forms (reveal, pilePile — for the `draw` and
`deckStack` pairs), the board/depths-blind form (deckStack — for the
reveal/pilePile pairs), and the stock-blind none-forms (pileStack,
stackPile).  The `some`-forms carry the successor along with the
replaced fields. -/

theorem reveal_blind_some {st : State} {c : Card} {cy : Cycle Card} {hs : Suit → Nat}
    {s₁ : State} (h : st.apply (Move.reveal c) = some s₁) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c)
      = some { s₁ with stock := cy, heights := hs } := by
  rw [apply_reveal_iff] at h
  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := h
  rw [hst₁]
  rw [apply_reveal_iff]
  exact ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩

theorem reveal_blind_none {st : State} {c : Card} {cy : Cycle Card} {hs : Suit → Nat}
    (h : st.apply (Move.reveal c) = none) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c) = none := by
  cases hr : ({ st with stock := cy, heights := hs } : State).apply (Move.reveal c) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_reveal_iff] at hr
      obtain ⟨htop, r, a, bd, hbot, hpile, hatt, _⟩ := hr
      have hcontra : st.apply (Move.reveal c) = some { st with
          board := bd,
          depths := fun a' => if a' = a then st.depths a - 1 else st.depths a' } :=
        apply_reveal_iff.mpr ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem pilePile_blind_some {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    {hs : Suit → Nat} {s₁ : State} (h : st.apply (Move.pilePile c b) = some s₁) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.pilePile c b)
      = some { s₁ with stock := cy, heights := hs } := by
  rw [apply_pilePile_iff] at h
  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := h
  rw [hst₁]
  rw [apply_pilePile_iff]
  exact ⟨b₀, hb₀, hne, hcmr, bd, hatt, rfl⟩

theorem pilePile_blind_none {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    {hs : Suit → Nat} (h : st.apply (Move.pilePile c b) = none) :
    ({ st with stock := cy, heights := hs } : State).apply (Move.pilePile c b) = none := by
  cases hr : ({ st with stock := cy, heights := hs } : State).apply (Move.pilePile c b) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_pilePile_iff] at hr
      obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, _⟩ := hr
      have hcontra : st.apply (Move.pilePile c b) = some { st with board := bd } :=
        apply_pilePile_iff.mpr ⟨b₀, hb₀, hne, hcmr, bd, hatt, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem deckStack_blind_some {st : State} {c : Card} {bd : Board} {dpt : Anchor → Nat}
    {sd : State} (h : st.apply (Move.deckStack c) = some sd) :
    ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c)
      = some { sd with board := bd, depths := dpt } := by
  rw [apply_deckStack_iff] at h
  obtain ⟨hp, hrk, hsd⟩ := h
  rw [hsd]
  rw [apply_deckStack_iff]
  exact ⟨hp, hrk, rfl⟩

theorem deckStack_blind_none {st : State} {c : Card} {bd : Board} {dpt : Anchor → Nat}
    (h : st.apply (Move.deckStack c) = none) :
    ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c) = none := by
  cases hr : ({ st with board := bd, depths := dpt } : State).apply (Move.deckStack c) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_deckStack_iff] at hr
      obtain ⟨hp, hrk, _⟩ := hr
      have hcontra : st.apply (Move.deckStack c) = some { st with
          stock := st.stock.removeAt (st.stock.cursor - 1),
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :=
        apply_deckStack_iff.mpr ⟨hp, hrk, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem pileStack_blind_none {st : State} {c : Card} {cy : Cycle Card}
    (h : st.apply (Move.pileStack c) = none) :
    ({ st with stock := cy } : State).apply (Move.pileStack c) = none := by
  cases hr : ({ st with stock := cy } : State).apply (Move.pileStack c) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_pileStack_iff] at hr
      obtain ⟨htop, b, hb, hrk, _⟩ := hr
      have hcontra : st.apply (Move.pileStack c) = some { st with
          board := st.board.detach b,
          heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s } :=
        apply_pileStack_iff.mpr ⟨htop, b, hb, hrk, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

theorem stackPile_blind_none {st : State} {c : Card} {b : Base} {cy : Cycle Card}
    (h : st.apply (Move.stackPile c b) = none) :
    ({ st with stock := cy } : State).apply (Move.stackPile c b) = none := by
  cases hr : ({ st with stock := cy } : State).apply (Move.stackPile c b) with
  | none => rfl
  | some _ =>
      exfalso
      rw [apply_stackPile_iff] at hr
      obtain ⟨hrk, hcp, bd, hatt, _⟩ := hr
      have hcontra : st.apply (Move.stackPile c b) = some { st with
          board := bd,
          heights := fun s => if s = c.suit then st.heights s - 1 else st.heights s } :=
        apply_stackPile_iff.mpr ⟨hrk, hcp, bd, hatt, rfl⟩
      exact absurd hcontra (by rw [h]; simp)

/-- `pileStack`'s some-form, stock-only replacement: the guards read
only the board and heights (both untouched by a stock with-update), and
the successor carries the replaced stock along. -/
theorem pileStack_blind_some {st : State} {c : Card} {cy : Cycle Card} {st₁ : State}
    (h : st.apply (Move.pileStack c) = some st₁) :
    ({ st with stock := cy } : State).apply (Move.pileStack c)
      = some { st₁ with stock := cy } := by
  rw [apply_pileStack_iff] at h
  obtain ⟨htop, b, hb, hrk, hst⟩ := h
  rw [hst]
  rw [apply_pileStack_iff]
  exact ⟨htop, b, hb, hrk, rfl⟩

/-- `stackPile`'s some-form, stock-only replacement. -/
theorem stackPile_blind_some {st : State} {c : Card} {b : Base} {cy : Cycle Card} {st₁ : State}
    (h : st.apply (Move.stackPile c b) = some st₁) :
    ({ st with stock := cy } : State).apply (Move.stackPile c b)
      = some { st₁ with stock := cy } := by
  rw [apply_stackPile_iff] at h
  obtain ⟨hrk, hcp, bd, hatt, hst⟩ := h
  rw [hst]
  rw [apply_stackPile_iff]
  exact ⟨hrk, hcp, bd, hatt, rfl⟩

/-- The `draw` half of every draw-pair: the deal always succeeds, so
only the other move's stock-blindness remains — failure persists, and
success carries the successor with the deal's stock. -/
theorem draw_comm_gen (st : State) (m : Move)
    (hn : st.apply m = none →
      ({ st with stock := st.stock.dealOnce st.drawStep } : State).apply m = none)
    (hs : ∀ s₁, st.apply m = some s₁ →
      ({ st with stock := st.stock.dealOnce st.drawStep } : State).apply m
        = some { s₁ with stock := s₁.stock.dealOnce s₁.drawStep }) :
    (st.apply Move.draw >>= fun s => s.apply m) = (st.apply m >>= fun s => s.apply Move.draw) := by
  have hD : st.apply Move.draw = some { st with stock := st.stock.dealOnce st.drawStep } := rfl
  rw [hD]
  cases hm : st.apply m with
  | none => exact hn hm
  | some s₁ => exact hs s₁ hm

theorem draw_comm_reveal (st : State) (c : Card) :
    (st.apply Move.draw >>= fun s => s.apply (Move.reveal c)) =
    (st.apply (Move.reveal c) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.reveal c) ?_ ?_
  · exact reveal_blind_none
  · intro s₁ h
    rw [apply_reveal_iff] at h
    obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := h
    rw [hst₁]
    rw [apply_reveal_iff]
    exact ⟨htop, r, a, bd, hbot, hpile, hatt, rfl⟩

theorem draw_comm_pileStack (st : State) (c : Card) :
    (st.apply Move.draw >>= fun s => s.apply (Move.pileStack c)) =
    (st.apply (Move.pileStack c) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.pileStack c) ?_ ?_
  · exact pileStack_blind_none
  · intro s₁ h
    rw [apply_pileStack_iff] at h
    obtain ⟨htop, b, hb, hrk, hst₁⟩ := h
    rw [hst₁]
    rw [apply_pileStack_iff]
    exact ⟨htop, b, hb, hrk, rfl⟩

theorem draw_comm_stackPile (st : State) (c : Card) (b : Base) :
    (st.apply Move.draw >>= fun s => s.apply (Move.stackPile c b)) =
    (st.apply (Move.stackPile c b) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.stackPile c b) ?_ ?_
  · exact stackPile_blind_none
  · intro s₁ h
    rw [apply_stackPile_iff] at h
    obtain ⟨hrk, hcp, bd, hatt, hst₁⟩ := h
    rw [hst₁]
    rw [apply_stackPile_iff]
    exact ⟨hrk, hcp, bd, hatt, rfl⟩

theorem draw_comm_pilePile (st : State) (c : Card) (b : Base) :
    (st.apply Move.draw >>= fun s => s.apply (Move.pilePile c b)) =
    (st.apply (Move.pilePile c b) >>= fun s => s.apply Move.draw) := by
  refine draw_comm_gen st (Move.pilePile c b) ?_ ?_
  · exact pilePile_blind_none
  · intro s₁ h
    rw [apply_pilePile_iff] at h
    obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := h
    rw [hst₁]
    rw [apply_pilePile_iff]
    exact ⟨b₀, hb₀, hne, hcmr, bd, hatt, rfl⟩

/-- Each move's legality reads only its components, so neither order
sees the other's writes.  The 49 move pairs split into the 37 with
overlapping components (the hypothesis is absurd — any shared component
witnesses it) and the 12 genuinely disjoint ones (draw with the four
non-stock moves via `draw_comm_*`; reveal/deckStack and deckStack/pilePile
via the blindness kit — both orders land on the same fieldwise merge). -/
theorem commute_of_compsDisjoint (st : State) (m m' : Move)
    (h : ∀ x ∈ Move.comps m, x ∉ Move.comps m') :
    (st.apply m >>= fun s => s.apply m') = (st.apply m' >>= fun s => s.apply m) := by
  cases m with
  | draw =>
      cases m' with
      | draw => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | reveal c => exact draw_comm_reveal st c
      | deckPile _ _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack c => exact draw_comm_pileStack st c
      | stackPile c _ => exact draw_comm_stackPile st c _
      | pilePile c b => exact draw_comm_pilePile st c b
  | reveal c =>
      cases m' with
      | draw => exact (draw_comm_reveal st c).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack c' =>
          cases hr : st.apply (Move.reveal c) with
          | none =>
              cases hd : st.apply (Move.deckStack c') with
              | none => rfl
              | some sd =>
                  show none = sd.apply (Move.reveal c)
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact (reveal_blind_none hr).symm
          | some s₁ =>
              cases hd : st.apply (Move.deckStack c') with
              | none =>
                  show s₁.apply (Move.deckStack c') = none
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [hst₁]
                  exact deckStack_blind_none hd
              | some sd =>
                  show s₁.apply (Move.deckStack c') = sd.apply (Move.reveal c)
                  have hrw := hr
                  have hdw := hd
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  rw [deckStack_blind_some hdw, reveal_blind_some hrw]
                  rw [hst₁, hsd]
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | deckPile _ _ =>
      cases m' with
      | draw => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | deckStack c =>
      cases m' with
      | draw => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | reveal c' =>
          cases hd : st.apply (Move.deckStack c) with
          | none =>
              cases hr : st.apply (Move.reveal c') with
              | none => rfl
              | some s₁ =>
                  show none = s₁.apply (Move.deckStack c)
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [hst₁]
                  exact (deckStack_blind_none hd).symm
          | some sd =>
              cases hr : st.apply (Move.reveal c') with
              | none =>
                  show sd.apply (Move.reveal c') = none
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact reveal_blind_none hr
              | some s₁ =>
                  show sd.apply (Move.reveal c') = s₁.apply (Move.deckStack c)
                  have hrw := hr
                  have hdw := hd
                  rw [apply_reveal_iff] at hr
                  obtain ⟨htop, r, a, bd, hbot, hpile, hatt, hst₁⟩ := hr
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  rw [reveal_blind_some hrw, deckStack_blind_some hdw]
                  rw [hst₁, hsd]
      | deckPile _ _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.stock (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ =>
          exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile c' b =>
          cases hd : st.apply (Move.deckStack c) with
          | none =>
              cases hpp : st.apply (Move.pilePile c' b) with
              | none => rfl
              | some s₁ =>
                  show none = s₁.apply (Move.deckStack c)
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [hst₁]
                  exact (deckStack_blind_none hd).symm
          | some sd =>
              cases hpp : st.apply (Move.pilePile c' b) with
              | none =>
                  show sd.apply (Move.pilePile c' b) = none
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact pilePile_blind_none hpp
              | some s₁ =>
                  show sd.apply (Move.pilePile c' b) = s₁.apply (Move.deckStack c)
                  have hppw := hpp
                  have hdw := hd
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  rw [pilePile_blind_some hppw]
                  have hb1 : ({ st with board := bd } : State).apply (Move.deckStack c)
                      = some { sd with board := bd, depths := st.depths } :=
                    deckStack_blind_some hdw
                  rw [hb1]
                  rw [hst₁, hsd]
  | pileStack c =>
      cases m' with
      | draw => exact (draw_comm_pileStack st c).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | stackPile c b =>
      cases m' with
      | draw => exact (draw_comm_stackPile st c b).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack _ => exact (h Component.foundations (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
  | pilePile c b =>
      cases m' with
      | draw => exact (draw_comm_pilePile st c b).symm
      | reveal _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | deckStack c' =>
          cases hpp : st.apply (Move.pilePile c b) with
          | none =>
              cases hd : st.apply (Move.deckStack c') with
              | none => rfl
              | some sd =>
                  show none = sd.apply (Move.pilePile c b)
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hsd]
                  exact (pilePile_blind_none hpp).symm
          | some s₁ =>
              cases hd : st.apply (Move.deckStack c') with
              | none =>
                  show s₁.apply (Move.deckStack c') = none
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [hst₁]
                  exact deckStack_blind_none hd
              | some sd =>
                  show s₁.apply (Move.deckStack c') = sd.apply (Move.pilePile c b)
                  have hppw := hpp
                  have hdw := hd
                  rw [apply_pilePile_iff] at hpp
                  obtain ⟨b₀, hb₀, hne, hcmr, bd, hatt, hst₁⟩ := hpp
                  rw [apply_deckStack_iff] at hd
                  obtain ⟨hp, hrk, hsd⟩ := hd
                  rw [hst₁, hsd]
                  have hb1 : ({ st with board := bd } : State).apply (Move.deckStack c')
                      = some { sd with board := bd, depths := st.depths } :=
                    deckStack_blind_some hdw
                  rw [hb1]
                  rw [pilePile_blind_some hppw]
                  rw [hst₁, hsd]
      | pileStack _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | stackPile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim
      | pilePile _ _ => exact (h Component.tableau (by simp [Move.comps]) (by simp [Move.comps])).elim

/-- The C-IND clean sector: draw·reveal always commutes.
Instance of `commute_of_compsDisjoint`. -/
theorem reveal_draw_comm (st : State) (c : Card) :
    (st.apply (Move.reveal c) >>= fun s => s.apply Move.draw) =
    (st.apply Move.draw >>= fun s => s.apply (Move.reveal c)) := by
  refine commute_of_compsDisjoint st (Move.reveal c) Move.draw ?_
  intro x hx
  cases x with
  | tableau => simp [Move.comps]
  | foundations => simp [Move.comps] at hx
  | hidden => simp [Move.comps]
  | stock => simp [Move.comps] at hx

/-- The stock-*consuming* moves: the card draws (`deckPile`,
`deckStack`).  `.draw` — the pure deal that advances the cursor —
consumes nothing: the pace advance, not a card down. -/
def Move.consumesStock : Move → Bool
  | .deckPile _ _ => true
  | .deckStack _ => true
  | _ => false

/-- The deal commutes with every non-consuming move: `.draw`'s
component signature is `[.stock]` *alone* and its legality is
unconditional (dealing reads nothing), while the non-consuming moves —
reveal, the two shuffles, pilePile — never touch the stock.  The
generalization of `reveal_draw_comm` from reveal to the whole
non-consuming sector.  The consuming draws (deckPile, deckStack) are
the genuine exceptions: their legality reads the cursor (`maskPos`),
which the deal changes.

This is the canonical form behind the window lemma's replay — deals
float freely through a non-consuming prefix, so the cursor at the
first consumption is a pure function of the deal count — and behind
`solvableEngine_iff_macro`'s regrouping (A3: draws commute with
accommodations).

Route: `draw` composed with itself is the same term on both sides; the
four other non-consuming moves are the proven `draw_comm_*` instances;
the two card draws contradict `consumesStock = false`. -/
theorem deal_commutes_nonStock (st : State) (m : Move)
    (hc : m.consumesStock = false) :
    (st.apply m >>= fun s => s.apply Move.draw) =
    (st.apply Move.draw >>= fun s => s.apply m) := by
  cases m with
  | draw => rfl
  | reveal c => exact (draw_comm_reveal st c).symm
  | deckPile c b => exact absurd hc (by simp [Move.consumesStock])
  | deckStack c => exact absurd hc (by simp [Move.consumesStock])
  | pileStack c => exact (draw_comm_pileStack st c).symm
  | stackPile c b => exact (draw_comm_stackPile st c b).symm
  | pilePile c b => exact (draw_comm_pilePile st c b).symm

/-! ### The cursor-blindness API — the replay steps, named

Every pace lemma's route repeats the same three steps: non-consuming
moves replay verbatim from a cursor-differing state, and the draw
commitments' successors merge.  Named here so the routes cite them. -/

/-- Non-consuming moves are stock-blind: the result's stock is
bit-for-bit the source's.

STATEMENT REPAIR (2026-09-13, prover-confirmed witness
`Temp\opencode\StockInvarWitness.lean`): as originally staged (the
`consumesStock = false` guard alone) this is FALSE for `m = Move.draw` —
the deal is non-consuming (it advances the pace, not a card down) but
it *writes* the stock cursor: from cursor 0 with a nonempty stock and
step 1 the deal lands at cursor 1, so `st₁.stock ≠ st.stock`.  Minimal
repair: the `m ≠ Move.draw` hypothesis.  The four remaining arms
(reveal, the two shuffles, pilePile) are with-updates off the stock. -/
theorem apply_nonConsuming_stock_invar {st st₁ : State} {m : Move}
    (hc : m.consumesStock = false) (hm : m ≠ Move.draw) (h : st.apply m = some st₁) :
    st₁.stock = st.stock := by
  cases m with
  | draw => exact absurd rfl hm
  | reveal c =>
      rw [apply_reveal_iff] at h
      obtain ⟨-, r, a, bd, -, -, -, hst⟩ := h
      rw [hst]
  | deckPile c b => exact absurd hc (by simp [Move.consumesStock])
  | deckStack c => exact absurd hc (by simp [Move.consumesStock])
  | pileStack c =>
      rw [apply_pileStack_iff] at h
      obtain ⟨-, b, -, -, hst⟩ := h
      rw [hst]
  | stackPile c b =>
      rw [apply_stackPile_iff] at h
      obtain ⟨-, -, bd, -, hst⟩ := h
      rw [hst]
  | pilePile c b =>
      rw [apply_pilePile_iff] at h
      obtain ⟨-, -, -, -, bd, -, hst⟩ := h
      rw [hst]

/-- Non-consuming moves are cursor-blind in legality: from two states
differing only in the stock cursor, the same move applies, with results
again differing only in the cursor.  This is the "replay the prefix
verbatim" step of every pace lemma, named.

Route: `st'` *is* `st` with the stock field replaced (all other fields
agree, by `diffCursor`), so the blindness kit applies the move from the
stock/heights-replaced state and carries the replacement into the
successor; the draw arm goes through `dealOnce_cards` directly. -/
theorem apply_nonConsuming_cursor_blind {st st' st₁ : State} {m : Move}
    (hc : m.consumesStock = false) (hd : st.diffCursor st')
    (h : st.apply m = some st₁) :
    ∃ st₁' : State, st'.apply m = some st₁' ∧ st₁.diffCursor st₁' := by
  have hst'eq : { st with stock := st'.stock } = st' :=
    state_ext hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 rfl hd.2.2.2.2.2
  cases m with
  | draw =>
      rw [apply_draw_iff] at h
      have hs : st'.apply Move.draw
          = some { st' with stock := st'.stock.dealOnce st'.drawStep } := rfl
      refine ⟨{ st' with stock := st'.stock.dealOnce st'.drawStep }, hs, ?_⟩
      rw [h]
      refine ⟨hd.1, hd.2.1, hd.2.2.1, hd.2.2.2.1, ?_, hd.2.2.2.2.2⟩
      show (st.stock.dealOnce st.drawStep).cards
          = (st'.stock.dealOnce st'.drawStep).cards
      rw [Cycle.dealOnce_cards, Cycle.dealOnce_cards, hd.2.2.2.2.1]
  | reveal c =>
      have hblind := reveal_blind_some (cy := st'.stock) (hs := st.heights) h
      have hst'2 : { st with stock := st'.stock, heights := st.heights } = st' :=
        state_ext hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 rfl hd.2.2.2.2.2
      rw [hst'2] at hblind
      rw [apply_reveal_iff] at h
      obtain ⟨-, r, a, bd, -, -, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock, heights := st.heights }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩
  | deckPile c b => exact absurd hc (by simp [Move.consumesStock])
  | deckStack c => exact absurd hc (by simp [Move.consumesStock])
  | pileStack c =>
      have hblind := pileStack_blind_some (cy := st'.stock) h
      rw [hst'eq] at hblind
      rw [apply_pileStack_iff] at h
      obtain ⟨-, b, -, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩
  | stackPile c b =>
      have hblind := stackPile_blind_some (cy := st'.stock) h
      rw [hst'eq] at hblind
      rw [apply_stackPile_iff] at h
      obtain ⟨-, -, bd, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩
  | pilePile c b =>
      have hblind := pilePile_blind_some (cy := st'.stock) (hs := st.heights) h
      have hst'2 : { st with stock := st'.stock, heights := st.heights } = st' :=
        state_ext hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 rfl hd.2.2.2.2.2
      rw [hst'2] at hblind
      rw [apply_pilePile_iff] at h
      obtain ⟨-, -, -, -, bd, -, hst⟩ := h
      refine ⟨{ st₁ with stock := st'.stock, heights := st.heights }, hblind, ?_⟩
      rw [hst]
      exact ⟨rfl, rfl, rfl, rfl, hd.2.2.2.2.1, rfl⟩

/-- `posOf` runs the finder over the cards alone (the cursor is never
read) — the `diffCursor` stock transfer. -/
theorem posOf_cards_eq {c : Card} {cy cy' : Cycle Card}
    (h : cy.cards = cy'.cards) : cy.posOf c = cy'.posOf c := by
  show Cycle.findFirstIdx (fun c' => decide (c' = c)) cy.cards
     = Cycle.findFirstIdx (fun c' => decide (c' = c)) cy'.cards
  rw [h]

/-- **The merge, game level (tableau landing)**: from two
cursor-differing states, the same `Draw(c)` commitment to the same base
lands on the *identical* successor — the guard's position is
cards-determined (`posOf` never reads the cursor), the attach is
cursor-blind, and the stock successor `(drawTo i).removeAt i` is
position-determined (`removeAt_drawTo`).  The "successors merge" step
of every pace lemma, named. -/
theorem applyDrawTo_merge {st st' st₁ st₁' : State} {c : Card} {b : Base}
    (hd : st.diffCursor st')
    (h₁ : st.applyDrawTo c b = some st₁) (h₂ : st'.applyDrawTo c b = some st₁') :
    st₁ = st₁' := by
  obtain ⟨i, bd, hr₁, hatt₁, hst₁⟩ := applyDrawTo_shape h₁
  obtain ⟨i', bd', hr₂, hatt₂, hst₂⟩ := applyDrawTo_shape h₂
  have hpos : st.stock.posOf c = st'.stock.posOf c := posOf_cards_eq hd.2.2.2.2.1
  have hii : i = i' := by
    have e1 := State.reachablePos_posOf hr₁
    have e2 := State.reachablePos_posOf hr₂
    rw [hpos] at e1
    exact Option.some.inj (e1.symm.trans e2)
  subst hii
  have hbb : st'.board.attach b c = st.board.attach b c := by rw [hd.2.1]
  rw [hbb] at hatt₂
  have hbd : bd = bd' := Option.some.inj (hatt₁.symm.trans hatt₂)
  subst hbd
  rw [hst₁, hst₂]
  refine state_ext hd.1 ?_ hd.2.2.1 hd.2.2.2.1 ?_ hd.2.2.2.2.2
  · rfl
  · rw [hd.2.2.2.2.1]

/-- **The merge, game level (stack landing)**: as `applyDrawTo_merge`,
through `applyDrawStackTo` — the rank guard reads the heights (equal by
`diffCursor`), the splice is position-determined, the heights bump is
cursor-blind. -/
theorem applyDrawStackTo_merge {st st' st₁ st₁' : State} {c : Card}
    (hd : st.diffCursor st')
    (h₁ : st.applyDrawStackTo c = some st₁) (h₂ : st'.applyDrawStackTo c = some st₁') :
    st₁ = st₁' := by
  have hpos : st.stock.posOf c = st'.stock.posOf c := posOf_cards_eq hd.2.2.2.2.1
  simp only [State.applyDrawStackTo] at h₁ h₂
  cases hr₁ : st.reachablePos c with
  | none => rw [hr₁] at h₁; exact absurd h₁ (by simp)
  | some i =>
      rw [hr₁] at h₁
      cases hr₂ : st'.reachablePos c with
      | none => rw [hr₂] at h₂; exact absurd h₂ (by simp)
      | some i' =>
          rw [hr₂] at h₂
          have hii : i = i' := by
            have e1 := State.reachablePos_posOf hr₁
            have e2 := State.reachablePos_posOf hr₂
            rw [hpos] at e1
            exact Option.some.inj (e1.symm.trans e2)
          subst hii
          have h₁' : (if c.rank.toIdx = st.heights c.suit then
              some { st with
                stock := (st.stock.drawTo i).removeAt i,
                heights := fun s => if s = c.suit then st.heights s + 1 else st.heights s }
              else none) = some st₁ := h₁
          have h₂' : (if c.rank.toIdx = st'.heights c.suit then
              some { st' with
                stock := (st'.stock.drawTo i).removeAt i,
                heights := fun s => if s = c.suit then st'.heights s + 1 else st'.heights s }
              else none) = some st₁' := h₂
          by_cases hrk : c.rank.toIdx = st.heights c.suit
          · rw [if_pos hrk, Option.some.injEq] at h₁'
            rw [if_pos (hrk.trans (congrFun (hd.2.2.1) c.suit)), Option.some.injEq] at h₂'
            rw [← h₁', ← h₂']
            refine state_ext hd.1 hd.2.1 ?_ hd.2.2.2.1 ?_ hd.2.2.2.2.2
            · funext s
              by_cases hsc : s = c.suit
              · show (if s = c.suit then st.heights s + 1 else st.heights s)
                  = (if s = c.suit then st'.heights s + 1 else st'.heights s)
                rw [if_pos hsc, if_pos hsc]
                exact congrArg (· + 1) (congrFun (hd.2.2.1) s)
              · show (if s = c.suit then st.heights s + 1 else st.heights s)
                  = (if s = c.suit then st'.heights s + 1 else st'.heights s)
                rw [if_neg hsc, if_neg hsc]
                exact congrFun (hd.2.2.1) s
            · rw [Cycle.removeAt_drawTo i st.stock, Cycle.removeAt_drawTo i st'.stock,
                hd.2.2.2.2.1]
          · rw [if_neg hrk] at h₁'; exact absurd h₁' (by simp)

/-- The bases and cards a move reads or writes (state-dependent — the
run under a `pilePile`, the boundary under a `reveal`). -/
def Move.touch (st : State) : Move → List Base × List Card
  | .draw => ([], [])
  | .reveal c =>
      (match st.board.bottomOf c with
       | some (Sum.inr r) =>
           (match st.pileOfTopHidden r with
            | some a => [st.hiddenBase a]
            | none => [Sum.inr r], [c, r])
       | _ => ([], [c]))
  | .deckPile c b => ([b], [c])
  | .deckStack c => ([], [c])
  | .pileStack c => ((st.board.bottomOf c).toList, [c])
  | .stackPile c b => ([b], [c])
  | .pilePile c b => (b :: (st.board.bottomOf c).toList, c :: st.board.aboveOf c)

/-- Disjoint touch-sets (bases and cards). -/
def disjointTouch (t₁ t₂ : List Base × List Card) : Prop :=
  (∀ b ∈ t₁.1, b ∉ t₂.1) ∧ (∀ c ∈ t₁.2, c ∉ t₂.2)

/-! ### The fine-commutation kit

Board edits are single-base `topOf` updates (attach writes its base,
detach clears one), so edits at pairwise-distinct bases compose
order-independently (`attach_attach_comm`, and the attach/detach and
detach/detach forms below); a card's `bottomOf` survives every edit
that neither seats nor detaches it; the hidden-pile views
(`topHidden`, `pileOfTopHidden`, `hiddenBase`) read only the deal and
depths, so they are board/stock/heights-blind; and the heights
updates (`±1` at a suit) commute as function updates. -/

/-- Attach preserves another card's seat (the equality form; Macro's
`bottomOf_attach_of_ne` restated for the upstream file). -/
theorem bottomOf_attach_ne {bd : Board} {b : Base} {c x : Card} {bd' : Board}
    (hatt : bd.attach b c = some bd') (hne : x ≠ c) :
    bd'.bottomOf x = bd.bottomOf x := by
  have hfree : bd.topOf b = none := ((Board.attach_eq_some_iff bd b c).mp (by rw [hatt]; simp)).1
  have hself : bd'.topOf b = some c := Board.attach_topOf bd b c hatt
  show findFirst (fun β => decide (bd'.topOf β = some x)) Board.enumBase
     = findFirst (fun β => decide (bd.topOf β = some x)) Board.enumBase
  exact findFirst_congr (fun β => by
    by_cases hβ : β = b
    · subst hβ
      have hcx : c ≠ x := fun hh => hne hh.symm
      rw [hself, hfree]
      simp [hcx]
    · rw [Board.attach_topOf_ne bd b c hatt hβ]) Board.enumBase

/-- An attach and a detach at distinct bases commute (both orders'
attaches succeed — the commutation's own hypothesis shape). -/
theorem attach_detach_comm {bd : Board} {b b' : Base} {c : Card} {bd₁ bd₂ : Board}
    (hne : b ≠ b') (h₁ : bd.attach b c = some bd₁)
    (h₂ : (bd.detach b').attach b c = some bd₂) :
    bd₁.detach b' = bd₂ := by
  refine Board.ext_topOf (funext (fun x => ?_))
  by_cases hxb : x = b
  · rw [hxb, Board.detach_topOf_ne bd₁ b' b hne, Board.attach_topOf bd b c h₁,
      Board.attach_topOf (bd.detach b') b c h₂]
  · by_cases hxb' : x = b'
    · rw [hxb', Board.detach_topOf bd₁ b', Board.attach_topOf_ne (bd.detach b') b c h₂
          (Ne.symm hne), Board.detach_topOf bd b']
    · rw [Board.detach_topOf_ne bd₁ b' x hxb', Board.attach_topOf_ne bd b c h₁ hxb,
        Board.attach_topOf_ne (bd.detach b') b c h₂ hxb, Board.detach_topOf_ne bd b' x hxb']

/-- Two detaches at distinct bases commute. -/
theorem detach_detach_comm {bd : Board} {b b' : Base} (hne : b ≠ b') :
    (bd.detach b).detach b' = (bd.detach b').detach b := by
  refine Board.ext_topOf (funext (fun x => ?_))
  by_cases hxb : x = b
  · rw [hxb, Board.detach_topOf_ne (bd.detach b) b' b hne, Board.detach_topOf bd b,
      Board.detach_topOf (bd.detach b') b]
  · by_cases hxb' : x = b'
    · rw [hxb', Board.detach_topOf (bd.detach b) b',
        Board.detach_topOf_ne (bd.detach b') b b' (Ne.symm hne), Board.detach_topOf bd b']
    · rw [Board.detach_topOf_ne (bd.detach b) b' x hxb', Board.detach_topOf_ne bd b x hxb,
        Board.detach_topOf_ne (bd.detach b') b x hxb, Board.detach_topOf_ne bd b' x hxb']

/-- When the shorter take-slice's last differs from the longer's, the
longer slice ends `[…, r', r]` — reveal's redirect corner: the base
under the boundary is the slice the depth-step exposes. -/
theorem take_reverse_drop1 {l : List Card} {n : Nat} {r r' : Card}
    (hr : (l.take n).getLast? = some r) (hr' : (l.take (n-1)).getLast? = some r')
    (hne : r ≠ r') : ((l.take n).reverse.drop 1).head? = some r' := by
  have hn : 0 < n := by
    cases n with
    | zero => exact absurd hr (by simp)
    | succ m => omega
  have hsplit : l.take n = l.take (n-1) ++ (l.drop (n-1)).take 1 := by
    have h : l.take ((n-1) + 1) = l.take (n-1) ++ (l.drop (n-1)).take 1 := List.take_add
    have hn1 : (n-1) + 1 = n := by omega
    rw [hn1] at h
    exact h
  cases hdrop : (l.drop (n-1)) with
  | nil =>
      have h1 : (l.drop (n-1)).take 1 = ([] : List Card) := by rw [hdrop]; rfl
      rw [h1, List.append_nil] at hsplit
      rw [hsplit] at hr
      exact absurd (Option.some.inj (hr.symm.trans hr')) hne
  | cons d ds =>
      have h1 : (d :: ds).take 1 = [d] := rfl
      rw [hsplit, hdrop, h1, List.reverse_append, List.reverse_singleton, List.cons_append]
      show ((l.take (n-1)).reverse).head? = some r'
      rw [head?_reverse_eq_getLast?]
      exact hr'

/-- The hidden-pile views are blind to the board, stock, and heights:
two states agreeing on deal and depths have the same `topHidden`
pointwise (hence the same `pileOfTopHidden` and `hiddenBase`). -/
theorem topHidden_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (a : Anchor) :
    st.topHidden a = st'.topHidden a := by
  show ((st.deal.piles a).take (st.depths a)).getLast?
      = ((st'.deal.piles a).take (st'.depths a)).getLast?
  rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], hdpt]

theorem pileOfTopHidden_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (r : Card) :
    st.pileOfTopHidden r = st'.pileOfTopHidden r := by
  show findFirst (fun a => decide (st.topHidden a = some r)) Anchor.all
     = findFirst (fun a => decide (st'.topHidden a = some r)) Anchor.all
  exact findFirst_congr (fun a => by
    rw [topHidden_congr hdeal hdpt a]) Anchor.all

theorem hiddenBase_congr {st st' : State} (hdeal : st.deal = st'.deal)
    (hdpt : st.depths = st'.depths) (a : Anchor) :
    st.hiddenBase a = st'.hiddenBase a := by
  show (match ((st.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
     = (match ((st'.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  have hh : st.hidden a = st'.hidden a := by
    show (st.deal.piles a).take (st.depths a) = (st'.deal.piles a).take (st'.depths a)
    rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], hdpt]
  rw [hh]

/-- Pointwise forms: the hidden-pile views at one pile read that
pile's depth alone. -/
theorem topHidden_congr' {st st' : State} (hdeal : st.deal = st'.deal) (a : Anchor)
    (h : st.depths a = st'.depths a) : st.topHidden a = st'.topHidden a := by
  show ((st.deal.piles a).take (st.depths a)).getLast?
      = ((st'.deal.piles a).take (st'.depths a)).getLast?
  rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], h]

theorem hiddenBase_congr' {st st' : State} (hdeal : st.deal = st'.deal) (a : Anchor)
    (h : st.depths a = st'.depths a) : st.hiddenBase a = st'.hiddenBase a := by
  show (match ((st.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
     = (match ((st'.hidden a).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  have hh : st.hidden a = st'.hidden a := by
    show (st.deal.piles a).take (st.depths a) = (st'.deal.piles a).take (st'.depths a)
    rw [show st'.deal.piles a = st.deal.piles a from by rw [hdeal], h]
  rw [hh]

/-- The with-update form: the base at one pile survives a board change
and a depth change elsewhere. -/
theorem hiddenBase_congr'' {st : State} {bd : Board} {dpt : Anchor → Nat} (a : Anchor)
    (h : st.depths a = dpt a) :
    st.hiddenBase a = ({ st with board := bd, depths := dpt } : State).hiddenBase a := by
  show (match (((st.deal.piles a).take (st.depths a)).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
     = (match (((st.deal.piles a).take (dpt a)).reverse.drop 1).head? with
        | some d => Sum.inr d
        | none => Sum.inl a)
  rw [h]

/-- The heights updates commute as function updates (bump∘bump and
drop∘drop unconditionally; bump∘drop at a shared suit needs the height
positive — every stackPile guard supplies it). -/
theorem heights_bump_bump {α : Type} [DecidableEq α] (f : α → Nat) (σ σ' : α) :
    (fun s => if s = σ' then (if s = σ then f s + 1 else f s) + 1
      else if s = σ then f s + 1 else f s)
    = (fun s => if s = σ then (if s = σ' then f s + 1 else f s) + 1
      else if s = σ' then f s + 1 else f s) := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos h2]
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg h2]
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_neg h1, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

theorem heights_bump_drop {α : Type} [DecidableEq α] (f : α → Nat) (σ σ' : α) (hpos : σ = σ' → 0 < f σ) :
    (fun s => if s = σ' then (if s = σ then f s - 1 else f s) + 1
      else if s = σ then f s - 1 else f s)
    = (fun s => if s = σ then (if s = σ' then f s + 1 else f s) - 1
      else if s = σ' then f s + 1 else f s) := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos h2, h1]
      have hpos' := hpos (h1.symm.trans h2)
      omega
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg h2]
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_neg h1, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

theorem heights_drop_drop {α : Type} [DecidableEq α] (f : α → Nat) (σ σ' : α) :
    (fun s => if s = σ' then (if s = σ then f s - 1 else f s) - 1
      else if s = σ then f s - 1 else f s)
    = (fun s => if s = σ then (if s = σ' then f s - 1 else f s) - 1
      else if s = σ' then f s - 1 else f s) := by
  funext s
  by_cases h1 : s = σ
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_pos h1, if_pos h1, if_pos h2]
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg h2]
  · by_cases h2 : s = σ'
    · rw [if_pos h2, if_neg h1, if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

theorem disjointTouch_symm {t₁ t₂ : List Base × List Card}
    (h : disjointTouch t₁ t₂) : disjointTouch t₂ t₁ :=
  ⟨fun b hb hc => h.1 b hc hb, fun c hc hcm => h.2 c hcm hc⟩

/-- Reveal's depth steps commute (two reveals, each stepping its own
pile's boundary). -/
theorem depths_step_step (dpt : Anchor → Nat) (a a' : Anchor) :
    (fun x => if x = a' then (if a' = a then dpt a - 1 else dpt a') - 1
      else (if x = a then dpt a - 1 else dpt x))
    = (fun x => if x = a then (if a = a' then dpt a' - 1 else dpt a) - 1
      else (if x = a' then dpt a' - 1 else dpt x)) := by
  funext x
  by_cases h1 : x = a
  · by_cases h2 : x = a'
    · rw [if_pos h2, if_pos (h2.symm.trans h1), if_pos h1, if_pos (h1.symm.trans h2),
        show a = a' from h1.symm.trans h2]
    · rw [if_neg h2, if_pos h1, if_pos h1, if_neg (fun hc => h2 (h1.trans hc))]
  · by_cases h2 : x = a'
    · rw [if_pos h2, if_neg (fun hc => h1 (h2.trans hc)), if_neg h1, if_pos h2]
    · rw [if_neg h2, if_neg h1, if_neg h1, if_neg h2]

/-! ### The pair lemmas — `commute_of_disjoint_touch`'s arms

One lemma per genuinely-fine unordered pair, at a canonical order; the
main theorem dispatches both orders (with `disjointTouch_symm`).  Each
follows the same route: unpack both compositions' shape witnesses,
transfer them across the other move's writes (the touch-disjointness
confines every board write to its own bases and every `bottomOf` change
to its own cards; the hidden-pile views read only deal and depths), and
assemble the common successor fieldwise (the board via the edit
commutations, the heights/depths via the update lemmas). -/

theorem comm_reveal_deckPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.deckPile c' b').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.deckPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.deckPile c' b') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hDP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hDP', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd', hatt', hs₂⟩ := hDP
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp', bd₁', hatt₁', hs₃⟩ := hDP'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop', r', a', bd₂', hbot', hpile', hatt₂', hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  rw [hRt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [b'] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c'] := hdisj.2
  have hβ : st.hiddenBase a ≠ b' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcne : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hrne : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  -- the deckPile attach preserves c's and c''s seats; reveal's view is board-blind
  rw [hs₃] at hbot' hpile' hatt₂'
  have hbr : bd₁'.bottomOf c = some (Sum.inr r') := hbot'
  rw [bottomOf_attach_ne hatt₁' hcne, hbot] at hbr
  have hrr : r' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r' = some a' := hpile'
  rw [hrr] at hpl
  have haa : a' = a := Option.some.inj (hpl.symm.trans hpile)
  rw [hs₁] at hatt'
  have hatt'₂ : bd₁.attach b' c' = some bd' := hatt'
  rw [hrr, haa] at hatt₂'
  have hatt₂'' : bd₁'.attach (st.hiddenBase a) r = some bd₂' := hatt₂'
  have hbd : bd' = bd₂' := Board.attach_attach_comm hβ hatt hatt'₂ hatt₁' hatt₂''
  rw [hs₂, hs₁, hs₄, hs₃, haa, hbd]

theorem comm_reveal_pileStack {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hPS⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₂, b₀, hb, hrk, hs₃⟩ := hPS'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop₃, r'', a'', bd₄, hbot₃, hpile₃, hatt₃, hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  have hPSt : (Move.pileStack c').touch st = ([b₀], [c']) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hRt, hPSt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [b₀] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c'] := hdisj.2
  have hβ : st.hiddenBase a ≠ b₀ :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcne : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hrne : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  -- the detach preserves c's seat (c ≠ the detached card); reveal's view is board-blind
  rw [hs₃] at hbot₃ hpile₃ hatt₃
  have htb₀ : st.board.topOf b₀ = some c' := (Board.bottomOf_eq st.board c' b₀).mp hb
  have hbr : (st.board.detach b₀).bottomOf c = some (Sum.inr r'') := hbot₃
  rw [bottomOf_detach_ne htb₀ hcne, hbot] at hbr
  have hrr : r'' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r'' = some a'' := hpile₃
  rw [hrr] at hpl
  have haa : a'' = a := Option.some.inj (hpl.symm.trans hpile)
  -- pileStack's detach base is the same in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hrne), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hrr, haa] at hatt₃
  have hatt₃' : (st.board.detach b₀).attach (st.hiddenBase a) r = some bd₄ := hatt₃
  rw [hs₂, hs₁, hs₄, hs₃, haa, hb₀e]
  refine state_ext rfl ?_ rfl rfl rfl rfl
  exact attach_detach_comm hβ hatt hatt₃'

theorem comm_reveal_stackPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk, hcp, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop₃, r'', a'', bd₄, hbot₃, hpile₃, hatt₃, hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  rw [hRt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [b'] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c'] := hdisj.2
  have hβ : st.hiddenBase a ≠ b' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcne : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hrne : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  rw [hs₃] at hbot₃ hpile₃ hatt₃
  have hbr : bd₃.bottomOf c = some (Sum.inr r'') := hbot₃
  rw [bottomOf_attach_ne hatt₁ hcne, hbot] at hbr
  have hrr : r'' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r'' = some a'' := hpile₃
  rw [hrr] at hpl
  have haa : a'' = a := Option.some.inj (hpl.symm.trans hpile)
  rw [hs₁] at hatt'
  have hatt'₂ : bd₁.attach b' c' = some bd₂ := hatt'
  rw [hrr, haa] at hatt₃
  have hatt₃' : bd₃.attach (st.hiddenBase a) r = some bd₄ := hatt₃
  have hbd : bd₂ = bd₄ := Board.attach_attach_comm hβ hatt hatt'₂ hatt₁ hatt₃'
  rw [hs₂, hs₁, hs₄, hs₃, haa, hbd]

/-- `reveal`·`reveal`: the depth steps commute, the boundary searches
survive the other reveal's depth write *except* at the exposed pile —
and when the exposed card IS the other reveal's boundary card, the
first reveal's seating blocks the second's attach (vacuity, via
`take_reverse_drop1`: the base under the boundary is the card the
depth-step exposes). -/
theorem comm_reveal_reveal {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.reveal c').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.reveal c')) = some st₂)
    (h₂ : (st.apply (Move.reveal c') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hRA, hRB⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hRC, hRD⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hRA
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hRA
  rw [apply_reveal_iff] at hRB
  obtain ⟨htop', r₁, a₁, bd₂, hbot₁, hpile₁, hatt₁, hs₂⟩ := hRB
  rw [apply_reveal_iff] at hRC
  obtain ⟨htop₂, r', a', bd₃, hbot', hpile', hatt', hs₃⟩ := hRC
  rw [apply_reveal_iff] at hRD
  obtain ⟨htop₃, r₄, a₄, bd₄, hbot₄, hpile₄, hatt₄, hs₄⟩ := hRD
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  have hRt' : (Move.reveal c').touch st = ([st.hiddenBase a'], [c', r']) := by
    simp only [Move.touch, hbot', hpile']
  rw [hRt, hRt'] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ [st.hiddenBase a'] := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ [c', r'] := hdisj.2
  have hβ : st.hiddenBase a ≠ st.hiddenBase a' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hrc' : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  have hrr' : r ≠ r' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  have hcr' : c ≠ r' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hTa : st.topHidden a = some r := of_decide_eq_true (findFirst_mem _ _ _ hpile).2
  have hTa' : st.topHidden a' = some r' := of_decide_eq_true (findFirst_mem _ _ _ hpile').2
  have haa' : a ≠ a' := fun hcon => hβ (by rw [hcon])
  -- the triggers' under-cards are untouched (card-disjointness + the
  -- attach blindness)
  rw [hs₁] at hbot₁
  have hbr₁ : bd₁.bottomOf c' = some (Sum.inr r₁) := hbot₁
  rw [bottomOf_attach_ne hatt (Ne.symm hrc'), hbot'] at hbr₁
  have hr₁ : r₁ = r' := Sum.inr.inj (Option.some.inj hbr₁.symm)
  rw [hr₁] at hatt₁ hpile₁
  rw [hs₃] at hbot₄
  have hbr₄ : bd₃.bottomOf c = some (Sum.inr r₄) := hbot₄
  rw [bottomOf_attach_ne hatt' hcr', hbot] at hbr₄
  have hr₄ : r₄ = r := Sum.inr.inj (Option.some.inj hbr₄.symm)
  rw [hr₄] at hatt₄ hpile₄
  -- the boundary searches: both survive unless the exposed card is the
  -- other's boundary — and then the FIRST reveal's own attach dies (its
  -- base is the exposed card, which the other trigger already occupies)
  by_cases hred : s₁.topHidden a = some r'
  · exfalso
    have hreseq : s₁.topHidden a = ((st.deal.piles a).take (st.depths a - 1)).getLast? := by
      rw [hs₁]
      show ((st.deal.piles a).take (if a = a then st.depths a - 1 else st.depths a)).getLast?
          = ((st.deal.piles a).take (st.depths a - 1)).getLast?
      rw [if_pos rfl]
    have hred' : ((st.deal.piles a).take (st.depths a - 1)).getLast? = some r' :=
      hreseq.symm.trans hred
    have hseq : (((st.deal.piles a).take (st.depths a)).reverse.drop 1).head? = some r' :=
      take_reverse_drop1 hTa hred' hrr'
    have hhb : st.hiddenBase a = Sum.inr r' := by
      show (match (((st.deal.piles a).take (st.depths a)).reverse.drop 1).head? with
            | some d => Sum.inr d
            | none => Sum.inl a) = Sum.inr r'
      rw [hseq]
    rw [hhb] at hatt
    obtain ⟨htopg, -⟩ := (Board.attach_eq_some_iff st.board (Sum.inr r') r).mp
      (by rw [hatt]; simp)
    rw [(Board.bottomOf_eq st.board c' (Sum.inr r')).mp hbot'] at htopg
    exact absurd htopg (by simp)
  by_cases hred' : s₃.topHidden a' = some r
  · exfalso
    have hreseq : s₃.topHidden a' = ((st.deal.piles a').take (st.depths a' - 1)).getLast? := by
      rw [hs₃]
      show ((st.deal.piles a').take (if a' = a' then st.depths a' - 1 else st.depths a')).getLast?
          = ((st.deal.piles a').take (st.depths a' - 1)).getLast?
      rw [if_pos rfl]
    have hred'' : ((st.deal.piles a').take (st.depths a' - 1)).getLast? = some r :=
      hreseq.symm.trans hred'
    have hseq : (((st.deal.piles a').take (st.depths a')).reverse.drop 1).head? = some r :=
      take_reverse_drop1 hTa' hred'' (fun hcon => hrr' hcon.symm)
    have hhb : st.hiddenBase a' = Sum.inr r := by
      show (match (((st.deal.piles a').take (st.depths a')).reverse.drop 1).head? with
            | some d => Sum.inr d
            | none => Sum.inl a') = Sum.inr r
      rw [hseq]
    rw [hhb] at hatt'
    obtain ⟨htopg, -⟩ := (Board.attach_eq_some_iff st.board (Sum.inr r) r').mp
      (by rw [hatt']; simp)
    rw [(Board.bottomOf_eq st.board c (Sum.inr r)).mp hbot] at htopg
    exact absurd htopg (by simp)
  -- no redirects: the searches agree
  have hpp : s₁.pileOfTopHidden r' = st.pileOfTopHidden r' := by
    show findFirst (fun x => decide (s₁.topHidden x = some r')) Anchor.all
        = findFirst (fun x => decide (st.topHidden x = some r')) Anchor.all
    refine findFirst_congr (fun x => ?_) Anchor.all
    by_cases hxa : x = a
    · subst hxa
      rw [decide_congr (iff_of_false hred
        (fun (hp : st.topHidden x = some r') =>
          hrr' (Option.some.inj (hp.symm.trans hTa)).symm))]
    · have hdx : st.depths x = s₁.depths x := by
        rw [hs₁]
        show st.depths x = (if x = a then st.depths a - 1 else st.depths x)
        rw [if_neg hxa]
      rw [topHidden_congr' (by rw [hs₁]) x hdx]
  have hpp' : s₃.pileOfTopHidden r = st.pileOfTopHidden r := by
    show findFirst (fun x => decide (s₃.topHidden x = some r)) Anchor.all
        = findFirst (fun x => decide (st.topHidden x = some r)) Anchor.all
    refine findFirst_congr (fun x => ?_) Anchor.all
    by_cases hxa : x = a'
    · subst hxa
      rw [decide_congr (iff_of_false hred'
        (fun (hp : st.topHidden x = some r) =>
          hrr' (Option.some.inj (hp.symm.trans hTa'))))]
    · have hdx : st.depths x = s₃.depths x := by
        rw [hs₃]
        show st.depths x = (if x = a' then st.depths a' - 1 else st.depths x)
        rw [if_neg hxa]
      rw [topHidden_congr' (by rw [hs₃]) x hdx]
  rw [hpp] at hpile₁
  have haa₁ : a₁ = a' := Option.some.inj (hpile₁.symm.trans hpile')
  rw [hpp'] at hpile₄
  have haa₄ : a₄ = a := Option.some.inj (hpile₄.symm.trans hpile)
  -- the attach bases: each reveal's base survives the other's depth write
  have hdpa' : st.depths a' = (fun x => if x = a then st.depths a - 1 else st.depths x) a' := by
    show st.depths a' = (if a' = a then st.depths a - 1 else st.depths a')
    rw [if_neg (fun hcon => haa' hcon.symm)]
  have hbase₁ : s₁.hiddenBase a' = st.hiddenBase a' := by
    rw [hs₁, show st.hiddenBase a' = ({ st with board := bd₁, depths := fun x => if x = a then st.depths a - 1 else st.depths x } : State).hiddenBase a'
      from hiddenBase_congr'' a' hdpa']
  have hdpa : st.depths a = (fun x => if x = a' then st.depths a' - 1 else st.depths x) a := by
    show st.depths a = (if a = a' then st.depths a' - 1 else st.depths a)
    rw [if_neg haa']
  have hbase₄ : s₃.hiddenBase a = st.hiddenBase a := by
    rw [hs₃, show st.hiddenBase a = ({ st with board := bd₃, depths := fun x => if x = a' then st.depths a' - 1 else st.depths x } : State).hiddenBase a
      from hiddenBase_congr'' a hdpa]
  rw [haa₁, hbase₁, hs₁] at hatt₁
  have hatt₁' : bd₁.attach (st.hiddenBase a') r' = some bd₂ := hatt₁
  rw [haa₄, hbase₄, hs₃] at hatt₄
  have hatt₄' : bd₃.attach (st.hiddenBase a) r = some bd₄ := hatt₄
  have hbd : bd₂ = bd₄ := Board.attach_attach_comm hβ hatt hatt₁' hatt' hatt₄'
  rw [hs₂, hs₁, hs₄, hs₃, haa₁, haa₄, hbd]
  refine state_ext rfl rfl rfl ?_ rfl rfl
  exact depths_step_step st.depths a a'

theorem comm_reveal_pilePile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.reveal c).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.reveal c) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.reveal c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hR, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hR'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_reveal_iff] at hR
  obtain ⟨htop, r, a, bd₁, hbot, hpile, hatt, hs₁⟩ := hR
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀, hb, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_reveal_iff] at hR'
  obtain ⟨htop₃, r'', a'', bd₄, hbot₃, hpile₃, hatt₃, hs₄⟩ := hR'
  have hRt : (Move.reveal c).touch st = ([st.hiddenBase a], [c, r]) := by
    simp only [Move.touch, hbot, hpile]
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hRt, hPPt] at hdisj
  have hD1 : ∀ b ∈ [st.hiddenBase a], b ∉ (b' :: [b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c, r], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hβ₁ : st.hiddenBase a ≠ b' :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hβ₂ : st.hiddenBase a ≠ b₀ :=
    fun hcon => hD1 (st.hiddenBase a) (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  have hcAb : c ∉ st.board.aboveOf c' :=
    fun hcon => hD2 c (by simp) (by simp [hcon])
  have hrc' : r ≠ c' := fun hcon => hD2 r (by simp) (by rw [hcon]; simp)
  have hrAb : r ∉ st.board.aboveOf c' :=
    fun hcon => hD2 r (by simp) (by simp [hcon])
  -- reveal's trigger seat survives the pilePile edit; its view is board-blind
  rw [hs₃] at hbot₃ hpile₃ hatt₃
  have htb₀ : st.board.topOf b₀ = some c' := (Board.bottomOf_eq st.board c' b₀).mp hb
  have hbr : bd₃.bottomOf c = some (Sum.inr r'') := hbot₃
  rw [bottomOf_attach_ne hatt₁ hcc', bottomOf_detach_ne htb₀ hcc', hbot] at hbr
  have hrr : r'' = r := Sum.inr.inj (Option.some.inj hbr.symm)
  have hpl : st.pileOfTopHidden r'' = some a'' := hpile₃
  rw [hrr] at hpl
  have haa : a'' = a := Option.some.inj (hpl.symm.trans hpile)
  -- pilePile's detach base agrees in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hrc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hrr, haa] at hatt₃
  have hatt₃' : bd₃.attach (st.hiddenBase a) r = some bd₄ := hatt₃
  rw [hs₁] at hatt'
  have hatt'₂ : (bd₁.detach b₀').attach b' c' = some bd₂ := hatt'
  rw [hb₀e] at hatt'₂
  -- the board: attach (hb a) r, detach b₀, attach b' c' — three distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = st.hiddenBase a
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hβ₁,
        Board.detach_topOf_ne bd₁ b₀ _ hβ₂,
        Board.attach_topOf st.board _ r hatt, Board.attach_topOf bd₃ _ r hatt₃']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne bd₃ _ r hatt₃'
          (fun hcon => hβ₁ hcon.symm), Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hne,
            Board.detach_topOf, Board.attach_topOf_ne bd₃ _ r hatt₃' (Ne.symm hβ₂),
            Board.attach_topOf_ne _ _ _ hatt₁ hne, Board.detach_topOf]
        · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb',
            Board.detach_topOf_ne _ _ _ hxb₀, Board.attach_topOf_ne _ _ _ hatt hxb,
            Board.attach_topOf_ne bd₃ _ r hatt₃' hxb,
            Board.attach_topOf_ne _ _ _ hatt₁ hxb', Board.detach_topOf_ne _ _ _ hxb₀]
  rw [hs₂, hs₁, hs₄, hs₃, haa, hbd]

theorem comm_deckPile_pileStack {st : State} {c c' : Card} {b : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckPile c b).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.deckPile c b) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.deckPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDP, hPS⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS', hDP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd₁, hatt, hs₁⟩ := hDP
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₂, b₀, hb, hrk, hs₃⟩ := hPS'
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp', bd₂, hatt', hs₄⟩ := hDP'
  have hPSt : (Move.pileStack c').touch st = ([b₀], [c']) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPSt] at hdisj
  have hD1 : ∀ β ∈ [b], β ∉ ([b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb₀ : b ≠ b₀ := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- pileStack's guard at s₁: the same detach base
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  -- deckPile's guard at s₃: the base is untouched (b ≠ b₀); the isVis
  -- read vacates only when it read the detached card itself
  rw [hs₃] at hcp' hatt'
  have hatt'₂ : (st.board.detach b₀).attach b c = some bd₂ := hatt'
  cases b with
  | inl _ =>
      rw [hs₂, hs₁, hs₄, hs₃, hb₀e]
      refine state_ext rfl ?_ rfl rfl rfl rfl
      exact attach_detach_comm hbb₀ hatt hatt'₂
  | inr d =>
      by_cases hdc : d = c'
      · exfalso
        rw [← hdc] at hb
        have h1 : (st.board.detach b₀).bottomOf d = none :=
          detach_bottomOf_self ((Board.bottomOf_eq st.board d b₀).mp hb)
        have h2 : ({ st with board := st.board.detach b₀, heights := fun s => if s = d.suit then st.heights s + 1 else st.heights s } : State).isVis d = true := by
          have := hcp'
          simp only [State.canPlace, Bool.and_eq_true_iff, decide_eq_true_iff] at this
          exact this.2.1
        rw [State.isVis, h1] at h2
        exact absurd h2 (by simp)
      · rw [hs₂, hs₁, hs₄, hs₃, hb₀e]
        refine state_ext rfl ?_ rfl rfl rfl rfl
        exact attach_detach_comm hbb₀ hatt hatt'₂

/-- `canPlace`'s tableau half: the base card is visible. -/
theorem canPlace_inr_isVis {st : State} {c d : Card}
    (h : st.canPlace c (Sum.inr d) = true) : st.isVis d = true := by
  simp only [State.canPlace, Bool.and_eq_true_iff, decide_eq_true_iff] at h
  exact h.2.1

theorem comm_deckPile_stackPile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckPile c b).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.deckPile c b) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.deckPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDP, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hDP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd₁, hatt, hs₁⟩ := hDP
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk, hcp₂, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp₃, bd₄, hatt₂', hs₄⟩ := hDP'
  have hD1 : ∀ β ∈ [b], β ∉ ([b'] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- vacuity corners: a base card equal to the other move's card is
  -- both required visible (its canPlace) and required unseated (the
  -- other's attach guard)
  have hatt₁g : st.board.bottomOf c' = none :=
    ((Board.attach_eq_some_iff st.board b' c').mp (by rw [hatt₁]; simp)).2
  have hattg : st.board.bottomOf c = none :=
    ((Board.attach_eq_some_iff st.board b c).mp (by rw [hatt]; simp)).2
  cases b with
  | inl a =>
      cases b' with
      | inl a' =>
          rw [hs₁] at hatt'
          rw [hs₃] at hatt₂'
          have hatt'₂ : bd₁.attach (Sum.inl a') c' = some bd₂ := hatt'
          have hatt₂'' : bd₃.attach (Sum.inl a) c = some bd₄ := hatt₂'
          have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
          rw [hs₂, hs₁, hs₄, hs₃, hbd]
      | inr d' =>
          by_cases hd' : d' = c
          · exfalso
            have h2 := canPlace_inr_isVis hcp₂
            rw [hd', State.isVis, hattg] at h2
            exact absurd h2 (by simp)
          · rw [hs₁] at hatt'
            rw [hs₃] at hatt₂'
            have hatt'₂ : bd₁.attach (Sum.inr d') c' = some bd₂ := hatt'
            have hatt₂'' : bd₃.attach (Sum.inl a) c = some bd₄ := hatt₂'
            have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
            rw [hs₂, hs₁, hs₄, hs₃, hbd]
  | inr d =>
      by_cases hd : d = c'
      · exfalso
        have h2 := canPlace_inr_isVis hcp
        rw [hd, State.isVis, hatt₁g] at h2
        exact absurd h2 (by simp)
      · cases b' with
        | inl a' =>
            rw [hs₁] at hatt'
            rw [hs₃] at hatt₂'
            have hatt'₂ : bd₁.attach (Sum.inl a') c' = some bd₂ := hatt'
            have hatt₂'' : bd₃.attach (Sum.inr d) c = some bd₄ := hatt₂'
            have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
            rw [hs₂, hs₁, hs₄, hs₃, hbd]
        | inr d' =>
            by_cases hd'' : d' = c
            · exfalso
              have h2 := canPlace_inr_isVis hcp₂
              rw [hd'', State.isVis, hattg] at h2
              exact absurd h2 (by simp)
            · rw [hs₁] at hatt'
              rw [hs₃] at hatt₂'
              have hatt'₂ : bd₁.attach (Sum.inr d') c' = some bd₂ := hatt'
              have hatt₂'' : bd₃.attach (Sum.inr d) c = some bd₄ := hatt₂'
              have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
              rw [hs₂, hs₁, hs₄, hs₃, hbd]

theorem comm_deckPile_pilePile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckPile c b).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.deckPile c b) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.deckPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDP, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hDP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckPile_iff] at hDP
  obtain ⟨hprev, hcp, bd₁, hatt, hs₁⟩ := hDP
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀, hb, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_deckPile_iff] at hDP'
  obtain ⟨hprev', hcp', bd₄, hatt₂', hs₄⟩ := hDP'
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPPt] at hdisj
  have hD1 : ∀ β ∈ [b], β ∉ (b' :: [b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hbb₀ : b ≠ b₀ := fun hcon => hD1 b (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- pilePile's detach base agrees in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hs₁, hb₀e] at hatt'
  have hatt'₂ : (bd₁.detach b₀).attach b' c' = some bd₂ := hatt'
  rw [hs₃] at hatt₂'
  have hatt₂'' : bd₃.attach b c = some bd₄ := hatt₂'
  -- the board: attach b c, detach b₀, attach b' c' — three distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = b
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hbb',
        Board.detach_topOf_ne _ _ _ hbb₀, Board.attach_topOf _ _ _ hatt,
        Board.attach_topOf _ _ _ hatt₂'']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb'),
          Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hne, Board.detach_topOf,
            Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb₀),
            Board.attach_topOf_ne _ _ _ hatt₁ hne, Board.detach_topOf]
        · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb', Board.detach_topOf_ne _ _ _ hxb₀,
            Board.attach_topOf_ne _ _ _ hatt hxb,
            Board.attach_topOf_ne _ _ _ hatt₂'' hxb,
            Board.attach_topOf_ne _ _ _ hatt₁ hxb',
            Board.detach_topOf_ne _ _ _ hxb₀]
  rw [hs₂, hs₁, hs₄, hs₃, hbd]

theorem comm_deckStack_pileStack {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckStack c).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.deckStack c) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.deckStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDS, hPS⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS', hDS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckStack_iff] at hDS
  obtain ⟨hprev, hrk, hs₁⟩ := hDS
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₂, b₀, hb, hrk₂, hs₃⟩ := hPS'
  rw [apply_deckStack_iff] at hDS'
  obtain ⟨hprev', hrk', hs₄⟩ := hDS'
  have hPSt : (Move.pileStack c').touch st = ([b₀], [c']) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPSt] at hdisj
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the two deckStack guards (one reads the
  -- pre-bump height, the other the post-bump)
  by_cases hσ : c'.suit = c.suit
  · exfalso
    rw [hs₃] at hrk'
    have hrk'' : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit + 1
      else st.heights c.suit) := hrk'
    rw [if_pos hσ.symm] at hrk''
    omega
  -- the suits differ: the bumps land on independent coordinates
  have hb₂ : st.board.bottomOf c' = some b₀' := by
    rw [hs₁] at hb'
    exact hb'
  rw [hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hs₂, hs₁, hs₄, hs₃, hb₀e]
  refine state_ext rfl rfl ?_ rfl rfl rfl
  exact heights_bump_bump st.heights c.suit c'.suit

theorem comm_deckStack_stackPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.deckStack c).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.deckStack c) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.deckStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hDS, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hDS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_deckStack_iff] at hDS
  obtain ⟨hprev, hrk, hs₁⟩ := hDS
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk₂, hcp, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_deckStack_iff] at hDS'
  obtain ⟨hprev', hrk'', hs₄⟩ := hDS'
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the deckStack guards through the drop
  have hvac : c.suit = c'.suit → False := by
    intro hσ
    rw [hs₃] at hrk''
    have hrk3 : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit - 1
      else st.heights c.suit) := hrk''
    rw [if_pos hσ] at hrk3
    rw [← hσ] at hrk₂
    omega
  have hpos : c'.suit = c.suit → 0 < st.heights c'.suit := fun _ => by
    have := hrk₂
    omega
  -- the two stackPile attaches are the same op on the same board
  rw [hs₁] at hatt'
  have hatt'₂ : st.board.attach b' c' = some bd₂ := hatt'
  have hbd : bd₂ = bd₃ := Option.some.inj (hatt'₂.symm.trans hatt₁)
  rw [hs₂, hs₁, hs₄, hs₃, hbd]
  refine state_ext rfl rfl ?_ rfl rfl rfl
  exact (heights_bump_drop st.heights c'.suit c.suit hpos).symm

theorem comm_pileStack_pileStack {st : State} {c c' : Card} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pileStack c).touch st) ((Move.pileStack c').touch st))
    (h₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.pileStack c')) = some st₂)
    (h₂ : (st.apply (Move.pileStack c') >>= fun s => s.apply (Move.pileStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPS, hPS'⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPS'', hPS'''⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop, b₀, hb, hrk, hs₁⟩ := hPS
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop', b₀', hb', hrk', hs₂⟩ := hPS'
  rw [apply_pileStack_iff] at hPS''
  obtain ⟨htop₂, b₀₂, hb₂, hrk₂, hs₃⟩ := hPS''
  rw [apply_pileStack_iff] at hPS'''
  obtain ⟨htop₃, b₀₃, hb₃, hrk₃, hs₄⟩ := hPS'''
  have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
    simp only [Move.touch, hb, Option.toList_some]
  have hPSt' : (Move.pileStack c').touch st = ([b₀₂], [c']) := by
    simp only [Move.touch, hb₂, Option.toList_some]
  rw [hPSt, hPSt'] at hdisj
  have hD1 : ∀ β ∈ [b₀], β ∉ ([b₀₂] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb₀ : b₀ ≠ b₀₂ := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the two pileStack guards (one reads the
  -- pre-bump height, the other the post-bump)
  by_cases hσ : c'.suit = c.suit
  · exfalso
    rw [hs₃] at hrk₃
    have hrk4 : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit + 1
      else st.heights c.suit) := hrk₃
    rw [if_pos hσ.symm] at hrk4
    omega
  -- the second detach reads the same seat in both orders
  have htb₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
  have htb₀₂ : st.board.topOf b₀₂ = some c' := (Board.bottomOf_eq st.board c' b₀₂).mp hb₂
  rw [hs₁] at hb'
  have hb₁ : (st.board.detach b₀).bottomOf c' = some b₀' := hb'
  rw [bottomOf_detach_ne htb₀ (Ne.symm hcc'), hb₂] at hb₁
  have hb₀e : b₀' = b₀₂ := (Option.some.inj hb₁).symm
  rw [hs₃] at hb₃
  have hb₃' : (st.board.detach b₀₂).bottomOf c = some b₀₃ := hb₃
  rw [bottomOf_detach_ne htb₀₂ hcc', hb] at hb₃'
  have hb₀₃e : b₀₃ = b₀ := (Option.some.inj hb₃').symm
  rw [hs₂, hs₁, hs₄, hs₃, hb₀e, hb₀₃e]
  refine state_ext rfl ?_ ?_ rfl rfl rfl
  · exact detach_detach_comm hbb₀
  · exact heights_bump_bump st.heights c.suit c'.suit

theorem comm_pileStack_stackPile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pileStack c).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.pileStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPS, hSP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP', hPS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop, b₀, hb, hrk, hs₁⟩ := hPS
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk₂, hcp, bd₃, hatt₁, hs₃⟩ := hSP'
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₃, b₀₃, hb₃, hrk₃, hs₄⟩ := hPS'
  have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPSt] at hdisj
  have hD1 : ∀ β ∈ [b₀], β ∉ ([b'] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hb₀b' : b₀ ≠ b' := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the guards through the drop
  have hvac : c'.suit = c.suit → False := by
    intro hσ
    rw [hs₃] at hrk₃
    have hrk4 : c.rank.toIdx = (if c.suit = c'.suit then st.heights c.suit - 1
      else st.heights c.suit) := hrk₃
    rw [if_pos hσ.symm] at hrk4
    rw [hσ] at hrk₂
    omega
  have hpos : c'.suit = c.suit → 0 < st.heights c'.suit := by
    intro _
    have := hrk₂
    omega
  -- the detach/attach bases agree in both orders
  have htb₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
  rw [hs₃] at hb₃
  have hb₃' : bd₃.bottomOf c = some b₀₃ := hb₃
  rw [bottomOf_attach_ne hatt₁ hcc', hb] at hb₃'
  have hb₀₃e : b₀₃ = b₀ := (Option.some.inj hb₃').symm
  rw [hs₁] at hatt'
  have hatt'₂ : (st.board.detach b₀).attach b' c' = some bd₂ := hatt'
  rw [hs₂, hs₁, hs₄, hs₃, hb₀₃e]
  refine state_ext rfl ?_ ?_ rfl rfl rfl
  · exact (attach_detach_comm (Ne.symm hb₀b') hatt₁ hatt'₂).symm
  · exact (heights_bump_drop st.heights c'.suit c.suit hpos).symm

theorem comm_pileStack_pilePile {st : State} {c c' : Card} {b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pileStack c).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.pileStack c) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.pileStack c)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPS, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hPS'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pileStack_iff] at hPS
  obtain ⟨htop, b₀, hb, hrk, hs₁⟩ := hPS
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀₂, hb₂, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_pileStack_iff] at hPS'
  obtain ⟨htop₃, b₀₃, hb₃, hrk₃, hs₄⟩ := hPS'
  have hPSt : (Move.pileStack c).touch st = ([b₀], [c]) := by
    simp only [Move.touch, hb, Option.toList_some]
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀₂], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb₂, Option.toList_some]
  rw [hPSt, hPPt] at hdisj
  have hD1 : ∀ β ∈ [b₀], β ∉ (b' :: [b₀₂] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hb₀b' : b₀ ≠ b' := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hb₀b₂ : b₀ ≠ b₀₂ := fun hcon => hD1 b₀ (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- the detach bases agree in both orders
  have htb₀ : st.board.topOf b₀ = some c := (Board.bottomOf_eq st.board c b₀).mp hb
  have htb₀₂ : st.board.topOf b₀₂ = some c' := (Board.bottomOf_eq st.board c' b₀₂).mp hb₂
  rw [hs₁] at hb'
  have hb₁ : (st.board.detach b₀).bottomOf c' = some b₀' := hb'
  rw [bottomOf_detach_ne htb₀ (Ne.symm hcc'), hb₂] at hb₁
  have hb₀e : b₀' = b₀₂ := (Option.some.inj hb₁).symm
  rw [hs₃] at hb₃
  have hb₃' : bd₃.bottomOf c = some b₀₃ := hb₃
  rw [bottomOf_attach_ne hatt₁ hcc', bottomOf_detach_ne htb₀₂ hcc', hb] at hb₃'
  have hb₀₃e : b₀₃ = b₀ := (Option.some.inj hb₃').symm
  rw [hs₁, hb₀e] at hatt'
  have hatt'₂ : ((st.board.detach b₀).detach b₀₂).attach b' c' = some bd₂ := hatt'
  rw [detach_detach_comm hb₀b₂] at hatt'₂
  rw [hs₂, hs₁, hs₄, hs₃, hb₀₃e]
  refine state_ext rfl ?_ rfl rfl rfl rfl
  exact (attach_detach_comm (Ne.symm hb₀b') hatt₁ hatt'₂).symm

theorem comm_stackPile_stackPile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.stackPile c b).touch st) ((Move.stackPile c' b').touch st))
    (h₁ : (st.apply (Move.stackPile c b) >>= fun s => s.apply (Move.stackPile c' b')) = some st₂)
    (h₂ : (st.apply (Move.stackPile c' b') >>= fun s => s.apply (Move.stackPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hSP, hSP'⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hSP'', hSP'''⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk, hcp, bd₁, hatt, hs₁⟩ := hSP
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk', hcp', bd₂, hatt', hs₂⟩ := hSP'
  rw [apply_stackPile_iff] at hSP''
  obtain ⟨hrk₂, hcp₂, bd₃, hatt₁, hs₃⟩ := hSP''
  rw [apply_stackPile_iff] at hSP'''
  obtain ⟨hrk₃, hcp₃, bd₄, hatt₂', hs₄⟩ := hSP'''
  have hD1 : ∀ β ∈ [b], β ∉ ([b'] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ [c'] := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- a shared suit contradicts the two guards through the drop
  by_cases hσ : c'.suit = c.suit
  · exfalso
    rw [hs₃] at hrk₃
    have hrk4 : c.rank.toIdx + 1 = (if c.suit = c'.suit then st.heights c.suit - 1
      else st.heights c.suit) := hrk₃
    rw [if_pos hσ.symm] at hrk4
    omega
  rw [hs₁] at hatt'
  have hatt'₂ : bd₁.attach b' c' = some bd₂ := hatt'
  rw [hs₃] at hatt₂'
  have hatt₂'' : bd₃.attach b c = some bd₄ := hatt₂'
  have hbd : bd₂ = bd₄ := Board.attach_attach_comm hbb' hatt hatt'₂ hatt₁ hatt₂''
  rw [hs₂, hs₁, hs₄, hs₃, hbd]
  refine state_ext rfl rfl ?_ rfl rfl rfl
  exact heights_drop_drop st.heights c.suit c'.suit

theorem comm_stackPile_pilePile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.stackPile c b).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.stackPile c b) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.stackPile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hSP, hPP⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP', hSP'⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_stackPile_iff] at hSP
  obtain ⟨hrk, hcp, bd₁, hatt, hs₁⟩ := hSP
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀, hb, hne, hcmr, bd₃, hatt₁, hs₃⟩ := hPP'
  rw [apply_stackPile_iff] at hSP'
  obtain ⟨hrk', hcp', bd₄, hatt₂', hs₄⟩ := hSP'
  have hPPt : (Move.pilePile c' b').touch st = (b' :: [b₀], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb, Option.toList_some]
  rw [hPPt] at hdisj
  have hD1 : ∀ β ∈ [b], β ∉ (b' :: [b₀] : List Base) := hdisj.1
  have hD2 : ∀ x ∈ [c], x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hbb₀ : b ≠ b₀ := fun hcon => hD1 b (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- pilePile's detach base agrees in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), hb] at hb₂
  have hb₀e : b₀' = b₀ := (Option.some.inj hb₂).symm
  rw [hs₁, hb₀e] at hatt'
  have hatt'₂ : (bd₁.detach b₀).attach b' c' = some bd₂ := hatt'
  rw [hs₃] at hatt₂'
  have hatt₂'' : bd₃.attach b c = some bd₄ := hatt₂'
  -- the board: attach b c, detach b₀, attach b' c' — three distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = b
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hbb',
        Board.detach_topOf_ne _ _ _ hbb₀, Board.attach_topOf _ _ _ hatt,
        Board.attach_topOf _ _ _ hatt₂'']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb'),
          Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hne, Board.detach_topOf,
            Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb₀),
            Board.attach_topOf_ne _ _ _ hatt₁ hne, Board.detach_topOf]
        · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb', Board.detach_topOf_ne _ _ _ hxb₀,
            Board.attach_topOf_ne _ _ _ hatt hxb,
            Board.attach_topOf_ne _ _ _ hatt₂'' hxb,
            Board.attach_topOf_ne _ _ _ hatt₁ hxb',
            Board.detach_topOf_ne _ _ _ hxb₀]
  rw [hs₂, hs₁, hs₄, hs₃, hbd]

theorem comm_pilePile_pilePile {st : State} {c c' : Card} {b b' : Base} {st₂ st₃ : State}
    (hdisj : disjointTouch ((Move.pilePile c b).touch st) ((Move.pilePile c' b').touch st))
    (h₁ : (st.apply (Move.pilePile c b) >>= fun s => s.apply (Move.pilePile c' b')) = some st₂)
    (h₂ : (st.apply (Move.pilePile c' b') >>= fun s => s.apply (Move.pilePile c b)) = some st₃) :
    st₂ = st₃ := by
  obtain ⟨s₁, hPP, hPP'⟩ := Option.bind_eq_some_iff.mp h₁
  obtain ⟨s₃, hPP'', hPP'''⟩ := Option.bind_eq_some_iff.mp h₂
  rw [apply_pilePile_iff] at hPP
  obtain ⟨b₀, hb, hne, hcmr, bd₁, hatt, hs₁⟩ := hPP
  rw [apply_pilePile_iff] at hPP'
  obtain ⟨b₀', hb', hne', hcmr', bd₂, hatt', hs₂⟩ := hPP'
  rw [apply_pilePile_iff] at hPP''
  obtain ⟨b₀'', hb'', hne'', hcmr'', bd₃, hatt₁, hs₃⟩ := hPP''
  rw [apply_pilePile_iff] at hPP'''
  obtain ⟨b₀''', hb''', hne''', hcmr''', bd₄, hatt₂', hs₄⟩ := hPP'''
  have hPPt : (Move.pilePile c b).touch st = (b :: [b₀], c :: st.board.aboveOf c) := by
    simp only [Move.touch, hb, Option.toList_some]
  have hPPt' : (Move.pilePile c' b').touch st = (b' :: [b₀''], c' :: st.board.aboveOf c') := by
    simp only [Move.touch, hb'', Option.toList_some]
  rw [hPPt, hPPt'] at hdisj
  have hD1 : ∀ β ∈ (b :: [b₀] : List Base), β ∉ (b' :: [b₀'']) := hdisj.1
  have hD2 : ∀ x ∈ (c :: st.board.aboveOf c), x ∉ (c' :: st.board.aboveOf c') := hdisj.2
  have hbb' : b ≠ b' := fun hcon => hD1 b (by simp) (by rw [hcon]; simp)
  have hbb'' : b ≠ b₀'' := fun hcon => hD1 b (by simp) (by simp [hcon])
  have hb₀b' : b₀ ≠ b' := fun hcon => hD1 b₀ (by simp) (by rw [hcon]; simp)
  have hb₀b'' : b₀ ≠ b₀'' := fun hcon => hD1 b₀ (by simp) (by simp [hcon])
  have hcc' : c ≠ c' := fun hcon => hD2 c (by simp) (by rw [hcon]; simp)
  -- the detach bases agree in both orders
  rw [hs₁] at hb'
  have hb₂ : bd₁.bottomOf c' = some b₀' := hb'
  rw [bottomOf_attach_ne hatt (Ne.symm hcc'), bottomOf_detach_ne
    ((Board.bottomOf_eq st.board c b₀).mp hb) (Ne.symm hcc'), hb''] at hb₂
  have hb₀e : b₀' = b₀'' := (Option.some.inj hb₂).symm
  rw [hs₃] at hb'''
  have hb₃ : bd₃.bottomOf c = some b₀''' := hb'''
  rw [bottomOf_attach_ne hatt₁ hcc', bottomOf_detach_ne
    ((Board.bottomOf_eq st.board c' b₀'').mp hb'') hcc', hb] at hb₃
  have hb₀₃e : b₀''' = b₀ := (Option.some.inj hb₃).symm
  rw [hs₁, hb₀e] at hatt'
  rw [hb₀e] at hne'
  have hatt'₂ : (bd₁.detach b₀'').attach b' c' = some bd₂ := hatt'
  rw [hs₃, hb₀₃e] at hatt₂'
  have hatt₂'' : (bd₃.detach b₀).attach b c = some bd₄ := hatt₂'
  have hb₀''b' : b₀'' ≠ b' := hne'
  -- the board: two detaches and two attaches at four distinct bases
  have hbd : bd₂ = bd₄ := by
    refine Board.ext_topOf (funext (fun x => ?_))
    by_cases hxb : x = b
    · rw [hxb, Board.attach_topOf_ne _ _ _ hatt'₂ hbb', Board.detach_topOf_ne _ _ _ hbb'',
        Board.attach_topOf _ _ _ hatt, Board.attach_topOf _ _ _ hatt₂'']
    · by_cases hxb' : x = b'
      · rw [hxb', Board.attach_topOf _ _ _ hatt'₂, Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb'),
          Board.detach_topOf_ne _ _ _ (Ne.symm hb₀b'), Board.attach_topOf _ _ _ hatt₁]
      · by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.attach_topOf_ne _ _ _ hatt'₂ hb₀b', Board.detach_topOf_ne _ _ _ hb₀b'',
            Board.attach_topOf_ne _ _ _ hatt hne, Board.detach_topOf,
            Board.attach_topOf_ne _ _ _ hatt₂'' hne, Board.detach_topOf]
        · by_cases hxb₀'' : x = b₀''
          · rw [hxb₀'', Board.attach_topOf_ne _ _ _ hatt'₂ hb₀''b', Board.detach_topOf,
              Board.attach_topOf_ne _ _ _ hatt₂'' (Ne.symm hbb''),
              Board.detach_topOf_ne _ _ _ (Ne.symm hb₀b''), Board.attach_topOf_ne _ _ _ hatt₁ hb₀''b',
              Board.detach_topOf]
          · rw [Board.attach_topOf_ne _ _ _ hatt'₂ hxb', Board.detach_topOf_ne _ _ _ hxb₀'',
              Board.attach_topOf_ne _ _ _ hatt hxb, Board.detach_topOf_ne _ _ _ hxb₀,
              Board.attach_topOf_ne _ _ _ hatt₂'' hxb, Board.detach_topOf_ne _ _ _ hxb₀,
              Board.attach_topOf_ne _ _ _ hatt₁ hxb', Board.detach_topOf_ne _ _ _ hxb₀'']
  rw [hs₂, hs₁, hs₄, hs₃, hbd]

/-- The fine-grained commutation schema — the type-ball interaction
lemma.  Moves with disjoint touch-sets commute (given both orders are
defined).

STATEMENT REPAIR (2026-09-13, prover-confirmed witness
`Temp\opencode\CommuteWitness.lean`): as originally staged (the
`hdisj` guard alone) this is FALSE for `{m, m'} = {draw, deckPile}`
(dually deckStack) — `.draw`'s touch set is ([], []), disjoint from
everything, but the deck moves' legality reads the waste top
(cursor-sensitive), which the deal changes: stock [cK, h2, cK, h4],
cursor 1, step 2, `cK` a king landing on a free anchor — both orders
succeed, landing on stocks [h2, cK, h4] and [cK, h2, h4].  Minimal
repair: the `hnc` guard — a deal only commutes with non-consuming
moves.  With it: `draw`-rows are `deal_commutes_nonStock`; the four
deck·deck pairs are vacuous (both first moves read the same `prev`);
reveal·deckStack and pilePile·deckStack fall to the coarse
`commute_of_compsDisjoint`; and the remaining sixteen fine pairs are
the `comm_*` lemmas above. -/
theorem commute_of_disjoint_touch {st : State} {m m' : Move} {st₂ st₃ : State}
    (hdisj : disjointTouch (m.touch st) (m'.touch st))
    (hnc : (m = Move.draw → m'.consumesStock = false) ∧
           (m' = Move.draw → m.consumesStock = false))
    (h₁ : (st.apply m >>= fun s => s.apply m') = some st₂)
    (h₂ : (st.apply m' >>= fun s => s.apply m) = some st₃) : st₂ = st₃ := by
  cases m with
  | draw =>
      cases m' with
      | draw => exact Option.some.inj (h₁.symm.trans h₂)
      | reveal c =>
          have hcomp := deal_commutes_nonStock st (Move.reveal c) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
      | deckPile c b => exact absurd (hnc.1 rfl) (by simp [Move.consumesStock])
      | deckStack c => exact absurd (hnc.1 rfl) (by simp [Move.consumesStock])
      | pileStack c =>
          have hcomp := deal_commutes_nonStock st (Move.pileStack c) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
      | stackPile c b =>
          have hcomp := deal_commutes_nonStock st (Move.stackPile c b) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
      | pilePile c b =>
          have hcomp := deal_commutes_nonStock st (Move.pilePile c b) (hnc.1 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.symm.trans h₂))
  | reveal c =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.reveal c) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact comm_reveal_reveal hdisj h₁ h₂
      | deckPile c' b' => exact comm_reveal_deckPile hdisj h₁ h₂
      | deckStack c' =>
          have hcomp := commute_of_compsDisjoint st (Move.reveal c) (Move.deckStack c') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps]
            | foundations => simp [Move.comps] at hx
            | hidden => simp [Move.comps]
            | stock => simp [Move.comps] at hx)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | pileStack c' => exact comm_reveal_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_reveal_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_reveal_pilePile hdisj h₁ h₂
  | deckPile c b =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.deckPile c b) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_deckPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckPile_iff] at hA hC
          obtain ⟨hprev, _, _, _, _⟩ := hA
          obtain ⟨hprev', _, _, _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | deckStack c' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckPile_iff] at hA
          rw [apply_deckStack_iff] at hC
          obtain ⟨hprev, _, _, _, _⟩ := hA
          obtain ⟨hprev', _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | pileStack c' => exact comm_deckPile_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_deckPile_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_deckPile_pilePile hdisj h₁ h₂
  | deckStack c =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.deckStack c) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' =>
          have hcomp := commute_of_compsDisjoint st (Move.deckStack c) (Move.reveal c') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps] at hx
            | foundations => simp [Move.comps]
            | hidden => simp [Move.comps] at hx
            | stock => simp [Move.comps])
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | deckPile c' b' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckStack_iff] at hA
          rw [apply_deckPile_iff] at hC
          obtain ⟨hprev, _, _⟩ := hA
          obtain ⟨hprev', _, _, _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | deckStack c' =>
          exfalso
          obtain ⟨s₁, hA, _⟩ := Option.bind_eq_some_iff.mp h₁
          obtain ⟨s₃, hC, _⟩ := Option.bind_eq_some_iff.mp h₂
          rw [apply_deckStack_iff] at hA hC
          obtain ⟨hprev, _, _⟩ := hA
          obtain ⟨hprev', _, _⟩ := hC
          rw [hprev] at hprev'
          have hcc' : c ≠ c' := fun hcon =>
            hdisj.2 c (by show c ∈ [c]; simp) (by rw [hcon]; show c' ∈ [c']; simp)
          exact hcc' (Option.some.inj hprev')
      | pileStack c' => exact comm_deckStack_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_deckStack_stackPile hdisj h₁ h₂
      | pilePile c' b' =>
          have hcomp := commute_of_compsDisjoint st (Move.deckStack c) (Move.pilePile c' b') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps] at hx
            | foundations => simp [Move.comps]
            | hidden => simp [Move.comps] at hx
            | stock => simp [Move.comps])
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
  | pileStack c =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.pileStack c) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_pileStack (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' => exact (comm_deckPile_pileStack (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckStack c' => exact (comm_deckStack_pileStack (disjointTouch_symm hdisj) h₂ h₁).symm
      | pileStack c' => exact comm_pileStack_pileStack hdisj h₁ h₂
      | stackPile c' b' => exact comm_pileStack_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_pileStack_pilePile hdisj h₁ h₂
  | stackPile c b =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.stackPile c b) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' => exact (comm_deckPile_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckStack c' => exact (comm_deckStack_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | pileStack c' => exact (comm_pileStack_stackPile (disjointTouch_symm hdisj) h₂ h₁).symm
      | stackPile c' b' => exact comm_stackPile_stackPile hdisj h₁ h₂
      | pilePile c' b' => exact comm_stackPile_pilePile hdisj h₁ h₂
  | pilePile c b =>
      cases m' with
      | draw =>
          have hcomp := deal_commutes_nonStock st (Move.pilePile c b) (hnc.2 rfl)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | reveal c' => exact (comm_reveal_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckPile c' b' => exact (comm_deckPile_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | deckStack c' =>
          have hcomp := commute_of_compsDisjoint st (Move.pilePile c b) (Move.deckStack c') (by
            intro x hx
            cases x with
            | tableau => simp [Move.comps]
            | foundations => simp [Move.comps] at hx
            | hidden => simp [Move.comps] at hx
            | stock => simp [Move.comps] at hx)
          exact Option.some.inj (h₁.symm.trans (hcomp.trans h₂))
      | pileStack c' => exact (comm_pileStack_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | stackPile c' b' => exact (comm_stackPile_pilePile (disjointTouch_symm hdisj) h₂ h₁).symm
      | pilePile c' b' => exact comm_pilePile_pilePile hdisj h₁ h₂

/-! ### The Draw-commitment commutation kit

`applyDrawTo`'s stock op normalizes to `⟨removeIdx cards i, i⟩`
(`removeAt_drawTo`); the *second* draw of each order finds its card at
the first-occurrence position of the spliced list (`posOf_removeIdx_shift`
for a card after the splice, `..._keep` for one before it); the board
part is two `attach`es at distinct bases (`attach_attach_comm`). -/

/-- Splicing out an earlier position shifts a later first occurrence
down by one. -/
theorem findFirstIdx_removeIdx_shift {α : Type} (p : α → Bool) :
    ∀ (l : List α) (q r : Nat), Cycle.findFirstIdx p l = some r → q < r →
      Cycle.findFirstIdx p (Cycle.removeIdx l q) = some (r - 1) := by
  intro l
  induction l with
  | nil =>
      intro q r h _
      exact absurd h (by simp [Cycle.findFirstIdx])
  | cons a t ih =>
      intro q r h hqr
      have hc : (if p a then some 0 else (Cycle.findFirstIdx p t).map Nat.succ) = some r := h
      by_cases hpa : p a = true
      · rw [if_pos hpa, Option.some.injEq] at hc
        exact absurd hqr (by omega)
      · rw [if_neg hpa] at hc
        cases q with
        | zero =>
            rw [Cycle.removeIdx_zero]
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            rw [hr']
            exact congrArg some (by omega)
        | succ q' =>
            rw [Cycle.removeIdx_succ]
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            have hih := ih q' r' hr' (by omega)
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some (r - 1)
            rw [if_neg hpa, hih, Option.map_some]
            exact congrArg some (by omega)

/-- Splicing out a later position leaves an earlier first occurrence
where it was. -/
theorem findFirstIdx_removeIdx_keep {α : Type} (p : α → Bool) :
    ∀ (l : List α) (p₀ q : Nat), Cycle.findFirstIdx p l = some p₀ → p₀ < q →
      Cycle.findFirstIdx p (Cycle.removeIdx l q) = some p₀ := by
  intro l
  induction l with
  | nil =>
      intro p₀ q h _
      exact absurd h (by simp [Cycle.findFirstIdx])
  | cons a t ih =>
      intro p₀ q h hpq
      have hc : (if p a then some 0 else (Cycle.findFirstIdx p t).map Nat.succ) = some p₀ := h
      cases q with
      | zero => exact absurd hpq (by omega)
      | succ q' =>
          rw [Cycle.removeIdx_succ]
          by_cases hpa : p a = true
          · rw [if_pos hpa, Option.some.injEq] at hc
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some p₀
            rw [if_pos hpa, ← hc]
          · rw [if_neg hpa] at hc
            obtain ⟨r', hr', hrr⟩ := Option.map_eq_some_iff.mp hc
            have hih := ih r' q' hr' (by omega)
            show (if p a then some 0
              else (Cycle.findFirstIdx p (Cycle.removeIdx t q')).map Nat.succ) = some p₀
            rw [if_neg hpa, hih, Option.map_some]
            exact congrArg some (by omega)

/-- The shift lemma, `posOf` packaging (the cursor is never read). -/
theorem posOf_removeIdx_shift {x : Card} {l : List Card} {cur cur' : Nat} {q r : Nat}
    (h : Cycle.posOf x ⟨l, cur⟩ = some r) (hqr : q < r) :
    Cycle.posOf x ⟨Cycle.removeIdx l q, cur'⟩ = some (r - 1) :=
  findFirstIdx_removeIdx_shift _ l q r h hqr

/-- The keep lemma, `posOf` packaging (the cursor is never read). -/
theorem posOf_removeIdx_keep {x : Card} {l : List Card} {cur cur' : Nat} {p q : Nat}
    (h : Cycle.posOf x ⟨l, cur⟩ = some p) (hpq : p < q) :
    Cycle.posOf x ⟨Cycle.removeIdx l q, cur'⟩ = some p :=
  findFirstIdx_removeIdx_keep _ l p q h hpq

/-- The Draw-commitment's stock successor: jump past `i`, splice `i`
out — the cursor lands exactly on `i`. -/
theorem removeAt_drawTo {α : Type} (i : Nat) (cy : Cycle α) :
    (cy.drawTo i).removeAt i = { cards := Cycle.removeIdx cy.cards i, cursor := i } := by
  simp only [Cycle.removeAt, Cycle.drawTo]
  rw [if_pos (Nat.lt_succ_self i), Nat.add_sub_cancel]

/-- A successful Draw commitment's shape: the guard's index, the
board attach, and the successor with the spliced stock. -/
theorem applyDrawTo_eq {st : State} {c : Card} {b : Base} {s' : State}
    (h : st.applyDrawTo c b = some s') :
    ∃ i bd, st.reachablePos c = some i ∧ st.board.attach b c = some bd ∧
      s' = { st with
             board := bd,
             stock := { cards := Cycle.removeIdx st.stock.cards i, cursor := i } } := by
  simp only [State.applyDrawTo] at h
  cases hr : st.reachablePos c with
  | none => rw [hr] at h; simp at h
  | some i =>
      rw [hr] at h
      cases ha : st.board.attach b c with
      | none => rw [ha] at h; simp at h
      | some bd =>
          rw [ha] at h
          simp at h
          refine ⟨i, bd, rfl, rfl, ?_⟩
          rw [← h, removeAt_drawTo]

/-- The guard's index is the plain stock position. -/
theorem reachablePos_posOf {st : State} {c : Card} {i : Nat}
    (h : st.reachablePos c = some i) : st.stock.posOf c = some i := by
  simp only [State.reachablePos] at h
  split at h
  · next hpos =>
      cases hp : st.stock.posOf c with
      | none => rw [hp] at h; simp at h
      | some i' =>
          rw [hp] at h
          simp at h
          rw [h.2]
  · simp at h

/-- The guard's index is in the accessible set. -/
theorem reachablePos_mask {st : State} {c : Card} {i : Nat} (hpos : 0 < st.drawStep)
    (h : st.reachablePos c = some i) :
    i ∈ Pace.maskPos st.stock st.drawStep hpos := by
  simp only [State.reachablePos, dif_pos hpos] at h
  cases hp : st.stock.posOf c with
  | none => rw [hp] at h; simp at h
  | some i' =>
      rw [hp] at h
      simp at h
      rw [h.2] at h
      exact h.1

/-- Two attachments at distinct bases commute. -/
theorem attach_attach_comm {bd : Board} {b b' : Base} {c c' : Card}
    {bd₁ bd₂ bd₃ bd₄ : Board} (hbb : b ≠ b')
    (h₁ : bd.attach b c = some bd₁) (h₂ : bd₁.attach b' c' = some bd₂)
    (h₃ : bd.attach b' c' = some bd₃) (h₄ : bd₃.attach b c = some bd₄) :
    bd₂ = bd₄ := by
  refine Board.ext_topOf (funext (fun x => ?_))
  by_cases hxb : x = b
  · rw [hxb, Board.attach_topOf_ne _ _ _ h₂ hbb, Board.attach_topOf _ _ _ h₁,
      Board.attach_topOf _ _ _ h₄]
  · by_cases hxb' : x = b'
    · rw [hxb', Board.attach_topOf _ _ _ h₂, Board.attach_topOf_ne _ _ _ h₄ (Ne.symm hbb),
        Board.attach_topOf _ _ _ h₃]
    · rw [Board.attach_topOf_ne _ _ _ h₂ hxb', Board.attach_topOf_ne _ _ _ h₁ hxb,
        Board.attach_topOf_ne _ _ _ h₄ hxb, Board.attach_topOf_ne _ _ _ h₃ hxb']

/-- At a saturated cursor (`cursor = length ≥ 2`) with a paced step
(`≥ 2`), position 0 is not accessible: every lane starts strictly
above 0. -/
theorem zero_notMem_maskPos {α : Type} {c : Cycle α} {step : Nat} (hstep : 0 < step)
    (h2 : 2 ≤ step) (hn : 2 ≤ c.cards.length) (hsat : c.cursor = c.cards.length) :
    0 ∉ Pace.maskPos c step hstep := by
  intro hmem
  have hmem' : 0 ∈ (Pace.laneUp step hstep
        (if c.cursor = 0 then step - 1 else c.cursor - 1) (c.cards.length - 1)
      ++ (if 0 < c.cards.length then [c.cards.length - 1] else [])
      ++ Pace.laneUp step hstep (step - 1)
        ((if c.cursor % step != 0 then c.cards.length else c.cursor) - 1)) := hmem
  simp only [List.mem_append] at hmem'
  rw [if_pos (by omega : 0 < c.cards.length), List.mem_singleton] at hmem'
  cases hmem' with
  | inl hmem'' =>
      cases hmem'' with
      | inl h1 =>
          obtain ⟨hle, -, -⟩ := (Pace.laneUp_mem step hstep _ _ 0).mp h1
          rw [hsat] at hle
          split at hle <;> omega
      | inr h01 => omega
  | inr h3 =>
      obtain ⟨hle, -, -⟩ := (Pace.laneUp_mem step hstep _ _ 0).mp h3
      omega

/-- **C13, generalized**: Draw-commitments at cycle-adjacent positions
commute (adjacency modulo the cycle length — the wrap counts), in the
paced game (`2 ≤ drawStep`).

STATEMENT REPAIR (2026-09-13, prover-confirmed): at step 1 the wrap
case (`i + 1 = len`, `j = 0`) is FALSE for `len ≥ 3` — the free-set
degeneration makes both orders legal and they land on different
cursors (`j` vs `len - 2`; witness: cards `[A,B,C]`, cursor 0, empty
board, `c` at 2, `c'` at 0 — end cursors 0 vs 1; the C-IND measurement's
`distinct` residual class).  The step guard is the minimal repair: with
it the wrap case at `len ≥ 3` is unreachable (order 1's second draw
would need position 0 in the mask of a saturated cursor —
`zero_notMem_maskPos`), and at `len = 2` both orders end at cursor 0
with the same (empty) splice. -/
theorem drawTo_comm_modAdjacent {st : State} {c c' : Card} {b b' : Base} {i j len : Nat}
    (hlen : st.stock.cards.length = len) (hadj : (i + 1) % len = j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') (hstep : 2 ≤ st.drawStep) {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ = st₄ := by
  have hilt : i < len := by rw [← hlen]; exact Cycle.posOf_lt hic
  obtain ⟨s₁, hA, hB⟩ := Option.bind_eq_some_iff.mp h₂
  obtain ⟨s₃, hC, hD⟩ := Option.bind_eq_some_iff.mp h₄
  obtain ⟨i₀, bd₁, hr₀, ha₁, hs₁⟩ := applyDrawTo_eq hA
  obtain ⟨k, bd₂, hrk, ha₂, hs₂⟩ := applyDrawTo_eq hB
  obtain ⟨j₀, bd₃, hr₁, ha₃, hs₃⟩ := applyDrawTo_eq hC
  obtain ⟨k', bd₄, hrk', ha₄, hs₄⟩ := applyDrawTo_eq hD
  have hi₀ : i₀ = i := Option.some.inj ((reachablePos_posOf hr₀).symm.trans hic)
  have hj₀ : j₀ = j := Option.some.inj ((reachablePos_posOf hr₁).symm.trans hjc)
  rw [hi₀] at hs₁
  rw [hj₀] at hs₃
  have hs₁s : s₁.stock = { cards := Cycle.removeIdx st.stock.cards i, cursor := i } := by
    rw [hs₁]; try rfl
  have hs₃s : s₃.stock = { cards := Cycle.removeIdx st.stock.cards j, cursor := j } := by
    rw [hs₃]; try rfl
  have hb₁ : s₁.board = bd₁ := by rw [hs₁]; try rfl
  have hb₃ : s₃.board = bd₃ := by rw [hs₃]; try rfl
  rw [hb₁] at ha₂
  rw [hb₃] at ha₄
  have hpk : s₁.stock.posOf c' = some k := reachablePos_posOf hrk
  rw [hs₁s] at hpk
  have hpk' : s₃.stock.posOf c = some k' := reachablePos_posOf hrk'
  rw [hs₃s] at hpk'
  by_cases hlt : i + 1 < len
  · -- non-wrap: j = i + 1 — both orders' second draws land on position i
    have hj1 : j = i + 1 := by rw [← hadj, Nat.mod_eq_of_lt hlt]
    have hk : k = j - 1 :=
      Option.some.inj (hpk.symm.trans (posOf_removeIdx_shift hjc (by omega)))
    have hk' : k' = i :=
      Option.some.inj (hpk'.symm.trans (posOf_removeIdx_keep hic (by omega)))
    have hbd : bd₂ = bd₄ := attach_attach_comm hbb ha₁ ha₂ ha₃ ha₄
    have hcomp₂ : st₂ = { st with
        board := bd₂,
        stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k, cursor := k } } := by
      rw [hs₂, hs₁]; try rfl
    have hcomp₄ : st₄ = { st with
        board := bd₄,
        stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k',
                   cursor := k' } } := by
      rw [hs₄, hs₃]; try rfl
    rw [hcomp₂, hcomp₄, hbd]
    have hcards : Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k
        = Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k' := by
      rw [show k = i from by omega, show k' = i from by omega, hj1]
      exact Cycle.removeIdx_comm st.stock.cards i i (Nat.le_refl i) (by rw [hlen]; exact hlt)
    rw [hcards, show k = k' from by omega]
  · -- wrap: i + 1 = len, j = 0
    have hlen1 : i + 1 = len := by omega
    have hj0 : j = 0 := by rw [← hadj, hlen1, Nat.mod_self]
    rcases (by omega : len = 1 ∨ len = 2 ∨ 3 ≤ len) with h1 | h2 | h3
    · -- len = 1: the successor stock is empty — the second draw dies at posOf
      have hi0' : i = 0 := by omega
      have h0 : 0 < st.stock.cards.length := by rw [hlen]; omega
      have hrlen := Cycle.removeIdx_length st.stock.cards 0 h0
      have hnil : Cycle.removeIdx st.stock.cards 0 = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      rw [hi0'] at hpk
      rw [hnil] at hpk
      have hnone : ({ cards := ([] : List Card), cursor := 0 } : Cycle Card).posOf c' = none :=
        Cycle.posOf_eq_none (by simp)
      rw [hnone] at hpk
      exact absurd hpk (by simp)
    · -- len = 2: both orders end at cursor 0 over the same (empty) splice
      have hk : k = 0 := by
        have hkeep : Cycle.posOf c' ⟨Cycle.removeIdx st.stock.cards i, i⟩ = some j :=
          posOf_removeIdx_keep hjc (by omega)
        have := Option.some.inj (hpk.symm.trans hkeep)
        omega
      have hk' : k' = 0 := by
        have hshift : Cycle.posOf c ⟨Cycle.removeIdx st.stock.cards j, j⟩ = some (i - 1) :=
          posOf_removeIdx_shift hic (by omega)
        have := Option.some.inj (hpk'.symm.trans hshift)
        omega
      have hbd : bd₂ = bd₄ := attach_attach_comm hbb ha₁ ha₂ ha₃ ha₄
      have hcomp₂ : st₂ = { st with
          board := bd₂,
          stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k, cursor := k } } := by
        rw [hs₂, hs₁]; try rfl
      have hcomp₄ : st₄ = { st with
          board := bd₄,
          stock := { cards := Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k',
                     cursor := k' } } := by
        rw [hs₄, hs₃]; try rfl
      rw [hcomp₂, hcomp₄, hbd]
      have hcards : Cycle.removeIdx (Cycle.removeIdx st.stock.cards i) k
          = Cycle.removeIdx (Cycle.removeIdx st.stock.cards j) k' := by
        rw [show i = 1 from by omega, hj0, hk, hk']
        exact (Cycle.removeIdx_comm st.stock.cards 0 0 (Nat.le_refl 0) (by rw [hlen]; omega)).symm
      rw [hcards, hk, hk']
    · -- len ≥ 3: order 1's second draw needs position 0 in the mask of a
      -- saturated cursor — unreachable at step ≥ 2
      have hk0 : k = 0 := by
        have hkeep : Cycle.posOf c' ⟨Cycle.removeIdx st.stock.cards i, i⟩ = some j :=
          posOf_removeIdx_keep hjc (by omega)
        have := Option.some.inj (hpk.symm.trans hkeep)
        omega
      have hsd : s₁.drawStep = st.drawStep := by rw [hs₁]; try rfl
      have hmem := reachablePos_mask (by rw [hsd]; omega : 0 < s₁.drawStep) hrk
      rw [hs₁s] at hmem
      rw [hk0, hj0] at hmem
      have hrlen : (Cycle.removeIdx st.stock.cards i).length = i := by
        have h0 : i < st.stock.cards.length := by rw [hlen]; exact hilt
        have := Cycle.removeIdx_length st.stock.cards i h0
        omega
      exact absurd hmem (zero_notMem_maskPos (by omega : 0 < s₁.drawStep) (by omega : 2 ≤ s₁.drawStep)
        (by rw [hrlen]; omega : 2 ≤ (Cycle.removeIdx st.stock.cards i).length)
        (by rw [hrlen] : i = (Cycle.removeIdx st.stock.cards i).length))

/-- **C13's boundary**: non-adjacent Draw-commitments land on different
cursors — the end states differ (the cards agree, by `removeIdx_comm`;
only the cursor position diverges: `j - 1` vs `i`).  The engine's
sweep/canonicalization is what recovers commutation beyond adjacency —
the C-IND landscape's residual. -/
theorem drawTo_nonadjacent_diverge {st : State} {c c' : Card} {b b' : Base} {i j : Nat}
    (hij : i < j) (hne : i + 1 ≠ j)
    (hic : st.stock.posOf c = some i) (hjc : st.stock.posOf c' = some j)
    (hbb : b ≠ b') {st₂ st₄ : State}
    (h₂ : (st.applyDrawTo c b >>= fun s => s.applyDrawTo c' b') = some st₂)
    (h₄ : (st.applyDrawTo c' b' >>= fun s => s.applyDrawTo c b) = some st₄) :
    st₂ ≠ st₄ := by
  have := hbb
  obtain ⟨s₁, hA, hB⟩ := Option.bind_eq_some_iff.mp h₂
  obtain ⟨s₃, hC, hD⟩ := Option.bind_eq_some_iff.mp h₄
  obtain ⟨i₀, bd₁, hr₀, -, hs₁⟩ := applyDrawTo_eq hA
  obtain ⟨k, bd₂, hrk, -, hs₂⟩ := applyDrawTo_eq hB
  obtain ⟨j₀, bd₃, hr₁, -, hs₃⟩ := applyDrawTo_eq hC
  obtain ⟨k', bd₄, hrk', -, hs₄⟩ := applyDrawTo_eq hD
  have hi₀ : i₀ = i := Option.some.inj ((reachablePos_posOf hr₀).symm.trans hic)
  have hj₀ : j₀ = j := Option.some.inj ((reachablePos_posOf hr₁).symm.trans hjc)
  rw [hi₀] at hs₁
  rw [hj₀] at hs₃
  have hs₁s : s₁.stock = { cards := Cycle.removeIdx st.stock.cards i, cursor := i } := by
    rw [hs₁]; try rfl
  have hs₃s : s₃.stock = { cards := Cycle.removeIdx st.stock.cards j, cursor := j } := by
    rw [hs₃]; try rfl
  have hpk : s₁.stock.posOf c' = some k := reachablePos_posOf hrk
  rw [hs₁s] at hpk
  have hpk' : s₃.stock.posOf c = some k' := reachablePos_posOf hrk'
  rw [hs₃s] at hpk'
  have hk : k = j - 1 := Option.some.inj (hpk.symm.trans (posOf_removeIdx_shift hjc hij))
  have hk' : k' = i := Option.some.inj (hpk'.symm.trans (posOf_removeIdx_keep hic hij))
  have hc₂ : st₂.stock.cursor = j - 1 := by
    rw [hs₂]
    show k = j - 1
    exact hk
  have hc₄ : st₄.stock.cursor = i := by
    rw [hs₄]
    show k' = i
    exact hk'
  intro hcon
  have hcur : st₂.stock.cursor = st₄.stock.cursor := by rw [hcon]
  rw [hc₂, hc₄] at hcur
  omega

