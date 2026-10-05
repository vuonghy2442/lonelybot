/- MidAccessDraft.lean -- the wave-19 DRAFT of the mid_access_of_noSeat
- reduction (Klondike/TwinSwapCompletion.lean).  NOT part of the build:
- the lakefile Klondike glob does not include attic/ and nothing imports
- this file.  Parked here by the wave-19 session so the successor can
- resume from the drafted machinery; reinstate INTO TwinSwapCompletion.lean,
- fix the remaining elaboration errors (~25, all local: literal-projection
- show orientations, a few rw-directions in the mirrors, the walk lemma
- beta-case show casts), then git rm this file.
/-- The take-mono list lemma (kept local to avoid core-name
collisions). -/
private theorem take_subset_mono {α : Type} : ∀ (m n : Nat), m ≤ n →
    ∀ (l : List α), l.take m ⊆ l.take n := by
  intro m n h l
  induction l generalizing m n with
  | nil => simp
  | cons x ls ih =>
      cases m with
      | zero => simp
      | succ m' =>
          cases n with
          | zero => omega
          | succ n' =>
              show x :: ls.take m' ⊆ x :: ls.take n'
              intro r hr
              simp only [List.mem_cons] at hr
              rcases hr with rfl | hr
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih m' n' (by omega) hr)

private theorem hidden_sub_of_deal {S A : State} {a : Anchor}
    (hdeal : S.deal = A.deal) (hle : S.depths a ≤ A.depths a) :
    S.hidden a ⊆ A.hidden a := by
  intro r hr
  have h1 : r ∈ (S.deal.piles a).take (S.depths a) := hr
  have h2 : r ∈ (A.deal.piles a).take (A.depths a) := by
    rw [← hdeal]
    exact take_subset_mono _ _ hle (S.deal.piles a) h1
  exact h2

/-- The replay pair's delta, carried by the induction: the A-side
state still has the twin seated at `β` (its own seat bare), the
B-side state is the fired image — the boards agree on every cell
but `β`, the heights on every suit but the twin's own, and the deal,
depths, stock and draw step are literally equal.  Slot order (= the
anonymous constructor's positions): `topOf β = some t`,
`topOf β = none` (B), cell-agreement off `β`, `bottomOf t = some β`,
`topOf (inr t) = none`, `bottomOf`-agreement off the twin,
deal/depths/stock equality, `S'.heights t.suit = S.heights t.suit + 1`,
heights-agreement off the twin's suit, draw step equality. -/
private def TwinReplayTrace (t : Card) (β : Base) (S S' : State) : Prop :=
  S.board.topOf β = some t ∧
  S'.board.topOf β = none ∧
  (∀ b, b ≠ β → S.board.topOf b = S'.board.topOf b) ∧
  S.board.bottomOf t = some β ∧
  S.board.topOf (Sum.inr t) = none ∧
  (∀ c, c ≠ t → S.board.bottomOf c = S'.board.bottomOf c) ∧
  S.deal = S'.deal ∧
  S.depths = S'.depths ∧
  S.stock = S'.stock ∧
  S'.heights t.suit = S.heights t.suit + 1 ∧
  (∀ s, s ≠ t.suit → S.heights s = S'.heights s) ∧
  S.drawStep = S'.drawStep

/-- Detach keeps every other card's holder (the twin's cell is the
only one written). -/
private theorem bottomOf_detach_of_ne {S : State} {β : Base} {c t : Card}
    (hbotT : S.board.topOf β = some t) (hc : c ≠ t) :
    (S.board.detach β).bottomOf c = S.board.bottomOf c := by
  cases hb : S.board.bottomOf c with
  | none =>
      refine (Board.bottomOf_eq_none _ _).mpr (fun b hb' => ?_)
      by_cases hbb : b = β
      · rw [hbb, Board.detach_topOf] at hb'; exact absurd hb' (by simp)
      · rw [Board.detach_topOf_ne _ _ _ hbb] at hb'
        exact ((Board.bottomOf_eq_none _ _).mp hb) b hb'
  | some b₁ =>
      have hb₁ : S.board.topOf b₁ = some c := (Board.bottomOf_eq _ _ _).mp hb
      have hne : b₁ ≠ β := by
        intro hcon; rw [hcon] at hb₁
        rw [hbotT] at hb₁
        exact absurd (Option.some.inj hb₁) (fun hcc => hc hcc.symm)
      exact (Board.bottomOf_eq _ _ b₁).mpr
        (by rw [Board.detach_topOf_ne _ _ _ hne]; exact hb₁)

/-- Cell agreement outside `β` transfers every non-twin card's holder
across the fired pair (the successor pack's `bottomOf` slot). -/
private theorem bottomOf_cell_transfer {bdA bdB : Board} {β : Base} {t c : Card}
    (hc : c ≠ t)
    (hβA : bdA.topOf β = some t) (hβB : bdB.topOf β = none)
    (hcells : ∀ x, x ≠ β → bdA.topOf x = bdB.topOf x) :
    bdA.bottomOf c = bdB.bottomOf c := by
  cases hb : bdA.bottomOf c with
  | none =>
      refine (((Board.bottomOf_eq_none _ _).mpr (fun x hx => ?_)).symm)
      by_cases hxx : x = β
      · rw [hxx, hβB] at hx; exact absurd hx (by simp)
      · rw [← hcells x hxx] at hx
        exact ((Board.bottomOf_eq_none _ _).mp hb) x hx
  | some b₁ =>
      have hb₁ : bdA.topOf b₁ = some c := (Board.bottomOf_eq _ _ _).mp hb
      have hne : b₁ ≠ β := by
        intro hcon; rw [hcon] at hb₁
        rw [hβA] at hb₁
        exact absurd (Option.some.inj hb₁) (fun hcc => hc hcc.symm)
      exact ((Board.bottomOf_eq _ _ b₁).mpr (by rw [← hcells b₁ hne]; exact hb₁)).symm

/-- The base case: the twin's own firing sets the delta. -/
private theorem twinReplayTrace_of_firing {t : Card} {β : Base} {S B : State}
    (hfire : S.apply (Move.pileStack t) = some B)
    (hβ : S.board.bottomOf t = some β) :
    TwinReplayTrace t β S B := by
  rw [apply_pileStack_iff] at hfire
  obtain ⟨htop, b₀, hb₀, -, hshape⟩ := hfire
  have hbotT : S.board.topOf β = some t := (Board.bottomOf_eq S.board t β).mp hβ
  have hβb : β = b₀ := (Option.some.inj (hb₀.symm.trans hβ)).symm
  subst hβb
  refine ⟨hbotT, ?_, ?_, hβ, htop, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hshape]
    exact Board.detach_topOf S.board β
  · intro b hbb2
    rw [hshape]
    exact (Board.detach_topOf_ne S.board β b hbb2).symm
  · intro c hc
    rw [hshape]
    exact (bottomOf_detach_of_ne hbotT hc).symm
  · rw [hshape]; try rfl
  · rw [hshape]; try rfl
  · rw [hshape]; try rfl
  · rw [hshape]
    show (if t.suit = t.suit then S.heights t.suit + 1 else S.heights t.suit) = _
    rw [ite_eq_left rfl]
  · intro s hs
    rw [hshape]
    show S.heights s = (if s = t.suit then S.heights s + 1 else S.heights s)
    rw [ite_eq_right hs]
  · rw [hshape]; try rfl

/-- The t-suit rung is untouched by every twinMid move (the three
foundation kinds are suit-gated off the twin's suit by `twinMid`;
everything else does not read heights at all). -/
private theorem heights_tSuit_stable {t : Card} {m : Move} {S S₁ : State}
    (hm : Move.twinMid t m = true) (hfire : S.apply m = some S₁) :
    S₁.heights t.suit = S.heights t.suit := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hfire
      rw [hfire]
  | reveal a =>
      rw [apply_reveal_iff] at hfire
      obtain ⟨r, bd, -, -, -, hshape⟩ := hfire
      rw [hshape]
  | deckPile c b =>
      rw [apply_deckPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]
  | deckStack c =>
      obtain ⟨hsu, -⟩ := (Move.twinMid_deckStack t c).mp hm
      rw [apply_deckStack_iff] at hfire
      obtain ⟨-, -, hshape⟩ := hfire
      rw [hshape]
      show (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) = _
      rw [ite_eq_right (fun h => hsu h.symm)]
  | pileStack c =>
      obtain ⟨hsu, -⟩ := (Move.twinMid_pileStack t c).mp hm
      rw [apply_pileStack_iff] at hfire
      obtain ⟨-, b₀, -, -, hshape⟩ := hfire
      rw [hshape]
      show (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) = _
      rw [ite_eq_right (fun h => hsu h.symm)]
  | stackPile c b =>
      obtain ⟨hsu, -⟩ := (Move.twinMid_stackPile t c b).mp hm
      rw [apply_stackPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]
      show (if t.suit = c.suit then S.heights t.suit - 1 else S.heights t.suit) = _
      rw [ite_eq_right (fun h => hsu h.symm)]
  | pilePile c b =>
      rw [apply_pilePile_iff] at hfire
      obtain ⟨b₀, -, -, -, bd, -, hshape⟩ := hfire
      rw [hshape]

/-- No move re-deals; reveals only shrink the hidden depth. -/
private theorem deal_stable_move {S S₁ : State} {m : Move}
    (hfire : S.apply m = some S₁) : S.deal = S₁.deal := by
  cases m with
  | draw =>
      rw [apply_draw_iff] at hfire
      rw [hfire]; try rfl
  | reveal a =>
      rw [apply_reveal_iff] at hfire
      obtain ⟨r, bd, -, -, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | deckPile c b =>
      rw [apply_deckPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | deckStack c =>
      rw [apply_deckStack_iff] at hfire
      obtain ⟨-, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | pileStack c =>
      rw [apply_pileStack_iff] at hfire
      obtain ⟨-, b₀, -, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | stackPile c b =>
      rw [apply_stackPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; try rfl
  | pilePile c b =>
      rw [apply_pilePile_iff] at hfire
      obtain ⟨b₀, -, -, -, bd, -, hshape⟩ := hfire
      rw [hshape]; try rfl

private theorem depths_mono_move {S S₁ : State} {m : Move}
    (hfire : S.apply m = some S₁) : ∀ a, S₁.depths a ≤ S.depths a := by
  intro a
  cases m with
  | draw =>
      rw [apply_draw_iff] at hfire
      rw [hfire]; exact Nat.le_refl _
  | reveal a' =>
      rw [apply_reveal_iff] at hfire
      obtain ⟨r, bd, -, -, -, hshape⟩ := hfire
      have hdeq : S₁.depths = fun x => if x = a' then S.depths x - 1
          else S.depths x := by rw [hshape]; rfl
      rw [hdeq]
      show (if a = a' then S.depths a - 1 else S.depths a) ≤ S.depths a
      by_cases h : a = a'
      · rw [ite_eq_left h]; omega
      · rw [ite_eq_right h]; exact Nat.le_refl _
  | deckPile c b =>
      rw [apply_deckPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | deckStack c =>
      rw [apply_deckStack_iff] at hfire
      obtain ⟨-, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | pileStack c =>
      rw [apply_pileStack_iff] at hfire
      obtain ⟨-, b₀, -, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | stackPile c b =>
      rw [apply_stackPile_iff] at hfire
      obtain ⟨-, -, bd, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _
  | pilePile c b =>
      rw [apply_pilePile_iff] at hfire
      obtain ⟨b₀, -, -, -, bd, -, hshape⟩ := hfire
      rw [hshape]; exact Nat.le_refl _

/-- The reveal's attach base is the anchor of a one-hidden-card pile,
or the seat of a hidden card. -/
private theorem hiddenBase_cases {st : State} (a : Anchor) :
    st.hiddenBase a = Sum.inl a ∨
      (∃ d, st.hiddenBase a = Sum.inr d ∧ d ∈ st.hidden a) := by
  unfold State.hiddenBase
  cases h : ((st.hidden a).reverse.drop 1).head? with
  | none => exact Or.inl rfl
  | some d =>
      exact Or.inr ⟨d, rfl, List.mem_reverse.mp (List.drop_subset 1 _ (mem_of_head? h))⟩

/-- **The walk delta** (the `pilePile` self-landing transfer's back):
over the fired pair, the A-side run above a card is the B-side run,
or the twin consed on top of it (the A-walk reads the twin's cell,
gains `t`, and stops — the twin's own seat is bare — the guard reads
see a card already accumulated exactly when the walk would have
looped). -/
private theorem aboveOf_twin_delta {t : Card} {β : Base} {S S' : State}
    (hdp : TwinReplayTrace t β S S') (z : Card) :
    S.board.aboveOf z = S'.board.aboveOf z ∨
      S.board.aboveOf z = t :: S'.board.aboveOf z := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, -, -, -, -, -, -, -⟩ := hdp
  have main : ∀ (n : Nat) (b : Base) (acc : List Card),
      Board.aboveOf.go S.board n b acc = Board.aboveOf.go S'.board n b acc ∨
        ∃ acc', Board.aboveOf.go S.board n b acc = t :: acc' ∧
          Board.aboveOf.go S'.board n b acc = acc' := by
    intro n
    induction n with
    | zero => intro b acc; exact Or.inl rfl
    | succ n ih =>
        intro b acc
        by_cases hbb : b = β
        · subst hbb
          by_cases hcon : acc.contains t = true
          · rw [aboveOf_go_succ S.board, hβA]
            refine Or.inl ?_
            show (if acc.contains t = true then acc
                else Board.aboveOf.go S.board n (Sum.inr t) (t :: acc)) = acc
            rw [ite_eq_left hcon]
          · rw [aboveOf_go_succ S.board, aboveOf_go_succ S'.board, hβA, hβB]
            refine Or.inr ⟨acc, ?_, ?_⟩
            · show (if acc.contains t = true then acc
                else Board.aboveOf.go S.board n (Sum.inr t) (t :: acc)) = t :: acc
              rw [ite_eq_right hcon]
              cases n with
              | zero => rfl
              | succ n' =>
                  show Board.aboveOf.go S.board n (Sum.inr t) (t :: acc) = t :: acc
                  rw [aboveOf_go_succ S.board, hseatt]
                  rfl
            · rfl
        · rw [aboveOf_go_succ S.board, aboveOf_go_succ S'.board, hcells b hbb]
          cases htop : S'.board.topOf b with
          | none => rfl
          | some c =>
              by_cases hcon : acc.contains c = true
              · show (if acc.contains c = true then acc
                  else Board.aboveOf.go S.board n (Sum.inr c) (c :: acc))
                  = (if acc.contains c = true then acc
                    else Board.aboveOf.go S'.board n (Sum.inr c) (c :: acc))
                rw [ite_eq_left hcon, ite_eq_left hcon]
              · show (if acc.contains c = true then acc
                  else Board.aboveOf.go S.board n (Sum.inr c) (c :: acc))
                  = (if acc.contains c = true then acc
                    else Board.aboveOf.go S'.board n (Sum.inr c) (c :: acc))
                rw [ite_eq_right hcon, ite_eq_right hcon]
                exact ih (Sum.inr c) (c :: acc)
  rcases main 53 (Sum.inr z) [] with h | ⟨acc', hA, hB⟩
  · rw [Board.aboveOf_eq_go 53 (by omega), Board.aboveOf_eq_go 53 (by omega)]
    exact Or.inl h
  · rw [← Board.aboveOf_eq_go 53 (by omega)] at hA
    have hB' : S'.board.aboveOf z = acc' := by
      rw [Board.aboveOf_eq_go 53 (by omega)]
      exact hB
    rw [hB']
    exact Or.inr hA

/-! ### The per-kind B→A transfers

Each mirror takes the replay pair (the delta above), the move's
B-side firing (the source play's own mid step), and the move's
local seat exclusions, and concludes the SAME move fires at the
A-side state leaving the pair intact. -/

/-- The `draw` transfer: the draw reads only the stock cursor, which
the twin's firing does not touch. -/
private theorem mid_access_draw {t : Card} {β : Base} {S S' T₁ : State}
    (hdp : TwinReplayTrace t β S S')
    (hfire : S'.apply Move.draw = some T₁) :
    ∃ S₁, S.apply Move.draw = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_draw_iff] at hfire
  obtain rfl := hfire
  have swit : State := { S with stock := S.stock.dealOnce S.drawStep }
  refine ⟨swit, rfl, ?_⟩
  refine ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, ?_, hhβ, hhh,
    hds⟩
  show S.stock.dealOnce S.drawStep = S'.stock.dealOnce S'.drawStep
  rw [hstock, hds]

/-- The `deckStack` transfer: the rung guard reads the moved card's
suit (off the twin's suit by `twinMid`), so the same height answers
on both sides. -/
private theorem mid_access_deckStack {t : Card} {β : Base} {S S' T₁ : State}
    {c : Card}
    (hdp : TwinReplayTrace t β S S')
    (hsu : c.suit ≠ t.suit)
    (hfire : S'.apply (Move.deckStack c) = some T₁) :
    ∃ S₁, S.apply (Move.deckStack c) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_deckStack_iff] at hfire
  obtain ⟨hprev, hrk, rfl⟩ := hfire
  have swit : State := { S with stock := S.stock.removeAt (S.stock.cursor - 1),
      heights := fun s => if s = c.suit then S.heights s + 1 else S.heights s }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_deckStack_iff]
    refine ⟨?_, ?_, rfl⟩
    · rw [hstock]; exact hprev
    · rw [hrk, hhh c.suit hsu]
  · refine ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, ?_, ?_, ?_, hds⟩
    · show S.stock.removeAt (S.stock.cursor - 1)
          = S'.stock.removeAt (S'.stock.cursor - 1)
      rw [hstock]
    · show (if t.suit = c.suit then S'.heights t.suit + 1 else S'.heights t.suit)
          = (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) + 1
      rw [ite_eq_right (fun h => hsu h.symm),
        ite_eq_right (fun h => hsu h.symm)]
      exact hhβ
    · intro s hs
      show (if s = c.suit then S.heights s + 1 else S.heights s)
          = (if s = c.suit then S'.heights s + 1 else S'.heights s)
      by_cases hsc : s = c.suit
      · rw [ite_eq_left hsc, ite_eq_left hsc]
        rw [hhh s hs]
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact hhh s hs

/-- The `pileStack` transfer: the raise's seat guard reads its own
cell (`Sum.inr c`, excluded from `β` by the repair — witness A's
corner), and the rung guard reads the off-suit height. -/
private theorem mid_access_pileStack {t : Card} {β : Base} {S S' T₁ : State}
    {c : Card}
    (hdp : TwinReplayTrace t β S S')
    (hsu : c.suit ≠ t.suit)
    (hseat : β ≠ Sum.inr c)
    (hfire : S'.apply (Move.pileStack c) = some T₁) :
    ∃ S₁, S.apply (Move.pileStack c) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβ, hseatt, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_pileStack_iff] at hfire
  obtain ⟨htop', b₀, hbot', hrk', rfl⟩ := hfire
  have hct : c ≠ t := fun h => hsu (congrArg Card.suit h)
  have hbotS : S.board.bottomOf c = some b₀ := by
    rw [hbofs c hct]; exact hbot'
  have hb₀β : b₀ ≠ β := by
    intro hcon
    rw [hcon] at hbotS
    have hthis := (Board.bottomOf_eq S.board c β).mp hbotS
    rw [hβA] at hthis
    exact absurd (Option.some.inj hthis) (fun hcc => hct hcc.symm)
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbotS
    rw [(Board.bottomOf_eq S.board c (Sum.inr t)).mp hbotS] at hseatt
    exact absurd hseatt (by simp)
  have swit : State := { S with board := S.board.detach b₀,
      heights := fun s => if s = c.suit then S.heights s + 1 else S.heights s }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_pileStack_iff]
    refine ⟨?_, b₀, hbotS, ?_, rfl⟩
    · rw [hcells (Sum.inr c) (Ne.symm hseat)]; exact htop'
    · rw [hrk', hhh c.suit hsu]
  · have hcells' : ∀ x, x ≠ β →
        (S.board.detach b₀).topOf x = (S'.board.detach b₀).topOf x := by
      intro x hx
      by_cases hxb₀ : x = b₀
      · rw [hxb₀, Board.detach_topOf, Board.detach_topOf]
      · rw [Board.detach_topOf_ne _ _ _ hxb₀, Board.detach_topOf_ne _ _ _ hxb₀]
        exact hcells x hx
    have hβA' : (S.board.detach b₀).topOf β = some t := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβA
    have hβB' : (S'.board.detach b₀).topOf β = none := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, rfl, ?_, ?_, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.detach_topOf_ne _ _ _ hb₀t]; exact hseatt
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · show (if t.suit = c.suit then S'.heights t.suit + 1 else S'.heights t.suit)
          = (if t.suit = c.suit then S.heights t.suit + 1 else S.heights t.suit) + 1
      rw [ite_eq_right (fun h => hsu h.symm),
        ite_eq_right (fun h => hsu h.symm)]
      exact hhβ
    · intro s hs
      show (if s = c.suit then S.heights s + 1 else S.heights s)
          = (if s = c.suit then S'.heights s + 1 else S'.heights s)
      by_cases hsc : s = c.suit
      · rw [ite_eq_left hsc, ite_eq_left hsc, hhh s hs]
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact hhh s hs

/-- The `deckPile` transfer: the landing cell is off `β` and off the
twin's seat (the no-landing premise), the waste top cannot be the
twin itself (visible at A, off the stock cycle by WF). -/
private theorem mid_access_deckPile {t : Card} {β : Base} {S S' T₁ : State}
    {X : Card} {b : Base}
    (hwf : S.WF)
    (hdp : TwinReplayTrace t β S S')
    (hseatβ : b ≠ β) (hseatt : b ≠ Sum.inr t)
    (hfire : S'.apply (Move.deckPile X b) = some T₁) :
    ∃ S₁, S.apply (Move.deckPile X b) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_deckPile_iff] at hfire
  obtain ⟨hprev, hcp', bd', hatt', rfl⟩ := hfire
  have hXt : X ≠ t := by
    intro hcon
    have hxs : t ∈ S.stock.cards := by
      rw [← hcon, hstock]
      exact Cycle.prev_mem hprev
    have hvt : S.isVis t = true := by
      show (S.board.bottomOf t).isSome = true
      rw [hbotβT]; rfl
    have hpos : S.stock.posOf t = none := hwf.vis_off_cycle t hvt
    exact absurd (Cycle.posOf_ne_none_of_mem hxs) (by rw [hpos]; simp)
  have hbx : S.board.bottomOf X = none := by
    rw [hbofs X hXt]
    exact ((Board.attach_eq_some_iff _ _ _).mp (by rw [hatt']; simp)).2
  have htopb : S.board.topOf b = none := by
    rw [hcells b hseatβ]; exact topOf_of_canPlace hcp'
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨htopb, hbx⟩)
  have swit : State := { S with board := bdA,
      stock := S.stock.removeAt (S.stock.cursor - 1) }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_deckPile_iff]
    refine ⟨?_, ?_, bdA, hattA, rfl⟩
    · rw [hstock]; exact hprev
    · cases b with
      | inl a =>
          have htopb' : S.board.topOf (Sum.inl a) = none := htopb
          exact (canPlace_inl_iff).mpr
            ⟨htopb', ((canPlace_inl_iff).mp hcp').2⟩
      | inr d =>
          have hd : d ≠ t := by
            intro hcon; exact hseatt (congrArg Sum.inr hcon)
          have hvisA : S.isVis d = true := by
            show (S.board.bottomOf d).isSome = true
            rw [hbofs d hd]
            exact ((canPlace_inr_iff).mp hcp').2.1
          exact (canPlace_inr_iff).mpr
            ⟨htopb, hvisA, ((canPlace_inr_iff).mp hcp').2.2⟩
  · have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = b
      · rw [hxb, Board.attach_topOf _ _ _ hattA, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' hxb]
        exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatβ)]; exact hβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' (Ne.symm hseatβ)]; exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, ?_, hhβ, hhh, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatt)]; exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · show S.stock.removeAt (S.stock.cursor - 1)
          = S'.stock.removeAt (S'.stock.cursor - 1)
      rw [hstock]

/-- The `stackPile` transfer (the low-suit worry-back): the un-stack
rung reads the moved card's suit (off the twin's), the landing cell
is off `β` and the twin's seat. -/
private theorem mid_access_stackPile {t : Card} {β : Base} {S S' T₁ : State}
    {c : Card} {b : Base}
    (hdp : TwinReplayTrace t β S S')
    (hsu : c.suit ≠ t.suit)
    (hseatβ : b ≠ β) (hseatt : b ≠ Sum.inr t)
    (hfire : S'.apply (Move.stackPile c b) = some T₁) :
    ∃ S₁, S.apply (Move.stackPile c b) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_stackPile_iff] at hfire
  obtain ⟨hrk', hcp', bd', hatt', rfl⟩ := hfire
  have hct : c ≠ t := fun h => hsu (congrArg Card.suit h)
  have hbc : S.board.bottomOf c = none := by
    rw [hbofs c hct]
    exact ((Board.attach_eq_some_iff _ _ _).mp (by rw [hatt']; simp)).2
  have htopb : S.board.topOf b = none := by
    rw [hcells b hseatβ]; exact topOf_of_canPlace hcp'
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨htopb, hbc⟩)
  have swit : State := { S with board := bdA,
      heights := fun s => if s = c.suit then S.heights s - 1 else S.heights s }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_stackPile_iff]
    refine ⟨?_, ?_, bdA, hattA, rfl⟩
    · rw [hrk', hhh c.suit hsu]
    · cases b with
      | inl a =>
          exact (canPlace_inl_iff).mpr
            ⟨htopb, ((canPlace_inl_iff).mp hcp').2⟩
      | inr d =>
          have hd : d ≠ t := by
            intro hcon; exact hseatt (congrArg Sum.inr hcon)
          have hvisA : S.isVis d = true := by
            show (S.board.bottomOf d).isSome = true
            rw [hbofs d hd]
            exact ((canPlace_inr_iff).mp hcp').2.1
          exact (canPlace_inr_iff).mpr
            ⟨htopb, hvisA, ((canPlace_inr_iff).mp hcp').2.2⟩
  · have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = b
      · rw [hxb, Board.attach_topOf _ _ _ hattA, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' hxb]
        exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatβ)]; exact hβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' (Ne.symm hseatβ)]; exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, rfl, ?_, ?_, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatt)]; exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · show (if t.suit = c.suit then S'.heights t.suit - 1 else S'.heights t.suit)
          = (if t.suit = c.suit then S.heights t.suit - 1 else S.heights t.suit) + 1
      rw [ite_eq_right (fun h => hsu h.symm),
        ite_eq_right (fun h => hsu h.symm)]
      exact hhβ
    · intro s hs
      show (if s = c.suit then S.heights s - 1 else S.heights s)
          = (if s = c.suit then S'.heights s - 1 else S'.heights s)
      by_cases hsc : s = c.suit
      · rw [ite_eq_left hsc, ite_eq_left hsc, hhh s hs]
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact hhh s hs

/-- The `reveal` transfer: the boundary card and the attach cell are
the same deal data on both sides (deal/depths are in the delta), so
only the two board cells matter — the boundary's own seat and the
`hiddenBase` cell — both excluded by the repaired premise. -/
private theorem mid_access_reveal {t : Card} {β : Base} {S S' T₁ : State}
    {a : Anchor}
    (hwf : S.WF)
    (hdp : TwinReplayTrace t β S S')
    (hseatR : ∀ r, S.topHidden a = some r → β ≠ Sum.inr r)
    (hseatB : β ≠ S.hiddenBase a)
    (hfire : S'.apply (Move.reveal a) = some T₁) :
    ∃ S₁, S.apply (Move.reveal a) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_reveal_iff] at hfire
  obtain ⟨r, bd', htopH', hbare', hatt', rfl⟩ := hfire
  have hTH : S.topHidden a = S'.topHidden a := by
    show ((S.deal.piles a).take (S.depths a)).getLast?
      = ((S'.deal.piles a).take (S'.depths a)).getLast?
    rw [hdeal, hdep]
  have htopH : S.topHidden a = some r := by rw [hTH]; exact htopH'
  have hβr : β ≠ Sum.inr r := hseatR r htopH
  have hrs : r ≠ t := by
    intro hcon
    have hvt : S.isVis t = true := by
      show (S.board.bottomOf t).isSome = true
      rw [hbotβT]; rfl
    rw [hcon] at htopH
    exact hwf.vis_not_hidden t hvt a (mem_of_getLast htopH)
  have hfreeR : S.board.topOf (Sum.inr r) = none := by
    rw [hcells (Sum.inr r) (Ne.symm hβr)]; exact hbare'
  have hhid : S.hidden a = S'.hidden a := by
    show (S.deal.piles a).take (S.depths a) = (S'.deal.piles a).take (S'.depths a)
    rw [hdeal, hdep]
  have hbase : S.hiddenBase a = S'.hiddenBase a := by
    unfold State.hiddenBase
    rw [hhid]
  have hguardB := (Board.attach_eq_some_iff _ _ _).mp (by rw [hatt']; simp)
  have hfreeB : S.board.topOf (S.hiddenBase a) = none := by
    rw [hcells (S.hiddenBase a) (Ne.symm hseatB), hbase]
    exact hguardB.1
  have hnewR : S.board.bottomOf r = none := by
    rw [hbofs r hrs]; exact hguardB.2
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨hfreeB, hnewR⟩)
  have swit : State := { S with board := bdA,
      depths := fun a' => if a' = a then S.depths a' - 1 else S.depths a' }
  refine ⟨swit, ?_, ?_⟩
  · rw [apply_reveal_iff]
    exact ⟨r, bdA, htopH, hfreeR, hattA, rfl⟩
  · have hbaseT : S.hiddenBase a ≠ Sum.inr t := by
      intro hcon
      rcases hiddenBase_cases (st := S) a with hbase | ⟨d, hbase, hd⟩
      · rw [hbase] at hcon; exact absurd hcon (by simp)
      · rw [hbase] at hcon
        have hdt : d ≠ t := by
          intro hcd
          have hvt : S.isVis t = true := by
            show (S.board.bottomOf t).isSome = true
            rw [hbotβT]; rfl
          have hmem : t ∈ S.hidden a := by rw [← hcd]; exact hd
          exact hwf.vis_not_hidden t hvt a hmem
        exact absurd (Sum.inr.inj hcon) hdt
    have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = S.hiddenBase a
      · rw [hxb, Board.attach_topOf _ _ _ hattA, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' hxb]
        exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA hseatB]
      exact hβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' hseatB]
      exact hβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, ?_, hstock, hhβ, hhh, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hbaseT)]
      exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'
    · funext a'
      show (if a' = a then S.depths a' - 1 else S.depths a')
          = (if a' = a then S'.depths a' - 1 else S'.depths a')
      rw [hdep]

/-- The `pilePile` transfer: the run head cannot be the twin (the
fired side does not have it), the detach cell is the run head's own
holder, and the self-landing guard transfers through the walk delta
(the A-side run gains at most the twin as its head — `aboveOf_twin_delta`). -/
private theorem mid_access_pilePile {t : Card} {β : Base} {S S' T₁ : State}
    {z : Card} {b : Base}
    (hdp : TwinReplayTrace t β S S')
    (hseatβ : b ≠ β) (hseatt : b ≠ Sum.inr t)
    (hfire : S'.apply (Move.pilePile z b) = some T₁) :
    ∃ S₁, S.apply (Move.pilePile z b) = some S₁ ∧ TwinReplayTrace t β S₁ T₁ := by
  have hdp2 : TwinReplayTrace t β S S' := hdp
  obtain ⟨hβA, hβB, hcells, hbotβT, hseatT, hbofs, hdeal, hdep, hstock, hhβ, hhh,
    hds⟩ := hdp
  rw [apply_pilePile_iff] at hfire
  obtain ⟨b₀, hbot', hne', hcmr', bd', hatt', rfl⟩ := hfire
  have hzt : z ≠ t := by
    intro hcon
    have hnone : S'.board.bottomOf t = none := by
      refine (Board.bottomOf_eq_none _ _).mpr (fun x hx => ?_)
      by_cases hxb : x = β
      · rw [hxb, hβB] at hx; exact absurd hx (by simp)
      · rw [← hcells x hxb] at hx
        have hbx2 : S.board.bottomOf t = some x := (Board.bottomOf_eq _ _ _).mp hx
        rw [hbotβT] at hbx2
        exact absurd (Option.some.inj hbx2) hxb
    rw [hcon, hnone] at hbot'
    exact absurd hbot' (by simp)
  have hbotS : S.board.bottomOf z = some b₀ := by
    rw [hbofs z hzt]; exact hbot'
  have hb₀β : b₀ ≠ β := by
    intro hcon
    rw [hcon] at hbotS
    have hthis := (Board.bottomOf_eq S.board z β).mp hbotS
    rw [hβA] at hthis
    exact absurd (Option.some.inj hthis) (fun hcc => hzt hcc.symm)
  have hb₀t : b₀ ≠ Sum.inr t := by
    intro hcon
    rw [hcon] at hbotS
    rw [← (Board.bottomOf_eq S.board z (Sum.inr t)).mp hbotS] at hseatT
    exact absurd hseatT (by simp)
  -- the B-side landing data, split per base kind
  have hfreeb : S.board.topOf b = none := by
    rw [hcells b hseatβ]
    cases b with
    | inl a => exact topOf_of_canPlace ((canMoveRun_inl_iff).mp hcmr')
    | inr d => exact topOf_of_canPlace (((canMoveRun_inr_iff).mp hcmr').1)
  have hcpA : S.canPlace z b = true := by
    cases b with
    | inl a =>
        exact (canPlace_inl_iff).mpr
          ⟨hfreeb, ((canPlace_inl_iff).mp
            ((canMoveRun_inl_iff).mp hcmr')).2⟩
    | inr d =>
        have hd : d ≠ t := by
          intro hcon; exact hseatt (congrArg Sum.inr hcon)
        have hBcp : S'.canPlace z (Sum.inr d) = true :=
          ((canMoveRun_inr_iff).mp hcmr').1
        have hvisA : S.isVis d = true := by
          show (S.board.bottomOf d).isSome = true
          rw [hbofs d hd]
          exact ((canPlace_inr_iff).mp hBcp).2.1
        exact (canPlace_inr_iff).mpr
          ⟨hfreeb, hvisA, ((canPlace_inr_iff).mp hBcp).2.2⟩
  have hselfA : S.canMoveRun z b = true := by
    cases b with
    | inl a => exact (canMoveRun_inl_iff).mpr hcpA
    | inr d =>
        have hBcp : S'.canPlace z (Sum.inr d) = true :=
          ((canMoveRun_inr_iff).mp hcmr').1
        have hBnot : (S'.board.aboveOf z).contains d = false :=
          ((canMoveRun_inr_iff).mp hcmr').2
        have hnot : (S.board.aboveOf z).contains d = false := by
          rcases aboveOf_twin_delta hdp2 z with h | h
          · rw [h]; exact hBnot
          · rw [h]
            by_cases hdt : d = t
            · exact absurd (congrArg Sum.inr hdt) hseatt
            · show (t :: S'.board.aboveOf z).contains d = false
              have hmemB : d ∉ S'.board.aboveOf z := by
                intro dm
                rw [(List.contains_iff_mem).mpr dm] at hBnot
                exact Bool.noConfusion hBnot
              have hmem : d ∉ t :: S'.board.aboveOf z := by
                intro dm
                rcases List.mem_cons.mp dm with rfl | dm
                · exact hdt rfl
                · exact hmemB dm
              by_cases hhc : (t :: S'.board.aboveOf z).contains d = true
              · exact absurd ((List.contains_iff_mem).mp hhc) hmem
              · simp only [Bool.not_eq_true'] at hhc
                exact hhc
        exact (canMoveRun_inr_iff).mpr ⟨hcpA, hnot⟩
  have hfreeA : (S.board.detach b₀).topOf b = none := by
    rw [Board.detach_topOf_ne _ _ _ (Ne.symm hne')]
    exact hfreeb
  have hnewz : (S.board.detach b₀).bottomOf z = none := by
    refine (Board.bottomOf_eq_none _ _).mpr (fun x hx => ?_)
    by_cases hxb : x = b₀
    · rw [hxb, Board.detach_topOf] at hx; exact absurd hx (by simp)
    · rw [Board.detach_topOf_ne _ _ _ hxb] at hx
      have hbxA : S.board.bottomOf z = some x := (Board.bottomOf_eq _ _ x).mpr hx
      rw [hbotS] at hbxA
      exact absurd (Option.some.inj hbxA) (Ne.symm hxb)
  obtain ⟨bdA, hattA⟩ := Option.ne_none_iff_exists'.mp
    ((Board.attach_eq_some_iff _ _ _).mpr ⟨hfreeA, hnewz⟩)
  have swit : State := { S with board := bdA }
  refine ⟨swit, ?_, ?_⟩
  · exact apply_pilePile_iff.mpr ⟨b₀, hbotS, hne', hselfA, bdA, hattA, rfl⟩
  · have hdetβA : (S.board.detach b₀).topOf β = some t := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβA
    have hdetβB : (S'.board.detach b₀).topOf β = none := by
      rw [Board.detach_topOf_ne _ _ _ (Ne.symm hb₀β)]; exact hβB
    have hcells' : ∀ x, x ≠ β → bdA.topOf x = bd'.topOf x := by
      intro x hx
      by_cases hxb : x = b
      · rw [hxb, Board.attach_topOf _ _ _ hattA, Board.attach_topOf _ _ _ hatt']
      · rw [Board.attach_topOf_ne _ _ _ hattA hxb, Board.attach_topOf_ne _ _ _ hatt' hxb]
        by_cases hxb₀ : x = b₀
        · rw [hxb₀, Board.detach_topOf, Board.detach_topOf]
        · rw [Board.detach_topOf_ne _ _ _ hxb₀, Board.detach_topOf_ne _ _ _ hxb₀]
          exact hcells x hx
    have hβA' : bdA.topOf β = some t := by
      rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatβ)]
      exact hdetβA
    have hβB' : bd'.topOf β = none := by
      rw [Board.attach_topOf_ne _ _ _ hatt' (Ne.symm hseatβ)]
      exact hdetβB
    refine ⟨hβA', hβB', hcells', ?_, ?_, ?_, hdeal, hdep, hstock, hhβ, hhh, hds⟩
    · exact (Board.bottomOf_eq _ _ β).mpr hβA'
    · rw [Board.attach_topOf_ne _ _ _ hattA (Ne.symm hseatt),
        Board.detach_topOf_ne _ _ _ (Ne.symm hb₀t)]
      exact hseatT
    · exact fun c' hc' => bottomOf_cell_transfer hc' hβA' hβB' hcells'

/-! ### The replay chain and the repaired reduction

The per-kind transfers assemble by induction on the mid: the whole
mid runs on the A-side of the pair, and the A-side t-suit rung — the
`twinMid` gate excludes every t-suit foundation move, so no replay
step touches it — is exactly the fired twin's own rung, so the
deferred firing at the replay's end lands on the source's `C` itself. -/

private theorem mid_access_chain {t : Card} {β : Base} {A : State} :
    ∀ (mid : List Move) (S S' C : State),
    (∀ m ∈ mid, Move.twinMid t m = true) →
    TwinReplayTrace t β S S' →
    S.WF →
    S.deal = A.deal →
    (∀ a, S.depths a ≤ A.depths a) →
    S.heights t.suit = A.heights t.suit →
    (∀ m ∈ mid, ∀ b : Base,
      (match m with
       | .deckPile _ b' => b = b'
       | .stackPile _ b' => b = b'
       | .pilePile _ b' => b = b'
       | .pileStack c' => b = Sum.inr c'
       | .reveal a' => b = Sum.inl a' ∨ b = A.hiddenBase a' ∨
           (∃ r, r ∈ A.hidden a' ∧ b = Sum.inr r)
       | _ => False) →
      b ≠ β ∧ b ≠ Sum.inr t) →
    S'.run mid = some C →
    ∃ M₀, S.run mid = some M₀ ∧ TwinReplayTrace t β M₀ C ∧
      M₀.heights t.suit = A.heights t.suit := by
  intro mid
  induction mid with
  | nil =>
      intro S S' C _ hdp _ _ _ _ hrk hrun
      obtain rfl := run_nil_elim hrun
      exact ⟨S, rfl, hdp, hrk⟩
  | cons m ms ih =>
      intro S S' C hmid hdp hwf hdeal hdep hrk hno hrun
      obtain ⟨S'₁, hmB, hrest⟩ := run_cons_elim hrun
      cases m with
      | draw =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_draw hdp hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf Move.draw S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid Move.draw List.mem_cons_self) hmA).trans hrk)
              hno hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply Move.draw with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | deckStack x =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_deckStack hdp
            ((Move.twinMid_deckStack t x).mp (hmid (Move.deckStack x)
              List.mem_cons_self)).1 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.deckStack x) S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.deckStack x) List.mem_cons_self)
                hmA).trans hrk)
              hno hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.deckStack x) with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | pileStack x =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_pileStack hdp
            ((Move.twinMid_pileStack t x).mp (hmid (Move.pileStack x)
              List.mem_cons_self)).1
            (Ne.symm (hno (Move.pileStack x) List.mem_cons_self (Sum.inr x) rfl).1)
            hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.pileStack x) S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.pileStack x) List.mem_cons_self)
                hmA).trans hrk)
              hno hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.pileStack x) with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | deckPile x b' =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_deckPile hwf hdp
            (hno (Move.deckPile x b') List.mem_cons_self b' rfl).1
            (hno (Move.deckPile x b') List.mem_cons_self b' rfl).2 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.deckPile x b') S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.deckPile x b') List.mem_cons_self)
                hmA).trans hrk)
              hno hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.deckPile x b') with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | stackPile x b' =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_stackPile hdp
            ((Move.twinMid_stackPile t x b').mp (hmid (Move.stackPile x b')
              List.mem_cons_self)).1
            (hno (Move.stackPile x b') List.mem_cons_self b' rfl).1
            (hno (Move.stackPile x b') List.mem_cons_self b' rfl).2 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.stackPile x b') S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.stackPile x b') List.mem_cons_self)
                hmA).trans hrk)
              hno hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.stackPile x b') with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | pilePile x b' =>
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_pilePile hdp
            (hno (Move.pilePile x b') List.mem_cons_self b' rfl).1
            (hno (Move.pilePile x b') List.mem_cons_self b' rfl).2 hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.pilePile x b') S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.pilePile x b') List.mem_cons_self)
                hmA).trans hrk)
              hno hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.pilePile x b') with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs
      | reveal a =>
          have hseatR : ∀ r, S.topHidden a = some r → β ≠ Sum.inr r := by
            intro r hr
            have hrS : r ∈ S.hidden a := mem_of_getLast hr
            have hrA : r ∈ A.hidden a := hidden_sub_of_deal hdeal (hdep a) hrS
            exact Ne.symm (hno (Move.reveal a) List.mem_cons_self (Sum.inr r)
              (Or.inr (Or.inr ⟨r, hrA, rfl⟩))).1
          have hseatB : β ≠ S.hiddenBase a := by
            rcases hiddenBase_cases (st := S) a with hbase | ⟨d, hbase, hd⟩
            · rw [← hbase]
              exact Ne.symm (hno (Move.reveal a) List.mem_cons_self (Sum.inl a)
                (Or.inl rfl)).1
            · have hdA : d ∈ A.hidden a := hidden_sub_of_deal hdeal (hdep a) hd
              rw [hbase]
              exact Ne.symm (hno (Move.reveal a) List.mem_cons_self (Sum.inr d)
                (Or.inr (Or.inr ⟨d, hdA, rfl⟩))).1
          obtain ⟨S₁, hmA, hdp₁⟩ := mid_access_reveal hwf hdp hseatR hseatB hmB
          obtain ⟨M₀, hMs, hpack₂, hrk₂⟩ :=
            ih S₁ S'₁ C (fun m' hm' => hmid m' (List.mem_cons_of_mem _ hm'))
              hdp₁ (apply_wf hwf (Move.reveal a) S₁ hmA)
              ((deal_stable_move hmA).symm.trans hdeal)
              (fun a => Nat.le_trans (depths_mono_move hmA a) (hdep a))
              ((heights_tSuit_stable (hmid (Move.reveal a) List.mem_cons_self)
                hmA).trans hrk)
              hno hrest
          refine ⟨M₀, ?_, hpack₂, hrk₂⟩
          show (match S.apply (Move.reveal a) with
            | some st' => st'.run ms
            | none => none) = some M₀
          rw [hmA]; exact hMs

/-- **HACCESS DERIVED (the repaired reduction, landed 2026-10-05)**:
at WF, the source's own mid plus the per-seat exclusions derive the
WHOLE replay at the pre-firing state, and the deferred twin firing
lands exactly on the source's mid successor `C` — the model-side
certificate of §8's landing-site audit.

The `noSeat` premise is wave 19's REPAIRED form (the wave-18 pin was
false as stated; see the section note above): beyond the three
landing kinds it now excludes the `pileStack` seat cells — the twin
may sit ON a raise card (witness A's corner, live at WF through
`board_edges`' deal-adjacency clause) — and the reveal's boundary
structure: the pile's anchor, `A.hiddenBase a`, and the seats of all
of `A.hidden a`'s cards — the current AND every future
boundary/attach cell of that pile's reveal chain (reveal only
decrements the take; every later boundary stays inside the shrinking
prefix). -/
theorem State.mid_access_of_noSeat {st : State} {t : Card}
    {p₁ mid : List Move} {A B C : State} {β : Base}
    (hwf : st.WF)
    (hp₁ : st.run p₁ = some A)
    (hf₁ : A.apply (Move.pileStack t) = some B)
    (hβ : A.board.bottomOf t = some β)
    (hmid : ∀ m ∈ mid, Move.twinMid t m = true)
    (hBmid : B.run mid = some C)
    (hnoseat : ∀ m ∈ mid, ∀ b : Base,
      (match m with
       | .deckPile _ b' => b = b'
       | .stackPile _ b' => b = b'
       | .pilePile _ b' => b = b'
       | .pileStack c' => b = Sum.inr c'
       | .reveal a' => b = Sum.inl a' ∨ b = A.hiddenBase a' ∨
           (∃ r, r ∈ A.hidden a' ∧ b = Sum.inr r)
       | _ => False) →
      b ≠ β ∧ b ≠ Sum.inr t) :
    ∃ M₀, A.run mid = some M₀ ∧ M₀.apply (Move.pileStack t) = some C := by
  have hwfA : A.WF := run_wf p₁ st A hp₁ hwf
  have hpack := twinReplayTrace_of_firing hf₁ hβ
  rw [apply_pileStack_iff] at hf₁
  obtain ⟨-, b₁, -, hrkA, -⟩ := hf₁
  obtain ⟨M₀, hArun, hpack₂, hrkM⟩ :=
    mid_access_chain (A := A) mid A B C hmid hpack hwfA rfl (fun _ => Nat.le_refl _)
      rfl hnoseat hBmid
  obtain ⟨hβM, hβC, hcellsM, hbotβM, hseatM, hbofsM, hdealM, hdepM, hstockM,
    hhβM, hhhM, -⟩ := hpack₂
  have hshC : { M₀ with board := M₀.board.detach β,
      heights := fun s => if s = t.suit then M₀.heights s + 1 else M₀.heights s }
      = C := by
    apply state_ext
    · exact hdealM
    · apply Board.ext_topOf
      funext x
      by_cases hxb : x = β
      · rw [hxb, Board.detach_topOf, hβC]
      · rw [Board.detach_topOf_ne _ _ _ hxb]
        exact hcellsM x hxb
    · funext s
      show (if s = t.suit then M₀.heights s + 1 else M₀.heights s) = C.heights s
      by_cases hs : s = t.suit
      · rw [ite_eq_left hs, hs]
        exact hhβM.symm
      · rw [ite_eq_right hs]
        exact hhhM s hs
    · exact hdepM
    · exact hstockM
    · rfl
  refine ⟨M₀, hArun, ?_⟩
  rw [apply_pileStack_iff]
  exact ⟨hseatM, β, hbotβM, by rw [hrkM]; exact hrkA, hshC⟩

