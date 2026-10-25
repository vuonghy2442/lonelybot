import Orig2.TwinPairFreeClass
import Orig2.TwinRaiseCommute
import Orig2.TwinSplicePlay
import Orig2.Classification
import Orig2.SeatMateStack
import Orig2.PairClassSeed
import Orig2.Kit
import Orig2.Integrity

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Orig2.TwinPairFreeRev — the pair-free reversal theorem

The pair-free orbit class of `Orig2/TwinPairFreeClass.lean` leaves one
direction open: a pair-free witness shuffle out of a both-seated `WF`
position is itself pair-free reversible.  This card proves it by
induction on the shuffle, reducing to a single-letter inverse:

* a pair-free `tabToFound` is undone by the `foundToTab` pull onto the
  give-back seat (the under-seat or the bare-king arm);
* a pair-free `foundToTab` is undone by the `tabToFound` re-raise;
* a pair-free `tabToTab` is undone by the mirror slide back onto its
  original seat (the under-seat or the bare-king arm);
* `wasteToFound`/`wasteToTab` are never reversible;
* a reversible `draw` is undone by a pure-draw return play, every
  letter of which is reversible by the draw cycle.

The single-letter inverse's reversibility witness is the original step
itself (return run `[m]`).  Zero `sorry`, zero `Classical.choice`, no
new axioms.
-/

open State

namespace TwinPairFreeRev

/-! ## §1. Foundation arithmetic -/

/-- The build-order list is nodup. -/
theorem upCards_nodup (s : Suit) : s.upCards.Nodup := by
  cases s <;> decide

/-- The first-occurrence position of a member is unchanged by taking a
prefix that still contains it. -/
theorem posOf_take_of_mem {α : Type} [DecidableEq α] :
    ∀ (l : List α) (x : α), x ∈ l → ∀ n, x ∈ l.take n →
      FoundKit.posOf x (l.take n) = FoundKit.posOf x l := by
  intro l
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons y t ih =>
      intro x hx n hn
      cases n with
      | zero =>
          rw [List.take_zero] at hn
          exact absurd hn (by simp)
      | succ m =>
          rw [List.take_succ_cons] at hn ⊢
          rcases List.mem_cons.mp hn with hxy | hxt
          · subst x
            rw [FoundKit.posOf, ite_eq_left rfl, FoundKit.posOf, ite_eq_left rfl]
          · by_cases hyx : y = x
            · subst hyx
              rw [FoundKit.posOf, ite_eq_left rfl, FoundKit.posOf, ite_eq_left rfl]
            · have hxt' : x ∈ t := by
                rcases List.mem_cons.mp hx with hxy2 | hxt2
                · exact absurd hxy2.symm hyx
                · exact hxt2
              rw [FoundKit.posOf, ite_eq_right hyx, FoundKit.posOf, ite_eq_right hyx,
                ih x hxt' m hxt]

/-- In a nodup list, the last element sits at the final index. -/
theorem posOf_last_eq_length_sub_one {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlast : lastOf l = some c) :
    FoundKit.posOf c l = l.length - 1 := by
  induction l with
  | nil =>
      rw [lastOf] at hlast
      exact absurd hlast (by simp)
  | cons y t ih =>
      cases t with
      | nil =>
          rw [lastOf] at hlast
          injection hlast with hcy
          subst hcy
          rw [FoundKit.posOf, ite_eq_left rfl]
          rfl
      | cons z t' =>
          rw [show lastOf (y :: z :: t') = lastOf (z :: t') from rfl] at hlast
          have hnd' : (z :: t').Nodup := (List.nodup_cons.mp hnd).2
          have hih := ih hnd' hlast
          have hyc : y ≠ c := by
            intro hcon
            subst hcon
            exact (List.nodup_cons.mp hnd).1 (lastOf_mem hlast)
          rw [FoundKit.posOf, ite_eq_right hyc, hih]
          rfl

/-- A `WF` foundation's chop length is the rank index of its top card. -/
theorem found_chop_length_eq_rank {st : State} {s : Suit} {c : Card}
    (hwf : st.WF) (htop : st.foundTop s = some c) :
    (chop (st.found s)).length = c.rank.toIdx := by
  obtain ⟨n, hn⟩ := hwf.found_prefix s
  have hlast : lastOf (st.found s) = some c := htop
  have hmemFound : c ∈ st.found s := lastOf_mem hlast
  have hmem : c ∈ s.upCards.take n := by rw [← hn]; exact hmemFound
  have hmemU : c ∈ s.upCards := List.mem_of_mem_take hmem
  obtain ⟨r, -, hcr⟩ := List.mem_map.mp hmemU
  have hc : c = Card.mk s r := hcr.symm
  subst hc
  have hnd : (s.upCards.take n).Nodup := List.Pairwise.take (i := n) (upCards_nodup s)
  have hposLast : FoundKit.posOf (Card.mk s r) (s.upCards.take n) =
      (s.upCards.take n).length - 1 :=
    posOf_last_eq_length_sub_one hnd (by rw [← hn]; exact hlast)
  have hposEq : FoundKit.posOf (Card.mk s r) (s.upCards.take n) =
      FoundKit.posOf (Card.mk s r) s.upCards :=
    posOf_take_of_mem s.upCards (Card.mk s r) hmemU n hmem
  have hrank : FoundKit.posOf (Card.mk s r) s.upCards = r.toIdx :=
    FoundKit.posOf_upCards s r
  have hcl : (chop (st.found s)).length + 1 = (st.found s).length := by
    have hlc := congrArg List.length (lastOf_chop hlast)
    rw [List.length_append] at hlc
    simp at hlc
    omega
  have htakeLen : (s.upCards.take n).length = (st.found s).length := by rw [← hn]
  calc
    (chop (st.found s)).length = (s.upCards.take n).length - 1 := by omega
    _ = FoundKit.posOf (Card.mk s r) (s.upCards.take n) := hposLast.symm
    _ = FoundKit.posOf (Card.mk s r) s.upCards := hposEq
    _ = r.toIdx := hrank
/-! ## §2. Pile-level round-trip helpers -/

/-- A no-reveal empty round trip. -/
private theorem afterRunRemoved_empty_eq : ∀ (p : Pile), p.hidden = [] →
    Pile.afterRunRemoved p ([] : List Card) = ⟨[], []⟩
  | ⟨[], _⟩, _ => rfl
  | ⟨_ :: _, _⟩, hhd => absurd hhd (by simp)

/-- A nonempty-prefix removal keeps the recorded prefix. -/
private theorem afterRunRemoved_cons (p : Pile) (w : Card) (ws : List Card) :
    Pile.afterRunRemoved p (w :: ws) = { p with faceUp := w :: ws } := rfl

/-- The below-part of a run that starts at `c` is empty. -/
private theorem below_head_eq {c : Card} {t : List Card} :
    below c (c :: t) = [] := by
  rw [below, ite_eq_left rfl]

/-- A card present in a list has a nonempty run from it. -/
private theorem fromCard_ne_nil_of_mem {c : Card} {l : List Card} (h : c ∈ l) :
    fromCard c l ≠ [] := by
  obtain ⟨t, ht⟩ := fromCard_eq_head_of_mem h
  rw [ht]
  simp

/-- A placement onto an empty seat, as one state update. -/
private theorem putCard_inl_eq_setPile {st : State} {c : Card} {a : Anchor} :
    st.putCard c (Sum.inl a) =
      { st with piles := fun a' => if a' = a then ⟨[], [c]⟩ else st.piles a' } := by
  show (st.setPile a ⟨[], [c]⟩) = _
  rfl

/-- A placement onto a located card base, as one state update. -/
private theorem putCard_inr_eq_setPile {st : State} {c : Card} {z : Card} {k : Anchor}
    (hz : st.pileOfTop z = some k) :
    st.putCard c (Sum.inr z) =
      { st with piles := fun a' =>
          if a' = k then { st.piles k with faceUp := (st.piles k).faceUp ++ [c] }
          else st.piles a' } := by
  simp only [State.putCard, hz]
  rfl

/-- The pile-level round trip of a card-on-card placement. -/
private theorem putCard_inr_roundtrip (p : Pile) (c : Card) (hf : p.faceUp ≠ []) :
    Pile.afterRunRemoved { p with faceUp := p.faceUp ++ [c] } (chop (p.faceUp ++ [c])) = p := by
  rcases p with ⟨h, f⟩
  rw [chop_snoc]
  cases f with
  | nil => exact absurd rfl hf
  | cons x xs => rfl

/-- The top pin with two exception piles. -/
private theorem topPin2 {st s₁ : State} {a k : Anchor} {z : Card}
    (htop : (s₁.piles a).top = some z)
    (hothers : ∀ a', a' ≠ a → a' ≠ k → s₁.piles a' = st.piles a')
    (hknot : (s₁.piles k).top ≠ some z)
    (hno : ∀ a', a' ≠ a → a' ≠ k → (st.piles a').top ≠ some z) :
    s₁.pileOfTop z = some a := by
  show firstWhere (fun a' => decide ((s₁.piles a').top = some z)) Anchor.all = some a
  refine firstWhere_find (Anchor.mem_all a) (decide_eq_true htop) ?_
  intro y hy hyne
  by_cases hyk : y = k
  · rw [hyk]
    exact decide_false_of_not hknot
  · have he : (s₁.piles y).top = (st.piles y).top := by rw [hothers y hyne hyk]
    rw [he]
    exact decide_false_of_not (hno y hyne hyk)

/-- The holding pin with two exception piles. -/
private theorem holdingPin2 {st s₁ : State} {k a : Anchor} {c : Card}
    (ha : c ∉ (s₁.piles a).faceUp)
    (hothers : ∀ a', a' ≠ k → a' ≠ a → s₁.piles a' = st.piles a')
    (hholds : c ∈ (s₁.piles k).faceUp)
    (hno : ∀ a', a' ≠ k → a' ≠ a → c ∉ (st.piles a').faceUp) :
    s₁.pileHolding c = some k := by
  show firstWhere (fun a' => decide (c ∈ (s₁.piles a').faceUp)) Anchor.all = some k
  refine firstWhere_find (Anchor.mem_all k) (decide_eq_true hholds) ?_
  intro y hy hyne
  by_cases hya : y = a
  · rw [hya]
    exact decide_false_of_not ha
  · have he : (s₁.piles y).faceUp = (st.piles y).faceUp := by rw [hothers y hyne hya]
    rw [he]
    exact decide_false_of_not (hno y hyne hya)

/-! ## §3. The raise undo, step form -/

/-- **The raise-undo scaffold, step form.** -/
private theorem step_foundToTab_of_tabToFound_scaffold {st s₁ : State} {c : Card} {b : Base}
    {seat : Anchor} {P' : Pile}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hs₁ : s₁ = { st.setFound c.suit (st.found c.suit ++ [c]) with
                  piles := fun a' =>
                    if a' = seat then
                      Pile.afterRunRemoved (st.piles seat) (chop (st.piles seat).faceUp)
                    else st.piles a' })
    (hft : s₁.foundTop c.suit = some c)
    (hcp : s₁.canPlace c b = true)
    (hset : (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c b
        = { s₁.setFound c.suit (chop (s₁.found c.suit)) with
            piles := fun a' => if a' = seat then P' else s₁.piles a' })
    (hs₁found : s₁.found c.suit = st.found c.suit ++ [c])
    (hs₁other : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ)
    (hseat' : P' = st.piles seat)
    (hkeep : ∀ a'', a'' ≠ seat → s₁.piles a'' = st.piles a'') :
    State.step s₁ (Move.foundToTab c b) = some st := by
  simp only [State.step, hft]
  rw [hcp]
  refine congrArg some (?_ :
    (s₁.setFound c.suit (chop (s₁.found c.suit))).putCard c b = st)
  rw [hset]
  refine State.ext (funext fun σ => ?_) (funext fun a'' => ?_) ?_ ?_ ?_
  · show (if σ = c.suit then chop (s₁.found c.suit) else s₁.found σ) = st.found σ
    by_cases hσ : σ = c.suit
    · rw [hσ, ite_eq_left rfl, hs₁found, chop_snoc]
    · rw [ite_eq_right hσ]
      exact hs₁other σ hσ
  · show (if a'' = seat then P' else s₁.piles a'') = st.piles a''
    by_cases ha'' : a'' = seat
    · rw [ha'', ite_eq_left rfl, hseat']
    · rw [ite_eq_right ha'']
      exact hkeep a'' ha''
  · show s₁.stock = st.stock
    rw [hs₁]
    rfl
  · show s₁.waste = st.waste
    rw [hs₁]
    rfl
  · show s₁.drawStep = st.drawStep
    rw [hs₁]
    rfl

/-- **The under-seat raise undo, step form.** -/
theorem step_foundToTab_of_tabToFound_under {st : State} {c : Card} {a : Anchor}
    {z : Card} {s₁ : State}
    (hstep : State.step st (Move.tabToFound c) = some s₁)
    (hpa : st.pileOfTop c = some a)
    (hz : lastOf (chop (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hsearch : s₁.pileOfTop z = some a) :
    State.step s₁ (Move.foundToTab c (Sum.inr z)) = some st := by
  obtain ⟨-, a₀, hpa₀, hs₁⟩ := step_tabToFound_inv hstep
  rw [hpa] at hpa₀
  injection hpa₀ with haa
  subst haa
  obtain ⟨-, hlastc⟩ := pileOfTop_top hpa
  have hfull : (st.piles a).faceUp = chop (st.piles a).faceUp ++ [c] := lastOf_chop hlastc
  obtain ⟨hs₁found, hs₁other, hft⟩ := tabToFound_found_trio hs₁
  have hcp : s₁.canPlace c (Sum.inr z) = true := by
    simp only [State.canPlace, hsearch]
    exact hsit
  exact step_foundToTab_of_tabToFound_scaffold hstep hs₁ hft hcp
    (putCard_inr_eq_setPile hsearch) hs₁found hs₁other
    (by
      have hQeq : (s₁.setFound c.suit (chop (s₁.found c.suit))).piles = s₁.piles := rfl
      have hpla : s₁.piles a
          = Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp) := by
        rw [hs₁]
        show (if a = a then
            Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a) = _
        rw [ite_eq_left rfl]
      rw [hQeq, hpla]
      cases hc : chop (st.piles a).faceUp with
      | nil =>
          rw [hc] at hz
          exact absurd hz (by simp [lastOf])
      | cons y ys =>
          rw [hc] at hfull
          show (⟨(st.piles a).hidden, (y :: ys) ++ [c]⟩ : Pile) = st.piles a
          exact Pile.ext rfl hfull.symm)
    (fun a'' ha'' => by
      rw [hs₁]
      show (if a'' = a then
          Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
          else st.piles a'') = st.piles a''
      rw [ite_eq_right ha''])

/-! ## §4. The pull undo, step form -/

/-- The state-level round trip behind the pull undo. -/
private theorem step_tabToFound_of_foundToTab_rtp
    {st : State} {c : Card} {b : Base} {s₁ : State} {k : Anchor}
    (hstep : State.step st (Move.foundToTab c b) = some s₁)
    (hidx : (chop (st.found c.suit)).length = c.rank.toIdx)
    (hfound : s₁.found c.suit = chop (st.found c.suit))
    (hotherfound : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ)
    (hsearch : s₁.pileOfTop c = some k)
    (hkrest : Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp) = st.piles k)
    (hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a')
    (hkeep : s₁.stock = st.stock ∧ s₁.waste = st.waste ∧ s₁.drawStep = st.drawStep) :
    State.step s₁ (Move.tabToFound c) = some st := by
  obtain ⟨c', htop, hc'c, -, hs⟩ := step_foundToTab_inv hstep
  simp only [hc'c] at htop
  have hF : st.found c.suit = chop (st.found c.suit) ++ [c] :=
    lastOf_chop htop
  have hnextup : s₁.nextUp c = true := by
    show decide (c.rank.toIdx = (s₁.found c.suit).length) = true
    rw [hfound, hidx]
    exact decide_eq_true rfl
  simp only [State.step, hnextup, hsearch]
  refine congrArg some (?_ :
    { s₁.setFound c.suit (s₁.found c.suit ++ [c]) with
      piles := fun a' =>
        if a' = k then Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
        else s₁.piles a' } = st)
  refine State.ext (funext fun σ => ?_) (funext fun a' => ?_) ?_ ?_ ?_
  · show (if σ = c.suit then s₁.found c.suit ++ [c] else s₁.found σ) = st.found σ
    by_cases hσ : σ = c.suit
    · rw [hσ, ite_eq_left rfl, hfound, ← hF]
    · rw [ite_eq_right hσ]
      exact hotherfound σ hσ
  · show (if a' = k then Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp)
        else s₁.piles a') = st.piles a'
    by_cases ha' : a' = k
    · rw [ha', ite_eq_left rfl]
      exact hkrest
    · rw [ite_eq_right ha']
      exact hzkeep a' ha'
  · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).stock = st.stock
    rw [setFound_stock]
    exact hkeep.1
  · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).waste = st.waste
    rw [setFound_waste]
    exact hkeep.2.1
  · show (s₁.setFound c.suit (s₁.found c.suit ++ [c])).drawStep = st.drawStep
    rw [setFound_drawStep]
    exact hkeep.2.2

/-- **The pull undo, step form.**  A successful pull is undone by the
re-raise of the same card. -/
theorem step_tabToFound_of_foundToTab {st s₁ : State} {c : Card} {b : Base}
    (hwf : st.WF)
    (hstep : State.step st (Move.foundToTab c b) = some s₁) :
    State.step s₁ (Move.tabToFound c) = some st := by
  obtain ⟨c', htop, hc'c, hcp, hs⟩ := step_foundToTab_inv hstep
  subst c'
  have hidx : (chop (st.found c.suit)).length = c.rank.toIdx :=
    found_chop_length_eq_rank hwf htop
  have hfound : s₁.found c.suit = chop (st.found c.suit) := by
    rw [hs, putCard_found, setFound_found_self]
  have hotherfound : ∀ σ, σ ≠ c.suit → s₁.found σ = st.found σ := by
    intro σ hσ
    rw [hs, putCard_found, setFound_found_ne hσ]
  have hkeep : s₁.stock = st.stock ∧ s₁.waste = st.waste ∧ s₁.drawStep = st.drawStep := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hs, putCard_stock, setFound_stock]
    · rw [hs, putCard_waste, setFound_waste]
    · rw [hs, putCard_drawStep, setFound_drawStep]
  rcases b with a | z
  · -- empty-seat landing
    obtain ⟨hemp, -⟩ := canPlace_inl hcp
    obtain ⟨hhd, hfu⟩ := (Pile.isEmpty_eq _).mp hemp
    have hs1a : s₁.piles a = ⟨[], [c]⟩ := by
      rw [hs]
      simp only [putCard_piles_inl, setFound_piles, ite_true]
    have hsearch : s₁.pileOfTop c = some a := by
      rw [pileOfTop_eq_some_iff (step_wf hwf hstep)]
      show lastOf (s₁.piles a).faceUp = some c
      rw [hs1a]
      rfl
    have hkrest : Pile.afterRunRemoved (s₁.piles a) (chop (s₁.piles a).faceUp) = st.piles a := by
      rw [hs1a]
      show Pile.afterRunRemoved (⟨[], [c]⟩ : Pile) (chop [c]) = st.piles a
      rw [show chop ([c] : List Card) = [] from rfl]
      rw [afterRunRemoved_empty_eq _ rfl]
      exact Pile.ext hhd.symm hfu.symm
    have hzkeep : ∀ a', a' ≠ a → s₁.piles a' = st.piles a' := by
      intro a' ha'
      rw [hs]
      simp only [putCard_piles_inl, setFound_piles]
      rw [ite_eq_right ha']
    exact step_tabToFound_of_foundToTab_rtp hstep hidx hfound hotherfound hsearch hkrest hzkeep hkeep
  · -- card landing
    obtain ⟨k, hzloc, -⟩ := canPlace_inr hcp
    have hfaceNon : (st.piles k).faceUp ≠ [] := (pileOfTop_top hzloc).1
    have hs1k : s₁.piles k =
        { st.piles k with faceUp := (st.piles k).faceUp ++ [c] } := by
      rw [hs, putCard_piles_inr (st.setFound c.suit (chop (st.found c.suit))) c z k (by simpa using hzloc)]
      simp only [setFound_piles, ite_true]
    have hsearch : s₁.pileOfTop c = some k := by
      rw [pileOfTop_eq_some_iff (step_wf hwf hstep)]
      show lastOf (s₁.piles k).faceUp = some c
      rw [hs1k]
      exact lastOf_snoc
    have hkrest : Pile.afterRunRemoved (s₁.piles k) (chop (s₁.piles k).faceUp) = st.piles k := by
      rw [hs1k]
      rw [show chop ((st.piles k).faceUp ++ [c]) = (st.piles k).faceUp from chop_snoc]
      obtain ⟨h, f, hpf⟩ : ∃ h f, st.piles k = ⟨h, f⟩ := ⟨_, _, rfl⟩
      rw [hpf] at hfaceNon ⊢
      cases f with
      | nil => exact absurd rfl hfaceNon
      | cons w ws => rfl
    have hzkeep : ∀ a', a' ≠ k → s₁.piles a' = st.piles a' := by
      intro a' ha'
      rw [hs, putCard_piles_inr (st.setFound c.suit (chop (st.found c.suit))) c z k (by simpa using hzloc)]
      simp only [setFound_piles]
      rw [ite_eq_right ha']
    exact step_tabToFound_of_foundToTab_rtp hstep hidx hfound hotherfound hsearch hkrest hzkeep hkeep
/-! ## §5. The slide undo, step form -/

/-- The slide landing facts. -/
private theorem tabToTab_landing_facts {st : State} {c : Card} {b : Base}
    {a k : Anchor} {P : Pile} {tr : List Card} {s₁ : State}
    (hs₁ : s₁ = (st.setPile a P).putRun (fromCard c (st.piles a).faceUp) b)
    (hrt : fromCard c (st.piles a).faceUp = c :: tr)
    (hcN : c ∉ (st.piles k).faceUp)
    (hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩) :
    (∀ σ, s₁.found σ = st.found σ) ∧ s₁.stock = st.stock ∧
      s₁.waste = st.waste ∧ s₁.drawStep = st.drawStep ∧
      (s₁.piles k).faceUp = (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp ∧
      (s₁.piles k).hidden = (st.piles k).hidden ∧
      below c (s₁.piles k).faceUp = (st.piles k).faceUp ∧
      fromCard c (s₁.piles k).faceUp = c :: tr := by
  have hKfaceUp : (s₁.piles k).faceUp =
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp :=
    congrArg (fun p => p.faceUp) hs₁K
  have hexcl := tfc_below_fromCard_excl c ((st.piles k).faceUp)
    (fromCard c (st.piles a).faceUp) hcN
  refine ⟨fun σ => by rw [hs₁, putRun_found, setPile_found],
    ?_, ?_, ?_, hKfaceUp, congrArg (fun p => p.hidden) hs₁K, ?_, ?_⟩
  · rw [hs₁, putRun_stock, setPile_stock]
  · rw [hs₁, putRun_waste, setPile_waste]
  · rw [hs₁, putRun_drawStep, setPile_drawStep]
  · have h1 : below c (s₁.piles k).faceUp
        = below c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.1, hrt, below_head_eq, List.append_nil]
  · have h1 : fromCard c (s₁.piles k).faceUp
        = fromCard c ((st.piles k).faceUp ++ fromCard c (st.piles a).faceUp) := by
      rw [hKfaceUp]
    rw [h1, hexcl.2, hrt, fromCard_head_eq]

/-- The bare-king slide's whole-segment relocation round trip. -/
private theorem tabToTab_bare_rtp {st : State} {c : Card} {b : Base} {a k : Anchor}
    {tr : List Card} {s₁ : State}
    (hs₁ : s₁ = (st.setPile a ⟨[], ([] : List Card)⟩).putRun
      (fromCard c (st.piles a).faceUp) b)
    (hrt : fromCard c (st.piles a).faceUp = c :: tr)
    (hface : (st.piles a).faceUp = c :: tr)
    (hhidden : (st.piles a).hidden = [])
    (hking : c.rank = Rank.king)
    (hhold : s₁.pileHolding c = some k)
    (hs₁A : s₁.piles a = ⟨[], ([] : List Card)⟩)
    (hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hka : k ≠ a)
    (hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = []) :
    s₁.run [Move.tabToTab c (Sum.inl a)] = some st := by
  obtain ⟨hsF, hsS, hsW, hsD, hKfaceUp, hKhidden, hbelowK, hrunK⟩ :=
    tabToTab_landing_facts hs₁ hrt hcN hs₁K
  have hcp1 : s₁.canPlace c (Sum.inl a) = true := by
    show ((s₁.piles a).isEmpty && decide (c.rank = Rank.king)) = true
    rw [hs₁A, decide_eq_true hking]
    rfl
  have hstep2 : State.step s₁ (Move.tabToTab c (Sum.inl a)) = some st := by
    simp only [State.step, hhold, hcp1, hrunK]
    refine congrArg some (?_ :
      (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inl a) = st)
    rw [show (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inl a)
        = (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
            (below c (s₁.piles k).faceUp))).setPile a
            ⟨[], c :: tr⟩ from rfl]
    refine State.ext (funext fun σ => ?_) (funext fun y => ?_) ?_ ?_ ?_
    · rw [setPile_found, setPile_found, hsF σ]
    · by_cases hya : y = a
      · rw [hya]
        show (if a = a then ⟨[], c :: tr⟩
          else (if a = k then
              Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
            else s₁.piles a)) = st.piles a
        rw [ite_eq_left rfl]
        refine Pile.ext ?_ ?_
        · rw [hhidden]
        · rw [hface]
      · by_cases hyk : y = k
        · rw [hyk]
          show (if k = a then ⟨[], c :: tr⟩
            else (if k = k then
                Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
              else s₁.piles k)) = st.piles k
          rw [ite_eq_right hka, ite_eq_left rfl, hbelowK]
          cases hF2 : (st.piles k).faceUp with
          | nil =>
              rw [afterRunRemoved_empty_eq _ (hKhidden.trans (hKE hF2))]
              exact Pile.ext (hKE hF2).symm hF2.symm
          | cons w r₂ =>
              exact Pile.ext hKhidden hF2.symm
        · show (if y = a then ⟨[], c :: tr⟩
            else (if y = k then
                Pile.afterRunRemoved (s₁.piles k) (below c (s₁.piles k).faceUp)
              else s₁.piles y)) = st.piles y
          rw [ite_eq_right hya, ite_eq_right hyk]
          exact hkeep y hya hyk
    · exact hsS
    · exact hsW
    · exact hsD
  simp only [State.run, hstep2]

/-- The under-seat slide's whole-segment relocation round trip. -/
private theorem tabToTab_under_rtp {st : State} {c : Card} {b : Base} {a k : Anchor}
    {z : Card} {tr : List Card} {s₁ : State}
    (hs₁ : s₁ = (st.setPile a
        (Pile.afterRunRemoved (st.piles a) (below c (st.piles a).faceUp))).putRun
      (fromCard c (st.piles a).faceUp) b)
    (hrt : fromCard c (st.piles a).faceUp = c :: tr)
    (hz : lastOf (below c (st.piles a).faceUp) = some z)
    (hsit : canSitOn c z = true)
    (hhold : s₁.pileHolding c = some k)
    (hsA : s₁.piles a = ⟨(st.piles a).hidden, below c (st.piles a).faceUp⟩)
    (hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
      (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩)
    (hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y)
    (hcN : c ∉ (st.piles k).faceUp)
    (hka : k ≠ a)
    (hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z)
    (hzK : (st.piles k).top ≠ some z)
    (hKE : (st.piles k).faceUp = [] → (st.piles k).hidden = []) :
    s₁.run [Move.tabToTab c (Sum.inr z)] = some st := by
  obtain ⟨hsF, hsS, hsW, hsD, hKfaceUp, hKhidden, hbelowK, hrunK⟩ :=
    tabToTab_landing_facts hs₁ hrt hcN hs₁K
  have haTop : (s₁.piles a).top = some z := by
    show lastOf ((s₁.piles a).faceUp) = some z
    rw [show (s₁.piles a).faceUp = below c (st.piles a).faceUp from
      congrArg (fun p => p.faceUp) hsA]
    exact hz
  have hsTop : s₁.pileOfTop z = some a := by
    show firstWhere (fun x => decide ((s₁.piles x).top = some z)) Anchor.all = some a
    exact firstWhere_find (Anchor.mem_all a) (decide_eq_true haTop)
      (fun y hy hyne => decide_false_of_not (hzOnly y hyne))
  have hmidA : (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles a = s₁.piles a := by
    show (if a = k then Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp) else s₁.piles a) = _
    rw [ite_eq_right (Ne.symm hka)]
  have hmidTop : ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles a).top = some z := by
    rw [hmidA]
    exact haTop
  have hknotN : ((s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).piles k).top ≠ some z := by
    show (if k = k then Pile.afterRunRemoved (s₁.piles k)
        (below c (s₁.piles k).faceUp) else s₁.piles k).top ≠ some z
    rw [ite_eq_left rfl, hbelowK]
    cases hF2 : (st.piles k).faceUp with
    | nil =>
        rw [afterRunRemoved_empty_eq _ (hKhidden.trans (hKE hF2))]
        intro htop
        nomatch htop
    | cons w r₂ =>
        exact fun htop => hzK (show (st.piles k).top = some z from by
          show lastOf ((st.piles k).faceUp) = some z
          rw [hF2]
          exact htop)
  have hzN' : (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
      (below c (s₁.piles k).faceUp)) : State).pileOfTop z = some a :=
    topPin2 hmidTop (fun y hya hyk => by
      show (if y = k then Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp) else s₁.piles y) = s₁.piles y
      rw [ite_eq_right hyk])
      hknotN (fun y hya _ => hzOnly y hya)
  have hcp1 : s₁.canPlace c (Sum.inr z) = true := by
    show (match s₁.pileOfTop z with
      | some _ => canSitOn c z | none => false) = true
    rw [hsTop]
    exact hsit
  have hstep2 : State.step s₁ (Move.tabToTab c (Sum.inr z)) = some st := by
    simp only [State.step, hhold, hcp1, hrunK]
    refine congrArg some (?_ :
      (s₁.setPile k (Pile.afterRunRemoved (s₁.piles k)
          (below c (s₁.piles k).faceUp))).putRun (c :: tr) (Sum.inr z) = st)
    refine State.ext (funext fun σ => ?_) (funext fun y => ?_) ?_ ?_ ?_
    · rw [putRun_found, setPile_found, hsF σ]
    · by_cases hya : y = a
      · rw [hya, putRun_piles_inr_self _ _ _ _ hzN', hmidA]
        refine Pile.ext ?_ ?_
        · exact congrArg (fun p => p.hidden) hsA
        · have hj := tfc_below_fromCard c ((st.piles a).faceUp)
          rw [hrt] at hj
          rw [show (s₁.piles a).faceUp = below c (st.piles a).faceUp from
            congrArg (fun p => p.faceUp) hsA]
          exact hj
      · by_cases hyk : y = k
        · rw [hyk, putRun_piles_inr_ne _ _ _ _ hzN' hka,
            setPile_piles_self, hbelowK]
          cases hF2 : (st.piles k).faceUp with
          | nil =>
              rw [afterRunRemoved_empty_eq _ (hKhidden.trans (hKE hF2))]
              exact Pile.ext (hKE hF2).symm hF2.symm
          | cons w r₂ =>
              exact Pile.ext hKhidden hF2.symm
        · rw [putRun_piles_inr_ne _ _ _ _ hzN' hya,
            setPile_piles_ne hyk]
          exact hkeep y hya hyk
    · rw [putRun_stock, setPile_stock]
      exact hsS
    · rw [putRun_waste, setPile_waste]
      exact hsW
    · rw [putRun_drawStep, setPile_drawStep]
      exact hsD
  simp only [State.run, hstep2]
/-! ## §6. Slide-undo support -/

/-- A suffix of a legal run is legal. -/
private theorem runOK_append_left : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK B = true := by
  intro A
  induction A with
  | nil => intro B h; exact h
  | cons y t ih =>
      intro B h
      exact ih B (runOK_cons_tail h)

/-- A prefix of a legal run is legal. -/
private theorem runOK_append_right : ∀ (A B : List Card),
    runOK (A ++ B) = true → runOK A = true := by
  intro A
  induction A with
  | nil => intro _ _; rfl
  | cons y t ih =>
      intro B h
      match t with
      | [] => rfl
      | w :: t' =>
          have h' : runOK (y :: w :: (t' ++ B)) = true := h
          rw [runOK, Bool.and_eq_true] at h' ⊢
          exact ⟨h'.1, ih B h'.2⟩

/-- The seam fit: in a legal face-up run, each card fits on its
immediate predecessor, anywhere in the list. -/
private theorem runOK_seam : ∀ (A B : List Card) {x c : Card},
    runOK (A ++ x :: c :: B) = true → canSitOn c x = true := by
  intro A
  induction A with
  | nil =>
      intro B x c h
      rw [List.nil_append, runOK, Bool.and_eq_true] at h
      exact h.1
  | cons y t ih =>
      intro B x c h
      exact ih B (runOK_cons_tail h)

/-- A list with a known last element keeps that element adjacent
to the snocced cards. -/
private theorem runOK_adjacent_snoc {P : List Card} {z c : Card}
    (hlast : lastOf P = some z) (hok : runOK (P ++ [c]) = true) :
    canSitOn c z = true := by
  have hc1 : P ++ [c] = (chop P ++ [z]) ++ [c] :=
    congrArg (· ++ [c]) (lastOf_chop hlast)
  have hc2 : (chop P ++ [z]) ++ [c] = chop P ++ [z, c] := by
    rw [List.append_assoc]
    rfl
  rw [hc1.trans hc2] at hok
  exact runOK_seam _ _ hok

/-- A card face-up in one pile tops no other pile. -/
private theorem wf_no_other_top {st : State} {c : Card} {a : Anchor}
    (hwf : st.WF) (hmem : c ∈ (st.piles a).faceUp) (a' : Anchor) (hne : a' ≠ a) :
    (st.piles a').top ≠ some c := by
  intro htop
  have := Pile.mem_of_top htop
  exact (mem_faceUp_unique hwf hmem a' hne).1 this

/-- `c` never lies strictly below itself. -/
private theorem below_not_mem_self {c : Card} : ∀ (l : List Card), c ∉ below c l := by
  intro l
  induction l with
  | nil => intro h; cases h
  | cons y t ih =>
      rw [below]
      split
      · intro h; cases h
      · rename_i hy
        intro h
        rcases List.mem_cons.1 h with hyc | hm
        · exact absurd hyc.symm hy
        · exact ih hm

/-- A run of one step read back as a step. -/
private theorem step_of_run_one {st : State} {m : Move} {s : State}
    (h : st.run [m] = some s) : State.step st m = some s := by
  cases hstep : State.step st m with
  | none =>
      have h2 : (match State.step st m with
          | some st' => some st'
          | none => none) = some s := h
      rw [hstep] at h2
      exact absurd h2 (by simp)
  | some t =>
      have h2 : (match State.step st m with
          | some st' => some st'
          | none => none) = some s := h
      rw [hstep] at h2
      exact congrArg some (Option.some.inj h2)

/-- **The bare-king slide inverse, step form.** -/
private theorem step_tabToTab_inverse_bare {st s₁ : State} {c : Card} {b : Base} {a : Anchor}
    (hwf : st.WF) (hh : st.pileHolding c = some a) (hcp : st.canPlace c b = true)
    (hbelow : below c (st.piles a).faceUp = [])
    (hhid : (st.piles a).hidden = []) (hkng : c.rank = Rank.king)
    (hstep : State.step st (Move.tabToTab c b) = some s₁) :
    State.step s₁ (Move.tabToTab c (Sum.inl a)) = some st := by
  obtain ⟨a₂, hht, hct, hfr, hs₁⟩ := step_tabToTab_inv hstep
  have haeq : a₂ = a := by
    have hx : some a = some a₂ := hh.symm.trans hht
    injection hx with hxE
    exact hxE.symm
  rw [haeq] at hs₁ hfr
  obtain ⟨tr, hrt⟩ := fromCard_eq_head_of_mem (pileHolding_mem hh)
  rw [hbelow, afterRunRemoved_empty_eq _ hhid] at hs₁
  cases b with
  | inl k =>
      have hka : k ≠ a := canPlace_inl_target_pile_ne hcp (pileHolding_mem hh)
      have hcN : c ∉ (st.piles k).faceUp :=
        (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ hyk, setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ (Ne.symm hka), setPile_piles_self]
        intro hcon
        cases hcon
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inl_self, hrt]
        exact List.mem_cons_self
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      have hs₁A : s₁.piles a = ⟨[], ([] : List Card)⟩ := by
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ (Ne.symm hka), setPile_piles_self]
      have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
          (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
        rw [hs₁, putRun_piles_inl_self]
        obtain ⟨hhE, hfE⟩ := (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1
        refine Pile.ext ?_ ?_
        · rw [hhE]
        · rw [hfE, List.nil_append]
      have hface : (st.piles a).faceUp = c :: tr := by
        have hj := tfc_below_fromCard c ((st.piles a).faceUp)
        rw [hbelow, hrt, List.nil_append] at hj
        exact hj.symm
      exact step_of_run_one
        (tabToTab_bare_rtp hs₁ hrt hface hhid hkng hhold hs₁A hs₁K
          hkeep hcN hka (by
            intro hcon
            have hemp := (Pile.isEmpty_eq (st.piles k)).mp (canPlace_inl hcp).1
            exact hemp.1))
  | inr z' =>
      obtain ⟨k, hk₀, -⟩ := canPlace_inr hcp
      obtain ⟨hka, hcN⟩ := canPlace_inr_seat hwf hh hcp hk₀
      have hmidK : (st.setPile a ⟨[], ([] : List Card)⟩ : State).piles k
          = st.piles k := by
        show (if k = a then ⟨[], ([] : List Card)⟩ else st.piles k) = _
        rw [ite_eq_right hka]
      have hmidAtop : ((st.setPile a ⟨[], ([] : List Card)⟩ : State).piles a).top
          ≠ some z' := by
        show (if a = a then ⟨[], ([] : List Card)⟩ else st.piles a).top
          ≠ some z'
        rw [ite_eq_left rfl]
        intro hcon
        nomatch hcon
      have hseatMid :
          (st.setPile a ⟨[], ([] : List Card)⟩ : State).pileOfTop z'
            = some k :=
          topPin2 (by
              rw [hmidK]
              exact (pileOfTop_top hk₀).2)
            (fun y hyk hya => by
              show (if y = a then ⟨[], ([] : List Card)⟩
                  else st.piles y) = st.piles y
              rw [ite_eq_right hya])
            hmidAtop (fun y hyk _ =>
              wf_no_other_top hwf (lastOf_mem (pileOfTop_top hk₀).2) y hyk)
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid hyk,
          setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid (Ne.symm hka),
          setPile_piles_self]
        intro hcon
        cases hcon
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid, hmidK, hrt]
        exact (List.mem_append).2 (Or.inr List.mem_cons_self)
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      have hs₁A : s₁.piles a = ⟨[], ([] : List Card)⟩ := by
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid (Ne.symm hka),
          setPile_piles_self]
      have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
          (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
        rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid, hmidK]
      have hface : (st.piles a).faceUp = c :: tr := by
        have hj := tfc_below_fromCard c ((st.piles a).faceUp)
        rw [hbelow, hrt, List.nil_append] at hj
        exact hj.symm
      exact step_of_run_one
        (tabToTab_bare_rtp hs₁ hrt hface hhid hkng hhold hs₁A hs₁K
          hkeep hcN hka (by
            intro hcon
            exact absurd hcon (pileOfTop_top hk₀).1))

/-- **The under-seat slide inverse, step form.** -/
private theorem step_tabToTab_inverse_under {st s₁ : State} {c : Card} {b : Base} {a : Anchor}
    {z₀ : Card} {pre' : List Card}
    (hwf : st.WF) (hh : st.pileHolding c = some a) (hcp : st.canPlace c b = true)
    (hbelow : below c (st.piles a).faceUp = z₀ :: pre')
    (hstep : State.step st (Move.tabToTab c b) = some s₁) :
    ∃ z : Card, State.step s₁ (Move.tabToTab c (Sum.inr z)) = some st := by
  obtain ⟨a₂, hht, hct, hfr, hs₁⟩ := step_tabToTab_inv hstep
  have haeq : a₂ = a := by
    have hx : some a = some a₂ := hh.symm.trans hht
    injection hx with hxE
    exact hxE.symm
  rw [haeq] at hs₁ hfr
  obtain ⟨tr, hrt⟩ := fromCard_eq_head_of_mem (pileHolding_mem hh)
  obtain ⟨z, hz⟩ := lastOf_exists (l := z₀ :: pre') (by simp)
  have hzB : lastOf (below c (st.piles a).faceUp) = some z := by
    rw [hbelow]
    exact hz
  have hzin : z ∈ below c (st.piles a).faceUp := lastOf_mem hzB
  have hzmem : z ∈ (st.piles a).faceUp := mem_below _ hzin
  have h1 := tfc_below_fromCard c ((st.piles a).faceUp)
  rw [hbelow, hrt] at h1
  have hrunOK0 : runOK ((st.piles a).faceUp) = true := hwf.runOK_of a
  have hrunlit : runOK ((z₀ :: pre') ++ (c :: tr)) = true := by
    rw [h1]
    exact hrunOK0
  have hrunTail : runOK (c :: tr) = true :=
    runOK_append_left (z₀ :: pre') (c :: tr) hrunlit
  have hfitpre : runOK (((z₀ :: pre') ++ [c]) ++ tr) = true := by
    rw [List.append_assoc]
    have hE : [c] ++ tr = c :: tr := by
      rw [List.cons_append, List.nil_append]
    rw [hE]
    exact hrunlit
  have hsit : canSitOn c z = true :=
    runOK_adjacent_snoc hz
      (runOK_append_right ((z₀ :: pre') ++ [c]) tr hfitpre)
  have hprene : below c (st.piles a).faceUp ≠ [] := by rw [hbelow]; simp
  cases b with
  | inl k =>
      have hka : k ≠ a := canPlace_inl_target_pile_ne hcp (pileHolding_mem hh)
      have hcN : c ∉ (st.piles k).faceUp :=
        (mem_faceUp_unique hwf (pileHolding_mem hh) k hka).1
      have hzK : (st.piles k).top ≠ some z :=
        wf_no_other_top hwf hzmem k hka
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ hyk, setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ (Ne.symm hka),
          setPile_piles_self, hbelow]
        show c ∉ (z₀ :: pre')
        rw [← hbelow]
        exact below_not_mem_self _
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inl_self, hrt]
        exact List.mem_cons_self
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      have hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z := by
        intro y hya
        by_cases hyk : y = k
        · rw [hyk]
          intro htop
          have hmemK : z ∈ (s₁.piles k).faceUp := Pile.mem_of_top htop
          have hkFu : (s₁.piles k).faceUp
              = fromCard c (st.piles a).faceUp := by
            rw [hs₁, putRun_piles_inl_self]
          rw [hkFu, hrt] at hmemK
          rcases List.mem_cons.1 hmemK with heq | htr2
          · rw [heq] at hsit
            obtain ⟨hrank, -⟩ := (canSitOn_eq c c).mp hsit
            omega
          · have hrk := runOK_head_gt hrunTail htr2
            obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp hsit
            omega
        · intro htop
          rw [hkeep y hya hyk] at htop
          exact wf_no_other_top hwf hzmem y hya htop
      have hsA : s₁.piles a = ⟨(st.piles a).hidden, below c (st.piles a).faceUp⟩ := by
        rw [hs₁, putRun_piles_inl_ne _ _ _ _ (Ne.symm hka), setPile_piles_self]
        cases hF : below c (st.piles a).faceUp with
        | nil => exact absurd hF hprene
        | cons w t₂ => rfl
      have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
          (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
        rw [hs₁, putRun_piles_inl_self]
        obtain ⟨hhE, hfE⟩ := (Pile.isEmpty_eq _).mp (canPlace_inl hcp).1
        refine Pile.ext ?_ ?_
        · rw [hhE]
        · rw [hfE, List.nil_append]
      exact ⟨z, step_of_run_one
        (tabToTab_under_rtp hs₁ hrt hzB hsit hhold hsA hs₁K hkeep hcN hka
          hzOnly hzK (by
            intro hcon
            have hemp := (Pile.isEmpty_eq (st.piles k)).mp (canPlace_inl hcp).1
            exact hemp.1))⟩
  | inr z' =>
      obtain ⟨k, hk₀, -⟩ := canPlace_inr hcp
      obtain ⟨hka, hcN⟩ := canPlace_inr_seat hwf hh hcp hk₀
      have hzK : (st.piles k).top ≠ some z :=
        wf_no_other_top hwf hzmem k hka
      have hz'mem : z' ∈ (st.piles k).faceUp :=
        lastOf_mem (pileOfTop_top hk₀).2
      have hnostK : ∀ y : Anchor, y ≠ k → (st.piles y).top ≠ some z' :=
        fun y hy => wf_no_other_top hwf hz'mem y hy
      have hmidK : (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles k = st.piles k := by
        show (if k = a then Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp) else st.piles k) = _
        rw [ite_eq_right hka]
      have hmidAtop : ((st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).piles a).top
          ≠ some z' := by
        show (if a = a then Pile.afterRunRemoved (st.piles a)
            (below c (st.piles a).faceUp) else st.piles a).top ≠ some z'
        rw [ite_eq_left rfl, hbelow]
        show (⟨(st.piles a).hidden, z₀ :: pre'⟩ : Pile).top ≠ some z'
        intro hcon
        have hlt : lastOf (z₀ :: pre') = some z' := hcon
        rw [hz] at hlt
        injection hlt with hzz'
        have hzc : z' ∈ (st.piles a).faceUp := by
          rw [← hzz']
          exact hzmem
        exact absurd hz'mem ((mem_faceUp_unique hwf hzc k hka).1)
      have hseatMid : (st.setPile a (Pile.afterRunRemoved (st.piles a)
          (below c (st.piles a).faceUp)) : State).pileOfTop z' = some k :=
        topPin2 (by
            rw [hmidK]
            exact (pileOfTop_top hk₀).2)
          (fun y hyk hya => by
            show (if y = a then Pile.afterRunRemoved (st.piles a)
                (below c (st.piles a).faceUp) else st.piles y) = st.piles y
            rw [ite_eq_right hya])
          hmidAtop (fun y hyk _ => hnostK y hyk)
      have hkeep : ∀ y, y ≠ a → y ≠ k → s₁.piles y = st.piles y := by
        intro y hya hyk
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid hyk,
          setPile_piles_ne hya]
      have hca : c ∉ (s₁.piles a).faceUp := by
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid (Ne.symm hka),
          setPile_piles_self, hbelow]
        show c ∉ (z₀ :: pre')
        rw [← hbelow]
        exact below_not_mem_self _
      have hhk : c ∈ (s₁.piles k).faceUp := by
        rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid, hmidK, hrt]
        exact (List.mem_append).2 (Or.inr List.mem_cons_self)
      have hhold : s₁.pileHolding c = some k :=
        holdingPin2 hca (fun y hyk hya => hkeep y hya hyk) hhk
          (fun y hyk hya =>
            (mem_faceUp_unique hwf (pileHolding_mem hh) y hya).1)
      have hzOnly : ∀ y, y ≠ a → (s₁.piles y).top ≠ some z := by
        intro y hya
        by_cases hyk : y = k
        · rw [hyk]
          intro htop
          have hmemK : z ∈ (s₁.piles k).faceUp := Pile.mem_of_top htop
          have hkFu : (s₁.piles k).faceUp
              = (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp := by
            rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid, hmidK]
          rw [hkFu, hrt] at hmemK
          have hzrun2 : z ∈ (st.piles k).faceUp ++ (c :: tr) := hmemK
          rcases (List.mem_append).1 hzrun2 with hL | hR
          · exact absurd hL ((mem_faceUp_unique hwf hzmem k hka).1)
          · rcases List.mem_cons.1 hR with heq | htr2
            · rw [heq] at hsit
              obtain ⟨hrank, -⟩ := (canSitOn_eq c c).mp hsit
              omega
            · have hrk := runOK_head_gt hrunTail htr2
              obtain ⟨hrank, -⟩ := (canSitOn_eq c z).mp hsit
              omega
        · intro htop
          rw [hkeep y hya hyk] at htop
          exact wf_no_other_top hwf hzmem y hya htop
      have hsA : s₁.piles a = ⟨(st.piles a).hidden, below c (st.piles a).faceUp⟩ := by
        rw [hs₁, putRun_piles_inr_ne _ _ _ _ hseatMid (Ne.symm hka),
          setPile_piles_self]
        cases hF : below c (st.piles a).faceUp with
        | nil => exact absurd hF hprene
        | cons w t₂ => rfl
      have hs₁K : s₁.piles k = ⟨(st.piles k).hidden,
          (st.piles k).faceUp ++ fromCard c (st.piles a).faceUp⟩ := by
        rw [hs₁, putRun_piles_inr_self _ _ _ _ hseatMid, hmidK]
      exact ⟨z, step_of_run_one
        (tabToTab_under_rtp hs₁ hrt hzB hsit hhold hsA hs₁K hkeep hcN hka
          hzOnly hzK (by
            intro hcon
            exact absurd hcon (pileOfTop_top hk₀).1))⟩
/-! ## §7. Pair-free inverse steps -/

/-- A `foundToTab` of a card off the pair is pair-free. -/
private theorem notFoundPair_foundToTab {x y : Card} {b : Base}
    (hyx : y ≠ x) (hyt : y ≠ x.twin) :
    NotFoundPair x (Move.foundToTab y b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro b' h; injection h with h1 h2; exact hyx h1
  · intro b' h; injection h with h1 h2; exact hyt h1

/-- A `tabToFound` of a card off the pair is pair-free. -/
private theorem notFoundPair_tabToFound {x y : Card}
    (hyx : y ≠ x) (hyt : y ≠ x.twin) :
    NotFoundPair x (Move.tabToFound y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; injection h with h1; exact hyx h1
  · intro h; injection h with h1; exact hyt h1
  · intro b h; cases h
  · intro b h; cases h

/-- A slide is pair-free whatever its mover. -/
private theorem notFoundPair_tabToTab {x y : Card} {b : Base} :
    NotFoundPair x (Move.tabToTab y b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; cases h
  · intro h; cases h
  · intro b' h; cases h
  · intro b' h; cases h

/-- `c` is not in the chop of a list whose last element is `c`. -/
private theorem not_mem_chop_of_last {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlast : lastOf l = some c) : c ∉ chop l := by
  have hl : l = chop l ++ [c] := lastOf_chop hlast
  rw [hl] at hnd
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.mp hnd
  intro hc
  exact hdisj c hc c (List.mem_cons_self) rfl

/-- The `below` part of a snocced last element. -/
private theorem below_append_snoc_self {front : List Card} {c : Card}
    (h : c ∉ front) : below c (front ++ [c]) = front := by
  induction front with
  | nil => rw [List.nil_append, below_cons, ite_eq_left rfl]
  | cons y t ih =>
      rw [List.cons_append, below_cons]
      have hyc : y ≠ c := fun hcon => h (by rw [hcon]; exact List.mem_cons_self)
      rw [ite_eq_right hyc]
      have hct : c ∉ t := fun hc => h (List.mem_cons_of_mem y hc)
      rw [ih hct]

/-- The part below a last element is exactly the chop. -/
private theorem below_eq_chop_of_last {l : List Card} {c : Card}
    (hnd : l.Nodup) (hlast : lastOf l = some c) : below c l = chop l := by
  have hl : l = chop l ++ [c] := lastOf_chop hlast
  have hnc : c ∉ chop l := not_mem_chop_of_last hnd hlast
  exact (congrArg (below c) hl).trans (below_append_snoc_self hnc)

/-- **Single-letter inverse, no-draw arm.** -/
theorem exists_step_inverse_pairFree_noDraw {x : Card} {u v : State} {m : Move}
    (hwf : u.WF)
    (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m)
    (hmnd : m ≠ Move.draw)
    (hno : NotFoundPair x m) :
    ∃ m' : Move, State.step v m' = some u ∧ NotFoundPair x m' ∧
      reversibleAtW v m' := by
  cases m with
  | draw => exact absurd rfl hmnd
  | wasteToFound c => exact absurd hrev (wasteToFound_not_reversibleAtW u c)
  | wasteToTab c b => exact absurd hrev (wasteToTab_not_reversibleAtW u c b)
  | tabToFound y =>
      have hyx : y ≠ x := fun h => hno.1 (by rw [h])
      have hyt : y ≠ x.twin := fun h => hno.2.1 (by rw [h])
      obtain ⟨hnext, a, hpa, hs⟩ := step_tabToFound_inv hstep
      have hR : tabToFoundR u y = true :=
        (tabToFoundR_iff_reversibleAtW hwf y).mpr hrev
      simp only [tabToFoundR, hnext, hpa] at hR
      cases hchop : chop (u.piles a).faceUp with
      | nil =>
          have hhid : (u.piles a).hidden = [] := by
            cases hhid : (u.piles a).hidden with
            | nil => rfl
            | cons h t =>
                rw [hchop, hhid] at hR
                exact absurd hR (by simp)
          have hking : y.rank = Rank.king := by
            rw [hchop, hhid] at hR
            exact of_decide_eq_true hR
          have hs1 : State.step v (Move.foundToTab y (Sum.inl a)) = some u :=
            step_foundToTab_of_tabToFound_bare hstep hpa hchop hhid hking
          refine ⟨Move.foundToTab y (Sum.inl a), hs1,
            notFoundPair_foundToTab hyx hyt, ?_⟩
          exact ⟨u, [Move.tabToFound y], hs1, run_one hstep⟩
      | cons z0 zs =>
          obtain ⟨z, hz0⟩ := lastOf_exists (l := z0 :: zs) (by simp)
          have hz : lastOf (chop (u.piles a).faceUp) = some z := by
            rw [hchop]
            exact hz0
          have hhh : u.pileHolding y = some a := by
            rw [pileHolding_eq_some_iff hwf]
            exact lastOf_mem (pileOfTop_top hpa).2
          have hndFace : (u.piles a).faceUp.Nodup := runOK_nodup (hwf.runOK_of a)
          have hzBelow : lastOf (below y (u.piles a).faceUp) = some z := by
            have hlast : lastOf (u.piles a).faceUp = some y := (pileOfTop_top hpa).2
            rw [below_eq_chop_of_last hndFace hlast]
            exact hz
          have hsit : canSitOn y z = true :=
            (tfc_seat_parent hwf hhh hzBelow).1
          have hsP : v.piles a =
              Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp) := by
            rw [hs]
            show (if a = a then
                Pile.afterRunRemoved (u.piles a) (chop (u.piles a).faceUp)
                else u.piles a) = _
            rw [ite_eq_left rfl]
          have hsearch : v.pileOfTop z = some a := by
            rw [pileOfTop_eq_some_iff (step_wf hwf hstep)]
            show lastOf (v.piles a).faceUp = some z
            rw [hsP]
            rw [hchop]
            exact hz0
          have hs1 : State.step v (Move.foundToTab y (Sum.inr z)) = some u :=
            step_foundToTab_of_tabToFound_under hstep hpa hz hsit hsearch
          refine ⟨Move.foundToTab y (Sum.inr z), hs1,
            notFoundPair_foundToTab hyx hyt, ?_⟩
          exact ⟨u, [Move.tabToFound y], hs1, run_one hstep⟩
  | foundToTab y b =>
      have hyx : y ≠ x := fun h => hno.2.2.1 b (by rw [h])
      have hyt : y ≠ x.twin := fun h => hno.2.2.2 b (by rw [h])
      have hs1 : State.step v (Move.tabToFound y) = some u :=
        step_tabToFound_of_foundToTab hwf hstep
      refine ⟨Move.tabToFound y, hs1, notFoundPair_tabToFound hyx hyt, ?_⟩
      exact ⟨u, [Move.foundToTab y b], hs1, run_one hstep⟩
  | tabToTab y b =>
      obtain ⟨a, hh, hcp, hfr, hs⟩ := step_tabToTab_inv hstep
      have hR : tabToTabR u y b = true :=
        (tabToTabR_iff_reversibleAtW hwf y b).mpr hrev
      simp only [tabToTabR, hh, hcp] at hR
      cases hbl : below y (u.piles a).faceUp with
      | nil =>
          have hhid : (u.piles a).hidden = [] := by
            cases hhid : (u.piles a).hidden with
            | nil => rfl
            | cons h t =>
                rw [hbl, hhid] at hR
                exact absurd hR (by simp)
          have hking : y.rank = Rank.king := by
            rw [hbl, hhid] at hR
            exact of_decide_eq_true hR
          have hs1 : State.step v (Move.tabToTab y (Sum.inl a)) = some u :=
            step_tabToTab_inverse_bare hwf hh hcp hbl hhid hking hstep
          refine ⟨Move.tabToTab y (Sum.inl a), hs1, notFoundPair_tabToTab, ?_⟩
          exact ⟨u, [Move.tabToTab y b], hs1, run_one hstep⟩
      | cons z pre' =>
          obtain ⟨z', hs1⟩ :=
            step_tabToTab_inverse_under hwf hh hcp hbl hstep
          refine ⟨Move.tabToTab y (Sum.inr z'), hs1, notFoundPair_tabToTab, ?_⟩
          exact ⟨u, [Move.tabToTab y b], hs1, run_one hstep⟩

/-- A pair-free reversible letter leaves both twins' `.inr` seats
verbatim. -/
private theorem seat_eq_of_pairFree_step {u v : State} {x : Card} {m : Move}
    (hwf : u.WF) (hstep : State.step u m = some v)
    (hrev : reversibleAtW u m) (hno : NotFoundPair x m)
    (hx : ∃ z, seatOf u x = some (Sum.inr z))
    (hxt : ∃ z : Card, seatOf u x.twin = some (Sum.inr z.twin)) :
    seatOf v x = seatOf u x ∧ seatOf v x.twin = seatOf u x.twin := by
  have hse_x : seatOf u x ≠ none := by
    obtain ⟨z, hz⟩ := hx
    rw [hz]
    simp
  have hse_xt : seatOf u x.twin ≠ none := by
    obtain ⟨z, hz⟩ := hxt
    rw [hz]
    simp
  have hxEq : seatOf v x = seatOf u x := by
    cases m with
    | draw => exact (chart_draw hstep).1 x
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyx : y ≠ x := fun h => hno.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_x (Ne.symm hyx)
    | foundToTab y base =>
        have hyx : y ≠ x := fun h => hno.2.2.1 base (by rw [h])
        exact pull_seat_change hstep x (Ne.symm hyx)
    | tabToTab y base =>
        obtain ⟨hyx, -⟩ := TwinSpliceComm.tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x
        rwa [ite_eq_right (Ne.symm hyx)] at h
  have hxtEq : seatOf v x.twin = seatOf u x.twin := by
    cases m with
    | draw => exact (chart_draw hstep).1 x.twin
    | wasteToFound y => exact absurd hrev (wasteToFound_not_reversibleAtW u y)
    | wasteToTab y base => exact absurd hrev (wasteToTab_not_reversibleAtW u y base)
    | tabToFound y =>
        have hyt : y ≠ x.twin := fun h => hno.2.1 (by rw [h])
        exact raise_seat_change_of_seated hstep hrev hse_xt (Ne.symm hyt)
    | foundToTab y base =>
        have hyt : y ≠ x.twin := fun h => hno.2.2.2 base (by rw [h])
        exact pull_seat_change hstep x.twin (Ne.symm hyt)
    | tabToTab y base =>
        obtain ⟨-, hyt⟩ := TwinSpliceComm.tabToTab_mover_off hwf hx hxt hstep
        have h := tfc_seat_point_edit hwf hstep hrev x.twin
        rwa [ite_eq_right (Ne.symm hyt)] at h
  exact ⟨hxEq, hxtEq⟩

/-! ## §8. The no-draw reversal -/

/-- **The pair-free reversal theorem, no-draw arm.** -/
theorem pairFreeReversal_noDraw {x : Card} :
    ∀ {u v : State} {z : Card} {play : List Move},
      u.WF →
      seatOf u x = some (Sum.inr z) →
      seatOf u x.twin = some (Sum.inr z.twin) →
      ShufflePlayW u play v →
      (∀ m ∈ play, NotFoundPair x m) →
      (∀ m ∈ play, m ≠ Move.draw) →
      PairFreeOrbit x v u := by
  intro u v z play
  induction play generalizing u z with
  | nil =>
      intro hwf hx hxt hplay hno hnd
      cases hplay
      exact pairFreeOrbit_refl x _
  | cons m rest ih =>
      intro hwf hx hxt hplay hno hnd
      cases hplay with
      | @cons _ s1 _ _ _ hrev hstep hrest =>
          have hm : NotFoundPair x m := hno m (by simp)
          have hmd : m ≠ Move.draw := hnd m (by simp)
          obtain ⟨m', hstep', hno', hrev'⟩ :=
            exists_step_inverse_pairFree_noDraw hwf hstep hrev hmd hm
          have hseats :=
            seat_eq_of_pairFree_step hwf hstep hrev hm ⟨z, hx⟩ ⟨z, hxt⟩
          have hwx : seatOf s1 x = some (Sum.inr z) := by rw [hseats.1, hx]
          have hwt : seatOf s1 x.twin = some (Sum.inr z.twin) := by rw [hseats.2, hxt]
          have hwf1 : s1.WF := step_wf hwf hstep
          have ih' := ih hwf1 hwx hwt hrest
            (fun n hn => hno n (List.mem_cons_of_mem m hn))
            (fun n hn => hnd n (List.mem_cons_of_mem m hn))
          have hstepOrbit : PairFreeOrbit x s1 u :=
            pairFreeOrbit_of_play (Walk.cons hrev' hstep' (Walk.nil u)) (by
              intro n hn
              rw [List.mem_singleton.mp hn]
              exact hno')
          exact PairFreeOrbit.trans ih' hstepOrbit




/-! ## §9. Draw-zone projection -/

/-- The recycle's branch catalogue. -/
private theorem recycle_fields (x : State) :
    (x.stock = [] → x.waste = [] → State.recycle x = x) ∧
    (x.stock = [] → x.waste ≠ [] →
      State.recycle x = { x with stock := x.waste.reverse, waste := [] }) ∧
    (x.stock ≠ [] → State.recycle x = x) := by
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · show (match x.stock with
        | [] => match x.waste with
          | [] => x
          | w => { x with stock := w.reverse, waste := ([] : List Card) }
        | _ => x) = x
    rw [h1, h2]
  · show (match x.stock with
        | [] => match x.waste with
          | [] => x
          | w => { x with stock := w.reverse, waste := ([] : List Card) }
        | _ => x)
      = { x with stock := x.waste.reverse, waste := [] }
    rw [h1]
    show (match x.waste with
      | [] => x
      | w => { x with stock := w.reverse, waste := ([] : List Card) })
      = { x with stock := x.waste.reverse, waste := [] }
    cases hcon : x.waste with
    | nil =>
        rw [hcon] at h2
        exact absurd rfl h2
    | cons a as => rfl
  · obtain ⟨a, as, hcon⟩ := list_cons_of_ne_nil h1
    show (match x.stock with
      | [] => match x.waste with
        | [] => x
        | w => { x with stock := w.reverse, waste := ([] : List Card) }
      | _ => x) = x
    rw [hcon]

/-- Two states with equal draw zones draw to the same dealt stock and
waste, each keeping its own found and tableau. -/
private theorem stepDraw_congr {x y : State}
    (hx1 : y.stock = x.stock) (hx2 : y.waste = x.waste)
    (hx3 : y.drawStep = x.drawStep)
    {s' : State} (hstep : State.step x Move.draw = some s') :
    State.step y Move.draw = some { s' with found := y.found, piles := y.piles } := by
  obtain ⟨r, hru, hrne, hshape⟩ := draw_unfold hstep
  have hrr : (State.recycle y).stock = (State.recycle x).stock ∧
      (State.recycle y).waste = (State.recycle x).waste ∧
      (State.recycle y).drawStep = (State.recycle x).drawStep ∧
      (State.recycle y).found = y.found ∧ (State.recycle y).piles = y.piles := by
    cases hs : y.stock with
    | nil =>
        cases hw : y.waste with
        | nil =>
            have hxs : x.stock = [] := hx1.symm.trans hs
            have hxw : x.waste = [] := hx2.symm.trans hw
            rw [(recycle_fields y).1 hs hw, (recycle_fields x).1 hxs hxw]
            exact ⟨hx1, hx2, hx3, rfl, rfl⟩
        | cons w ws =>
            have hxs : x.stock = [] := hx1.symm.trans hs
            have hxw : x.waste = w :: ws := hx2.symm.trans hw
            have hxr : State.recycle x =
                { x with stock := x.waste.reverse, waste := [] } :=
              (recycle_fields x).2.1 hxs (by rw [hxw]; simp)
            have hyr : State.recycle y =
                { y with stock := y.waste.reverse, waste := [] } :=
              (recycle_fields y).2.1 hs (by rw [hw]; simp)
            rw [hyr, hxr, hxw, hw]
            exact ⟨rfl, rfl, hx3, rfl, rfl⟩
    | cons a as =>
        have hxs : x.stock = a :: as := hx1.symm.trans hs
        have hxr : State.recycle x = x := (recycle_fields x).2.2 (by rw [hxs]; simp)
        have hyr : State.recycle y = y := (recycle_fields y).2.2 (by rw [hs]; simp)
        rw [hyr, hxr]
        exact ⟨hx1, hx2, hx3, rfl, rfl⟩
  have hvne : (State.recycle y).stock ≠ [] := by
    rw [hrr.1, hru]
    exact hrne
  show State.dealStock (State.recycle y) = _
  rw [dealStock_eq_of_ne_nil _ hvne]
  rw [hshape]
  rw [hrr.2.2.1, hrr.1, hrr.2.1, hrr.2.2.2.1, hrr.2.2.2.2, hru]

/-- No letter changes the deal quantum. -/
private theorem step_drawStep {u u' : State} {m : Move}
    (h : State.step u m = some u') : u'.drawStep = u.drawStep := by
  cases m with
  | draw => exact draw_drawStep h
  | wasteToFound c =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToFound_inv h
      rw [hs]
      rfl
  | wasteToTab c b =>
      obtain ⟨-, x, xs, hw, hs⟩ := step_wasteToTab_inv h
      rw [hs]
      exact (putCard_keep (st := u) (c := c) (b := b)).2.2.2
  | tabToFound c =>
      obtain ⟨-, a, hp, hs⟩ := step_tabToFound_inv h
      rw [hs]
      rfl
  | foundToTab c b =>
      obtain ⟨c', ht, hc', hcp, hs⟩ := step_foundToTab_inv h
      rw [hs]
      exact (putCard_keep (st := u.setFound c.suit (chop (u.found c.suit)))
        (c := c) (b := b)).2.2.2
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hne, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact (putRun_keep (st := u.setPile a
        (Pile.afterRunRemoved (u.piles a) (below c (u.piles a).faceUp)))
        (run := fromCard c (u.piles a).faceUp) (b := b)).2.2.2

/-- A non-draw, non-waste letter keeps the whole draw zone. -/
private theorem step_zone_keep_of_zoneMove {x y : State} {m : Move}
    (hmd : m ≠ Move.draw)
    (hmw : (∀ c, m ≠ Move.wasteToFound c) ∧ (∀ c b, m ≠ Move.wasteToTab c b))
    (h : State.step x m = some y) :
    y.stock = x.stock ∧ y.waste = x.waste ∧ y.drawStep = x.drawStep := by
  cases m with
  | draw => exact absurd rfl hmd
  | wasteToFound c => exact absurd rfl (hmw.1 c)
  | wasteToTab c b => exact absurd rfl (hmw.2 c b)
  | tabToFound c =>
      obtain ⟨-, a, hp, hs⟩ := step_tabToFound_inv h
      rw [hs]
      exact ⟨rfl, rfl, rfl⟩
  | foundToTab c b =>
      obtain ⟨c', ht, hc', hcp, hs⟩ := step_foundToTab_inv h
      rw [hs]
      exact ⟨(putCard_keep (st := x.setFound c.suit (chop (x.found c.suit)))
          (c := c) (b := b)).2.1,
        (putCard_keep (st := x.setFound c.suit (chop (x.found c.suit)))
          (c := c) (b := b)).2.2.1,
        (putCard_keep (st := x.setFound c.suit (chop (x.found c.suit)))
          (c := c) (b := b)).2.2.2⟩
  | tabToTab c b =>
      obtain ⟨a, hh, hcp, hne, hs⟩ := step_tabToTab_inv h
      rw [hs]
      exact ⟨(putRun_keep (st := x.setPile a
          (Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp)))
          (run := fromCard c (x.piles a).faceUp) (b := b)).2.1,
        (putRun_keep (st := x.setPile a
          (Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp)))
          (run := fromCard c (x.piles a).faceUp) (b := b)).2.2.1,
        (putRun_keep (st := x.setPile a
          (Pile.afterRunRemoved (x.piles a) (below c (x.piles a).faceUp)))
          (run := fromCard c (x.piles a).faceUp) (b := b)).2.2.2⟩

/-- A pure-draw run's landing depends only on the draw zone. -/
private theorem run_draws_zone_transfer {s s' : State} {q : List Move}
    (hq : ∀ m ∈ q, m = Move.draw)
    (hst : s.stock = s'.stock) (hwa : s.waste = s'.waste) (hds : s.drawStep = s'.drawStep)
    {u : State} (hu : s.run q = some u) :
    ∃ u', s'.run q = some u' ∧ u'.stock = u.stock ∧ u'.waste = u.waste ∧
      u'.drawStep = u.drawStep := by
  induction q generalizing s s' with
  | nil =>
      have hsu : s = u := Option.some.inj hu
      subst hsu
      exact ⟨s', rfl, hst.symm, hwa.symm, hds.symm⟩
  | cons m rest ih =>
      have hm : m = Move.draw := hq m (by simp)
      subst hm
      obtain ⟨s1, hstep, hrest⟩ := State.run_cons hu
      have hrestq : ∀ n ∈ rest, n = Move.draw :=
        fun n hn => hq n (List.mem_cons_of_mem Move.draw hn)
      have hstep' : State.step s' Move.draw =
          some { s1 with found := s'.found, piles := s'.piles } :=
        stepDraw_congr hst.symm hwa.symm hds.symm hstep
      obtain ⟨u', hu', h1, h2, h3⟩ :
          ∃ u' : State,
            ({ s1 with found := s'.found, piles := s'.piles } : State).run rest = some u' ∧
              u'.stock = u.stock ∧ u'.waste = u.waste ∧ u'.drawStep = u.drawStep :=
        ih (s := s1) (s' := { s1 with found := s'.found, piles := s'.piles })
          hrestq rfl rfl rfl hrest
      refine ⟨u', ?_, h1, h2, h3⟩
      exact run_cons_shape hstep' hu'

/-- A returning play contains no waste letters (the cycle count never
rises and every waste letter strictly drops it). -/
private theorem run_no_waste {s t : State} {play : List Move}
    (hrun : s.run play = some t) (hcc : cycleCount t = cycleCount s) :
    ∀ m ∈ play, (∀ c, m ≠ Move.wasteToFound c) ∧ (∀ c b, m ≠ Move.wasteToTab c b) := by
  induction play generalizing s with
  | nil => intro m hm; cases hm
  | cons m rest ih =>
      intro n hn
      obtain ⟨s1, hstep, hrest⟩ := State.run_cons hrun
      have hle1 : cycleCount s1 ≤ cycleCount s := cycleCount_step hstep
      have hle2 : cycleCount t ≤ cycleCount s1 :=
        mono_run cycleCount (fun _ _ _ hst => cycleCount_step hst) hrest
      have hcc1 : cycleCount s1 = cycleCount s := by omega
      rcases List.mem_cons.mp hn with rfl | hmem
      · refine ⟨?_, ?_⟩
        · intro c hcon
          rw [hcon] at hstep
          have := cycleCount_step_wasteToFound hstep
          omega
        · intro c b hcon
          rw [hcon] at hstep
          have := cycleCount_step_wasteToTab hstep
          omega
      · exact ih hrest (hcc.trans hcc1.symm) n hmem

/-- Filtering a play to its draw letters preserves its final draw zone,
provided the play has no waste letters. -/
private theorem run_filter_draw_zone {s t : State} {play : List Move}
    (hrun : s.run play = some t)
    (hnoWaste : ∀ m ∈ play,
      (∀ c, m ≠ Move.wasteToFound c) ∧ (∀ c b, m ≠ Move.wasteToTab c b)) :
    ∃ u, s.run (play.filter (fun m => decide (m = Move.draw))) = some u ∧
      u.stock = t.stock ∧ u.waste = t.waste ∧ u.drawStep = t.drawStep := by
  induction play generalizing s with
  | nil =>
      have hst : s = t := Option.some.inj hrun
      subst hst
      exact ⟨s, rfl, rfl, rfl, rfl⟩
  | cons m rest ih =>
      obtain ⟨s1, hstep, hrest⟩ := State.run_cons hrun
      have hnoTail : ∀ n ∈ rest,
          (∀ c, n ≠ Move.wasteToFound c) ∧ (∀ c b, n ≠ Move.wasteToTab c b) :=
        fun n hn => hnoWaste n (List.mem_cons_of_mem m hn)
      by_cases hm : m = Move.draw
      · have hfilter : (m :: rest).filter (fun m => decide (m = Move.draw)) =
            m :: rest.filter (fun m => decide (m = Move.draw)) := by
          simp [hm]
        obtain ⟨u, hu, h1, h2, h3⟩ := ih hrest hnoTail
        refine ⟨u, ?_, h1, h2, h3⟩
        rw [hfilter]
        have hstep' : State.step s Move.draw = some s1 := by
          rw [← hm]
          exact hstep
        rw [hm]
        exact run_cons_shape hstep' hu
      · have hfilter : (m :: rest).filter (fun m => decide (m = Move.draw)) =
            rest.filter (fun m => decide (m = Move.draw)) := by
          simp [hm]
        obtain ⟨u, hu, h1, h2, h3⟩ := ih hrest hnoTail
        have hzone := step_zone_keep_of_zoneMove hm (hnoWaste m (by simp)) hstep
        obtain ⟨u', hu', h1', h2', h3'⟩ :=
          run_draws_zone_transfer (s := s1) (s' := s)
            (q := rest.filter (fun m => decide (m = Move.draw)))
            (by intro n hn; exact of_decide_eq_true (List.mem_filter.mp hn).2)
            hzone.1 hzone.2.1 hzone.2.2 hu
        refine ⟨u', ?_, h1'.trans h1, h2'.trans h2, h3'.trans h3⟩
        rw [hfilter]
        exact hu'

/-- A pure-draw run keeps the board verbatim. -/
private theorem run_draws_piles_found {s t : State} {q : List Move}
    (hq : ∀ m ∈ q, m = Move.draw) (hrun : s.run q = some t) :
    t.piles = s.piles ∧ t.found = s.found := by
  induction q generalizing s with
  | nil =>
      have hst : s = t := Option.some.inj hrun
      subst hst
      exact ⟨rfl, rfl⟩
  | cons m rest ih =>
      have hm : m = Move.draw := hq m (by simp)
      subst hm
      obtain ⟨s1, hstep, hrest⟩ := State.run_cons hrun
      have hrestq : ∀ n ∈ rest, n = Move.draw :=
        fun n hn => hq n (List.mem_cons_of_mem Move.draw hn)
      obtain ⟨h1, h2⟩ := ih hrestq hrest
      exact ⟨h1.trans (stepDraw_piles hstep), h2.trans (stepDraw_found hstep)⟩

/-- **Every letter of a cycle is reversible at its origin.** -/
private theorem shufflePlayW_of_cycle_segment {s : State} {c : List Move}
    (hcyc : s.run c = some s) :
    ∀ {pre seg : List Move} {t : State},
      s.run pre = some t → c = pre ++ seg → ShufflePlayW t seg s := by
  intro pre seg
  induction seg generalizing pre with
  | nil =>
      intro t hpre hdec
      have hpre' : s.run pre = some s := by
        have h := hcyc
        rw [hdec, List.append_nil] at h
        exact h
      have htu : t = s := Option.some.inj (hpre.symm.trans hpre')
      rw [htu]
      exact Walk.nil s
  | cons m rest ih =>
      intro t hpre hdec
      have hcyc' : s.run (pre ++ (m :: rest)) = some s := by
        rw [← hdec]
        exact hcyc
      obtain ⟨t0, hpre0, hrest0⟩ := run_append_split s pre (m :: rest) s hcyc'
      have ht0 : t0 = t := Option.some.inj (hpre0.symm.trans hpre)
      rw [ht0] at hrest0
      obtain ⟨t1, hstep, hrest⟩ := State.run_cons hrest0
      have hpre' : s.run (pre ++ [m]) = some t1 :=
        run_append s pre [m] t t1 hpre (run_one hstep)
      have hdec' : c = (pre ++ [m]) ++ rest := by
        rw [hdec, List.append_assoc]
        rfl
      have hrev : reversibleAtW t m :=
        ⟨t1, rest ++ pre, hstep, run_append t1 rest pre s t hrest hpre⟩
      exact Walk.cons hrev hstep (ih hpre' hdec')

/-- **The draw cycle walk.** -/
private theorem shufflePlayW_of_draw_cycle {u v : State} {q : List Move}
    (hstep : State.step u Move.draw = some v)
    (hrun : v.run q = some u) :
    ShufflePlayW v q u := by
  have hcyc : u.run (Move.draw :: q) = some u :=
    run_cons_shape hstep hrun
  exact shufflePlayW_of_cycle_segment hcyc (pre := [Move.draw]) (seg := q)
    (t := v) (run_one hstep) rfl

/-- **The draw inverse orbit.**  A reversible draw at a `WF` position
is pair-free reversible. -/
theorem draw_inverse_orbit {x : Card} {u v : State}
    (hwf : u.WF)
    (hstep : State.step u Move.draw = some v)
    (hrev : reversibleAtW u Move.draw) :
    PairFreeOrbit x v u := by
  obtain ⟨w, p, hstep', hrun⟩ := hrev
  have hwv : w = v := Option.some.inj (hstep'.symm.trans hstep)
  rw [hwv] at hrun
  have hcc : cycleCount u = cycleCount v := (draw_cycleCount hstep).symm
  have hnoWaste := run_no_waste hrun hcc
  obtain ⟨u', hqrun, hst, hwa, hds⟩ := run_filter_draw_zone hrun hnoWaste
  have hboard : u'.piles = v.piles ∧ u'.found = v.found :=
    run_draws_piles_found
      (by intro m hm; exact of_decide_eq_true (List.mem_filter.mp hm).2) hqrun
  have hstate : u' = u :=
    State.ext (hboard.2.trans (stepDraw_found hstep))
      (hboard.1.trans (stepDraw_piles hstep)) hst hwa hds
  rw [hstate] at hqrun
  have hwalk : ShufflePlayW v (p.filter (fun m => decide (m = Move.draw))) u :=
    shufflePlayW_of_draw_cycle hstep hqrun
  exact pairFreeOrbit_of_play hwalk (by
    intro m hm
    have hm' := (List.mem_filter.mp hm).2
    have hmd : m = Move.draw := of_decide_eq_true hm'
    rw [hmd]
    simp [NotFoundPair])

/-! ## §10. The full pair-free reversal theorem -/

/-- **The pair-free reversal theorem.** -/
theorem pairFreeReversal {x : Card} : PairFreeReversal x := by
  intro u v z play
  induction play generalizing u z with
  | nil =>
      intro hwf hx hxt hplay hno
      cases hplay
      exact pairFreeOrbit_refl x _
  | cons m rest ih =>
      intro hwf hx hxt hplay hno
      cases hplay with
      | @cons _ s1 _ _ _ hrev hstep hrest =>
          have hm : NotFoundPair x m := hno m (by simp)
          have hseats :=
            seat_eq_of_pairFree_step hwf hstep hrev hm ⟨z, hx⟩ ⟨z, hxt⟩
          have hwx : seatOf s1 x = some (Sum.inr z) := by rw [hseats.1, hx]
          have hwt : seatOf s1 x.twin = some (Sum.inr z.twin) := by rw [hseats.2, hxt]
          have hwf1 : s1.WF := step_wf hwf hstep
          have ih' := ih hwf1 hwx hwt hrest
            (fun n hn => hno n (List.mem_cons_of_mem m hn))
          by_cases hmd : m = Move.draw
          · have hstepD : State.step u Move.draw = some s1 := by
              rw [← hmd]
              exact hstep
            have hrevD : reversibleAtW u Move.draw := by
              rw [← hmd]
              exact hrev
            have horbit : PairFreeOrbit x s1 u :=
              draw_inverse_orbit hwf hstepD hrevD
            exact PairFreeOrbit.trans ih' horbit
          · obtain ⟨m', hstep', hno', hrev'⟩ :=
              exists_step_inverse_pairFree_noDraw hwf hstep hrev hmd hm
            have horbit : PairFreeOrbit x s1 u :=
              pairFreeOrbit_of_play (Walk.cons hrev' hstep' (Walk.nil u)) (by
                intro n hn
                rw [List.mem_singleton.mp hn]
                exact hno')
            exact PairFreeOrbit.trans ih' horbit

/-! ## §11. Audit -/

/-- The exact task-facing name of the full reversal theorem. -/
theorem pairFreeReversal_proved {x : Card} : PairFreeReversal x := pairFreeReversal

end TwinPairFreeRev

#print axioms TwinPairFreeRev.upCards_nodup
#print axioms TwinPairFreeRev.posOf_take_of_mem
#print axioms TwinPairFreeRev.posOf_last_eq_length_sub_one
#print axioms TwinPairFreeRev.found_chop_length_eq_rank
#print axioms TwinPairFreeRev.step_foundToTab_of_tabToFound_under
#print axioms TwinPairFreeRev.step_tabToFound_of_foundToTab
#print axioms TwinPairFreeRev.exists_step_inverse_pairFree_noDraw
#print axioms TwinPairFreeRev.pairFreeReversal_noDraw
#print axioms TwinPairFreeRev.draw_inverse_orbit
#print axioms TwinPairFreeRev.pairFreeReversal
#print axioms TwinPairFreeRev.pairFreeReversal_proved