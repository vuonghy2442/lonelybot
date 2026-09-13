import Klondike.Move

/-!
# Reveal-arm crux validation

The successor's new edge `r → hiddenBase a` needs the dealt-parent
decomposition: from `topHidden a = some r` and the boundary's
second-card fact, the pile's deal slice decomposes as
`t ++ d₂ :: r :: rest`.  Machine-checking the list work.

(`head?_rev` is a local copy of the `head?_reverse_eq_getLast?`
landed in Move.lean this session — the olean predates the edit.)
-/

theorem head?_rev {α : Type} : ∀ (l : List α), l.reverse.head? = l.getLast? := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b u =>
      cases hrev : (b :: u).reverse with
      | nil =>
        exfalso
        have ht := congrArg List.reverse hrev
        rw [List.reverse_reverse] at ht
        simp at ht
      | cons z zs =>
        rw [show (a :: b :: u).reverse = z :: (zs ++ [a]) from by
          rw [List.reverse_cons, hrev, List.cons_append]]
        rw [hrev] at ih
        exact ih

theorem hidden_parent_adjacent {st : State} {a : Anchor} {r d₂ : Card}
    (hta : st.topHidden a = some r)
    (hhb : ((st.hidden a).reverse.drop 1).head? = some d₂) :
    ∃ t rest, st.deal.piles a = t ++ d₂ :: r :: rest := by
  simp only [State.topHidden, State.hidden] at hta
  obtain ⟨s, hs⟩ := List.getLast?_eq_some_iff.mp hta
  simp only [State.hidden] at hhb
  rw [hs, List.reverse_append,
    show (([r] : List Card).reverse ++ s.reverse).drop 1 = s.reverse from rfl] at hhb
  obtain ⟨u, hu⟩ :=
    List.getLast?_eq_some_iff.mp (by rw [← head?_rev s]; exact hhb)
  refine ⟨u, (st.deal.piles a).drop (st.depths a), ?_⟩
  refine (List.take_append_drop (st.depths a) (st.deal.piles a)).symm.trans ?_
  rw [hs, hu, List.append_assoc, List.append_assoc]
  rfl

/-- info: 'hidden_parent_adjacent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hidden_parent_adjacent
