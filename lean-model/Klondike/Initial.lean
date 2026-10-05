import Klondike.Bridge
import Klondike.Kit

/-!
# The initial state — exhibiting WF states

Every theorem so far is quantified over `st.WF` states that were never
exhibited: without a constructor, the entire development risks
vacuity.  This module builds the standard game — deal splitting, the
initial board (each pile's top dealt card face-up on the boundary),
empty foundations, fresh stock — and states `initial_wf`.

It also carries runnable sanity checks (`by decide`), the seed of the
cross-validation oracle: the model executes.
-/

/-- Where pile `a`'s slice starts in the deal list (0, 1, 3, 6, 10,
15, 21 — the triangular numbers; the 28 dealt cards precede the
24-card stock). -/
def Anchor.start : Anchor → Nat
  | .p0 => 0 | .p1 => 1 | .p2 => 3 | .p3 => 6 | .p4 => 10 | .p5 => 15 | .p6 => 21

/-- Deal from a card list: pile `a` takes the next `a.toIdx + 1`
cards, the remainder is the stock.  Any list works; well-formedness
needs 52 distinct cards. -/
def Deal.ofList (l : List Card) : Deal where
  piles := fun a => (l.drop a.start).take (a.toIdx + 1)
  stock := l.drop 28

/-- The standard deal: the universe order, split triangularly. -/
def Deal.standard : Deal := Deal.ofList Card.universe

/-- The base a pile's top dealt card sits on: the card beneath it, or
the anchor for the single-card pile. -/
def initBase (d : Deal) (a : Anchor) : Base :=
  match a.toIdx with
  | 0 => Sum.inl a
  | k + 1 => match (d.piles a)[k]? with
    | some under => Sum.inr under
    | none => Sum.inl a

/-- One deal step: attach pile `a`'s top dealt card on its base (a
no-op for an empty pile). -/
def initStep (d : Deal) (bd : Board) (a : Anchor) : Board :=
  match (d.piles a).getLast? with
  | some top => (bd.attach (initBase d a) top).getD bd
  | none => bd

/-- The initial board: each pile's top dealt card, face-up, sitting
on the boundary (the card beneath it, or the anchor for the
single-card pile). -/
def initialBoard (d : Deal) : Board :=
  Anchor.all.foldl (initStep d) Board.empty

/-- The initial state of a dealt game: hidden boundary at `a.toIdx`
per pile, foundations empty, stock fresh at the start of its first
pass. -/
def State.initial (d : Deal) (drawStep : Nat) : State where
  deal := d
  board := initialBoard d
  heights := fun _ => 0
  depths := fun a => a.toIdx
  stock := ⟨d.stock, 0⟩
  drawStep := drawStep

/-! ## Statements -/

/-- The `ofList` slices, exposed for rewriting. -/
theorem Deal.ofList_piles (l : List Card) (a : Anchor) :
    (Deal.ofList l).piles a = (l.drop a.start).take (a.toIdx + 1) := rfl

theorem Deal.ofList_stock (l : List Card) :
    (Deal.ofList l).stock = l.drop 28 := rfl

/-- The triangular split reassembles the list: the piles' concatenated
slices followed by the stock is `l` again, so `noDupCards` transfers
wholesale. -/
theorem Deal.ofList_split (l : List Card) :
    (Anchor.all.flatMap (Deal.ofList l).piles) ++ (Deal.ofList l).stock = l := by
  show (Anchor.all.flatMap fun a => (l.drop a.start).take (a.toIdx + 1)) ++ l.drop 28 = l
  simp only [Anchor.all, List.flatMap_cons, List.flatMap_nil, Anchor.start, Anchor.toIdx,
    Nat.reduceAdd, List.append_nil]
  rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc,
    take_drop_chunk l 21 7 28 (by omega), take_drop_chunk l 15 6 21 (by omega),
    take_drop_chunk l 10 5 15 (by omega), take_drop_chunk l 6 4 10 (by omega),
    take_drop_chunk l 3 3 6 (by omega), take_drop_chunk l 1 2 3 (by omega),
    take_drop_chunk l 0 1 1 (by omega), List.drop_zero]

/-- `ofList` on 52 distinct cards is well-formed (lengths by the
triangular split, distinctness preserved by `drop`/`take`). -/
theorem Deal.ofList_wf {l : List Card} (hlen : l.length = 52) (hnd : noDupCards l) :
    (Deal.ofList l).WF := by
  refine ⟨fun a => ?_, ?_, ?_⟩
  · rw [Deal.ofList_piles, List.length_take, List.length_drop, hlen]
    cases a <;> decide
  · rw [Deal.ofList_stock, List.length_drop, hlen]
  · rw [Deal.ofList_split]
    exact hnd

/-- The step spec: one fold step either keeps a base's top or sets it
to the pile's top dealt card. -/
theorem initStep_topOf (d : Deal) (bd : Board) (a : Anchor) (b : Base) (c : Card)
    (h : (initStep d bd a).topOf b = some c) :
    bd.topOf b = some c ∨ (b = initBase d a ∧ (d.piles a).getLast? = some c) := by
  unfold initStep at h
  cases hgt : (d.piles a).getLast? with
  | none =>
    rw [hgt] at h
    exact Or.inl h
  | some top =>
    rw [hgt] at h
    have h2 : ((bd.attach (initBase d a) top).getD bd).topOf b = some c := h
    cases hat : bd.attach (initBase d a) top with
    | none =>
      rw [hat] at h2
      exact Or.inl h2
    | some bd' =>
      rw [hat] at h2
      have h' : bd'.topOf b = some c := h2
      by_cases hbb : b = initBase d a
      · subst hbb
        rw [Board.attach_topOf bd (initBase d a) top hat] at h'
        rw [Option.some.injEq] at h'
        exact Or.inr ⟨rfl, congrArg some h'⟩
      · rw [Board.attach_topOf_ne bd (initBase d a) top hat hbb] at h'
        exact Or.inl h'

/-- The fold spec: the final board's tops come either from the seed
or from some pile's top dealt card. -/
theorem initFold_topOf (d : Deal) : ∀ (as : List Anchor) (bs : Board) (b : Base) (c : Card),
    (as.foldl (initStep d) bs).topOf b = some c →
    bs.topOf b = some c ∨ ∃ a ∈ as, b = initBase d a ∧ (d.piles a).getLast? = some c := by
  intro as
  induction as with
  | nil => intro bs b c h; exact Or.inl h
  | cons a rest ih =>
    intro bs b c h
    rw [List.foldl_cons] at h
    rcases ih (initStep d bs a) b c h with hold | ⟨a', ha', hbq, hgt⟩
    · rcases initStep_topOf d bs a b c hold with hold' | ⟨hbq, hgt⟩
      · exact Or.inl hold'
      · exact Or.inr ⟨a, List.mem_cons_self, hbq, hgt⟩
    · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hbq, hgt⟩

/-- The initial board's tops are exactly the piles' top dealt cards. -/
theorem initialBoard_topOf (d : Deal) (b : Base) (c : Card)
    (h : (initialBoard d).topOf b = some c) :
    ∃ a ∈ Anchor.all, b = initBase d a ∧ (d.piles a).getLast? = some c := by
  rcases initFold_topOf d Anchor.all Board.empty b c h with hold | hex
  · rw [Board.empty_topOf] at hold; simp at hold
  · exact hex

/-! ## The initial board seats every pile's top (the construction half)

`initialBoard_topOf` above analyzes an edge; the converse — the fold
really writes every pile's top seat — is the forward seating theorem
the reachability fence (witnesses/KingAnchorReachProbe.lean) and the
wave-20 reachable-corner work need.  The proof carries the fold's
running image: every written seat is a processed pile's top dealt
card at its own `initBase`, every processed pile's top sits at its
base.  (Moved from the reach probe, wave-20, where it was private and
in-file; unchanged otherwise.) -/

/-- The last element, by its index (the element at `length - 1` is the
last) — the converse of `getLast?_index`. -/
theorem getLast?_of_index : ∀ (l : List Card) (c : Card),
    l[l.length - 1]? = some c → l.getLast? = some c := by
  intro l
  induction l with
  | nil => intro c h; simp at h
  | cons x t ih =>
      intro c h
      cases t with
      | nil =>
          have hxc : x = c := by
            have hh := h
            simp only [List.length_cons, List.length_nil] at hh
            exact Option.some.inj hh
          rw [hxc]
          rfl
      | cons y u =>
          have hc : (y :: u)[(y :: u).length - 1]? = some c := by
            have hh := h
            rw [show (x :: y :: u).length - 1 = ((y :: u).length - 1) + 1 from by
                simp only [List.length_cons]
                omega] at hh
            rw [List.getElem?_cons_succ] at hh
            exact hh
          have hlast : (y :: u).getLast? = some c := ih c hc
          have hcons : (x :: y :: u).getLast? = (y :: u).getLast? := rfl
          rw [hcons]
          exact hlast

/-- The running board image during the initial dealing: every seat
written so far is a processed pile's top dealt card at its own base,
and every processed pile's top sits at its base. -/
private def InitImg (d : Deal) (proc : List Anchor) (bd : Board) : Prop :=
  (∀ a ∈ proc, bd.topOf (initBase d a) = (d.piles a).getLast?) ∧
  (∀ b c, bd.topOf b = some c →
    ∃ a, a ∈ proc ∧ b = initBase d a ∧ (d.piles a).getLast? = some c)

private theorem initImg_empty : InitImg d [] Board.empty := by
  refine ⟨fun a ha => absurd ha (by simp), ?_⟩
  intro b c hb
  rw [Board.empty_topOf] at hb
  exact absurd hb (by simp)

/-- The pile index decides the anchor. -/
private theorem anchor_toIdx_inj {a a' : Anchor} (h : a.toIdx = a'.toIdx) :
    a = a' := by
  cases a <;> cases a' <;> simp_all [Anchor.toIdx]

/-- The dealt under-card form of `initBase`: an anchor for `p0`, the
under-card otherwise (WF pile lengths keep the index in range). -/
private theorem initBase_shape (d : Deal) (hd : d.WF) (a : Anchor) :
    a = Anchor.p0 ∨ ∃ u, initBase d a = Sum.inr u ∧ u ∈ d.piles a := by
  cases hti : a.toIdx with
  | zero => exact Or.inl (anchor_toIdx_inj hti)
  | succ k =>
      refine Or.inr ?_
      have hlen : (d.piles a).length = k + 2 := by rw [hd.1 a, hti]
      cases hgt : (d.piles a)[k]? with
      | none =>
          have hbad := List.getElem?_eq_none_iff.mp hgt
          rw [hlen] at hbad
          exact absurd hbad (by omega)
      | some u =>
          refine ⟨u, ?_, ?_⟩
          · show initBase d a = Sum.inr u
            simp only [initBase, hti, hgt]
          · exact List.mem_iff_getElem?.mpr ⟨k, hgt⟩

/-- `initBase` is injective in the anchor at a WF deal. -/
private theorem initBase_eq_of_eq (d : Deal) (hd : d.WF) {a a' : Anchor}
    (h : initBase d a = initBase d a') : a = a' := by
  have hp0 : initBase d Anchor.p0 = Sum.inl Anchor.p0 := rfl
  rcases initBase_shape d hd a with hap | ⟨u, hu, hmu⟩
  · rcases initBase_shape d hd a' with hap' | ⟨u', hu', hmu'⟩
    · rw [hap, hap']
    · rw [hap, hp0, hu'] at h
      exact absurd h (by simp)
  · rcases initBase_shape d hd a' with hap' | ⟨u', hu', hmu'⟩
    · rw [hu, hap', hp0] at h
      exact absurd h (by simp)
    · rw [hu, hu'] at h
      have huu : u = u' := Sum.inr.inj h
      have hmu2 : u ∈ d.piles a' := by rw [huu]; exact hmu'
      exact Deal.piles_disj hd hmu hmu2

/-- The next pile's base is free in the running board: all written seats
belong to processed piles. -/
private theorem initBase_free (d : Deal) (hd : d.WF) {proc : List Anchor}
    {bd : Board} (himg : InitImg d proc bd) {a₀ : Anchor} (hnot : a₀ ∉ proc) :
    bd.topOf (initBase d a₀) = none := by
  cases hocc : bd.topOf (initBase d a₀) with
  | none => rfl
  | some c =>
      exfalso
      obtain ⟨a, ham, hbase, -⟩ := himg.2 _ c hocc
      exact hnot (by rw [initBase_eq_of_eq d hd hbase]; exact ham)

/-- One deal step of the initial fold preserves (and extends) the
board image. -/
private theorem initStep_preserves_Img (d : Deal) (hd : d.WF)
    {proc : List Anchor} {bd : Board} {a₀ : Anchor}
    (himg : InitImg d proc bd) (hnot : a₀ ∉ proc) :
    InitImg d (a₀ :: proc) (initStep d bd a₀) := by
  obtain ⟨h1, h2⟩ := himg
  cases hgt : (d.piles a₀).getLast? with
  | none =>
      have hstep : initStep d bd a₀ = bd := by simp only [initStep, hgt]
      rw [hstep]
      refine ⟨?_, ?_⟩
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | hap
        · rw [initBase_free d hd ⟨h1, h2⟩ hnot, hgt]
        · exact h1 a hap
      · intro b c hb
        obtain ⟨a, ham, hbase, hlast⟩ := h2 b c hb
        exact ⟨a, List.mem_cons_of_mem _ ham, hbase, hlast⟩
  | some top =>
      have hfree := initBase_free d hd ⟨h1, h2⟩ hnot
      have hbotnone : bd.bottomOf top = none := by
        refine (Board.bottomOf_eq_none bd top).mpr (fun b' hb => ?_)
        obtain ⟨a, ham, hb, hlast⟩ := h2 b' top hb
        have hmema : top ∈ d.piles a := mem_of_getLast hlast
        have hmem0 : top ∈ d.piles a₀ := mem_of_getLast hgt
        have hae := Deal.piles_disj hd hmem0 hmema
        rw [← hae] at ham
        exact hnot ham
      have hattach : bd.attach (initBase d a₀) top ≠ none :=
        (Board.attach_eq_some_iff bd (initBase d a₀) top).mpr ⟨hfree, hbotnone⟩
      cases hatt : bd.attach (initBase d a₀) top with
      | none => rw [hatt] at hattach; exact absurd hattach (by simp)
      | some bd' =>
          have hstep : initStep d bd a₀ = bd' := by
            simp only [initStep, hgt, hatt, Option.getD]
          rw [hstep]
          refine ⟨?_, ?_⟩
          · intro a ha
            rcases List.mem_cons.mp ha with hhead | hap
            · rw [hhead]
              rw [Board.attach_topOf bd (initBase d a₀) top hatt, hgt]
            · have hne : initBase d a ≠ initBase d a₀ := by
                intro hcon
                exact hnot (by
                  have heq := (initBase_eq_of_eq d hd hcon).symm
                  rw [heq]
                  exact hap)
              rw [Board.attach_topOf_ne bd (initBase d a₀) top hatt hne]
              exact h1 a hap
          · intro b c hb
            by_cases hbb : b = initBase d a₀
            · rw [hbb, Board.attach_topOf bd (initBase d a₀) top hatt,
                Option.some.injEq] at hb
              exact ⟨a₀, (by simp), hbb, by rw [← hb]; exact hgt⟩
            · rw [Board.attach_topOf_ne bd (initBase d a₀) top hatt hbb] at hb
              obtain ⟨a, ham, hbase, hlast⟩ := h2 b c hb
              exact ⟨a, List.mem_cons_of_mem _ ham, hbase, hlast⟩

/-- The fold driver: the whole dealing sequence boards every pile's top
card. -/
private theorem initFold_img_aux (d : Deal) (hd : d.WF) :
    ∀ (as proc : List Anchor) (bd : Board),
    as.Nodup → proc.Nodup → (∀ a ∈ as, a ∉ proc) →
    (∀ a ∈ as, a ∈ Anchor.all) → (∀ a ∈ proc, a ∈ Anchor.all) →
    InitImg d proc bd →
    InitImg d (as.reverse ++ proc) (as.foldl (initStep d) bd) := by
  intro as
  induction as with
  | nil =>
      intro proc bd _ _ _ _ _ himg
      exact himg
  | cons a₀ rest ih =>
      intro proc bd hnd hndp hdis hallp hallproc himg
      have hstep := initStep_preserves_Img d hd himg (hdis a₀ (by simp))
      obtain ⟨ha0nr, hndr⟩ := List.nodup_cons.mp hnd
      have hproc' : (a₀ :: proc).Nodup :=
        List.nodup_cons.mpr ⟨hdis a₀ (by simp), hndp⟩
      have hdis' : ∀ a ∈ rest, a ∉ a₀ :: proc := by
        intro a har hap
        rcases List.mem_cons.mp hap with heq | happ
        · rw [heq] at har
          exact ha0nr har
        · exact hdis a (List.mem_cons_of_mem _ har) happ
      have hallas : ∀ a ∈ rest, a ∈ Anchor.all :=
        fun a har => hallp a (List.mem_cons_of_mem _ har)
      have hallproc' : ∀ a ∈ a₀ :: proc, a ∈ Anchor.all := by
        intro a hap
        rcases List.mem_cons.mp hap with heq | hp
        · rw [heq]
          exact a₀.mem_all
        · exact hallproc a hp
      have hmm := ih (a₀ :: proc) (initStep d bd a₀) hndr hproc' hdis'
        hallas hallproc' hstep
      rw [show (a₀ :: rest).reverse ++ proc = rest.reverse ++ a₀ :: proc from by
        rw [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]]
      exact hmm

/-- **The forward seating theorem**: the initial board seats every
pile's top dealt card at its base (the construction half of
`initialBoard_topOf`). -/
theorem initialBoard_seats (d : Deal) (hd : d.WF) (a : Anchor) :
    (initialBoard d).topOf (initBase d a) = (d.piles a).getLast? := by
  have hall := initFold_img_aux d hd Anchor.all [] Board.empty
    (by decide) (by decide)
    (fun _ _ ha => absurd ha (by simp))
    (fun a _ => a.mem_all) (fun _ ha => absurd ha (by simp))
    initImg_empty
  refine hall.1 a ?_
  exact List.mem_reverse.mpr a.mem_all

/-- A pile of length `k + 2` whose last is `c` and whose `k`-th card
is `under` decomposes with `under` directly beneath `c`. -/
theorem decompose_last : ∀ (k : Nat) (l : List Card) (u c : Card),
    l.length = k + 2 → l[k]? = some u → l.getLast? = some c →
    ∃ t, l = t ++ u :: c :: [] := by
  intro k
  induction k with
  | zero =>
    intro l u c hlen h0 hgt
    cases l with
    | nil => simp at hlen
    | cons a t =>
      cases t with
      | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
      | cons b r =>
        cases r with
        | nil =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
          simp at hgt
          subst h0
          subst hgt
          exact ⟨[], rfl⟩
        | cons z zs =>
          simp only [List.length_cons, List.length_cons] at hlen
          omega
  | succ k ih =>
    intro l u c hlen h0 hgt
    cases l with
    | nil => simp at hlen
    | cons a t =>
      simp only [List.length_cons] at hlen
      simp only [List.getElem?_cons_succ] at h0
      cases t with
      | nil => simp at h0
      | cons x t' =>
        obtain ⟨t₀, ht⟩ := ih (x :: t') u c
          (by simp only [List.length_cons] at hlen ⊢; omega) h0 hgt
        exact ⟨a :: t₀, by rw [ht]; rfl⟩

/-- **The exhibit**: a well-formed deal's initial state is WF — the
theorems' hypotheses are non-vacuous, and `State.initial` is the
witness constructor: the top cards sit on the card they were dealt
onto (deal-adjacency), the fully-revealed single-card pile on its
anchor, the stock is the deal's stock.  The draw step must be positive
(the engine's `NonZeroU8`). -/
theorem initial_wf {d : Deal} (hd : d.WF) (hstep : 0 < drawStep) :
    (State.initial d drawStep).WF := by
  obtain ⟨hlen, hstock, hnd⟩ := hd
  have hdw : d.WF := ⟨hlen, hstock, hnd⟩
  refine ⟨hdw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a
    show a.toIdx ≤ (d.piles a).length
    have := hlen a
    omega
  · intro b c hb
    have hbo : (initialBoard d).bottomOf c = some b := (Board.bottomOf_eq _ _ _).mpr hb
    obtain ⟨a, -, hbq, hgt⟩ := initialBoard_topOf d b c hb
    subst hbq
    refine ⟨hbo, ?_⟩
    cases hti : a.toIdx with
    | zero =>
      simp only [initBase, hti]
      right
      have h1 : (d.piles a).length = 1 := by rw [hlen a, hti]
      cases hl : d.piles a with
      | nil => rw [hl] at h1; simp at h1
      | cons x t =>
        cases t with
        | nil =>
          rw [hl] at hgt
          simp at hgt
          show (d.piles a).head? = some c
          rw [hl]
          exact congrArg some hgt
        | cons y r =>
          rw [hl] at h1
          simp only [List.length_cons, List.length_cons] at h1
          omega
    | succ k =>
      have hlk : (d.piles a).length = k + 2 := by rw [hlen a, hti]
      simp only [initBase, hti]
      cases hget : (d.piles a)[k]? with
      | none =>
        have hn := List.getElem?_eq_none_iff.mp hget
        rw [hlk] at hn
        omega
      | some under =>
        obtain ⟨t, ht⟩ := decompose_last k (d.piles a) under c hlk hget hgt
        have htlen : t.length = k := by
          have hlt : (t ++ under :: c :: []).length = k + 2 := by rw [← ht]; exact hlk
          simp only [List.length_append, List.length_cons, List.length_nil] at hlt
          omega
        have hsub1 : a.toIdx = t.length + 1 := by rw [hti]; omega
        have hsub2 : t.length + 1 - t.length = 1 := by omega
        have htake : (d.piles a).take (a.toIdx) = t ++ [under] := by
          rw [ht, hsub1, List.take_append, take_length_succ_self, hsub2]
          rfl
        refine Or.inl ⟨a, t, [], ht, Or.inl ⟨a, ?_⟩⟩
        show ((d.piles a).take (a.toIdx)).getLast? = some under
        rw [htake, getLast?_append_single]
  · intro c hc
    have hc' : ((initialBoard d).bottomOf c).isSome = true := hc
    cases h : (initialBoard d).bottomOf c with
    | none => rw [h] at hc'; simp at hc'
    | some b =>
      have htop : (initialBoard d).topOf b = some c := (Board.bottomOf_eq _ _ _).mp h
      obtain ⟨a, -, -, hgt⟩ := initialBoard_topOf d b c htop
      exact Cycle.posOf_eq_none (Deal.piles_stock_disj hdw (mem_of_getLast hgt))
  · intro c hc
    simp only [State.onFound] at hc
    rw [show (State.initial d drawStep).heights c.suit = 0 from rfl] at hc
    have : c.rank.toIdx < 0 := of_decide_eq_true hc
    omega
  · intro c hc
    have h0 : (State.initial d drawStep).heights c.suit = 0 := rfl
    rw [h0] at hc
    omega
  · intro c hc a hcm
    have hc' : ((initialBoard d).bottomOf c).isSome = true := hc
    cases h : (initialBoard d).bottomOf c with
    | none => rw [h] at hc'; simp at hc'
    | some b =>
      have htop : (initialBoard d).topOf b = some c := (Board.bottomOf_eq _ _ _).mp h
      obtain ⟨a₀, -, hbq, hgt⟩ := initialBoard_topOf d b c htop
      subst hbq
      have hcm2 : c ∈ (d.piles a).take a.toIdx := hcm
      have hcp : c ∈ d.piles a := List.take_subset _ _ hcm2
      have hcp₀ : c ∈ d.piles a₀ := mem_of_getLast hgt
      have haa : a = a₀ := Deal.piles_disj hdw hcp hcp₀
      subst haa
      have hget : (d.piles a)[a.toIdx]? = some c := by
        have h1 := getLast?_index (d.piles a) c hgt
        rw [hlen a, Nat.add_sub_cancel] at h1
        exact h1
      exact notMem_take_of_get (Deal.pile_noDup hdw a) hget hcm2
  · intro s
    show (0 : Nat) ≤ 13
    exact Nat.zero_le _
  · show (0 : Nat) ≤ d.stock.length
    exact Nat.zero_le _
  · exact hstep
  · exact ⟨noDupCards_append_right hnd, fun c hc => hc⟩

/-! ## Runnable sanity checks — the oracle seed -/

example : (Deal.standard.piles Anchor.p6).length = 7 := by decide

example : Deal.standard.stock.length = 24 := by decide

example : (State.initial Deal.standard 1).depths Anchor.p6 = 6 := by decide

/-- The standard game's single-card pile: its ace of hearts sits
directly on the anchor, and the derived `bottomOf` search finds it —
the matching machinery executes correctly on a concrete state. -/
example : (State.initial Deal.standard 1).board.bottomOf ⟨Suit.heart, Rank.ace⟩
    = some (Sum.inl Anchor.p0) := by decide
