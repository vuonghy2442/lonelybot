import Orig.Combine
import Orig.Integrity

/-!
# Orig — the foundation shuttle join

`FUTURES-ORIG.md` §3, candidate B — the route map's first futures
theorem (the §6 rescue order's smallest commit: B, then A, then
C-by-regimes): the foundation shuttle join.

Two landings of the same waste top `c` — onto `b₁`, onto `b₂` — of a
card that is also next for its foundation (the rung, `u.nextUp c`)
are joined by an explicit `RevEqW` pair of witness plays: the
two-move physical round trip through the foundation.

* `raisedMid` — the shuttle's mid state: the placed `c` lifted onto
  its foundation; everything else about `u` verbatim.
* `raise_tabToFound` — the first leg: from any `wasteToTab`-landing
  `s` of `c`, `tabToFound c` fires (the rung survived the placement —
  no tableau move touches a foundation; the `pileOfTop` search pins
  c's pile exactly — at `u` the card lived in the waste, so `WF`
  puts it in no pile, and the placement moved it into exactly one
  pile; the raise never triggers a reveal — a king sits on an empty
  seat with no hidden stack beneath it, a non-king on a card base
  that remains below), landing at the `raisedMid` state, whatever
  the base was.
* `lower_foundToTab` — the second leg: `foundToTab c b` fires from
  the mid state (its `canPlace` is read against `u`'s verbatim
  piles), landing exactly on the `wasteToTab c b` successor.
* `shuttle_join` — the assembly: `s₁` shuttles to `s₂` (raise, then
  lower onto `b₂`); `s₂` shuttles to `s₁` (raise, then lower onto
  `b₁`); each move's own witness is the mirror leg's head, so both
  plays are `ShufflePlayW`s and the pair is one `RevEqW`.  The
  construction is uniform in `b₁ = b₂`: when the bases coincide the
  same two plays shuttle a state to itself, so the degenerate case
  of the route map (`b₁ = b₂` forces `s₁ = s₂` by step determinism)
  needs no separate branch.

Constructivity: every step is a decidable-shape case split, a list
induction, or an explicit term — the whole file audits
`[propext, Quot.sound]` or fewer, with no `Classical.choice`
anywhere.
-/

/-! ## Card isolation copies — dedup at harvest

`decide_false_of_not`, `firstWhere_find`, and `lastOf_snoc` are
copies of helpers that are *private* in `Orig.Integrity`;
`list_cons_of_ne_nil` mirrors `Orig.Phase`'s private helper; and
`step_wasteToTab_inv`, `putCard_inr_eq`, `putCard_keep` are small
kin of the `putCard`/`step`-inversion shape lemmas owned by the
in-flight `Orig.Irreversible` card.  They live here privately so
this card imports nothing unmerged; at harvest, promote or delete
against the canonical versions. -/




/-- Everything a legal `wasteToTab` needs and hands back: the
guard, and the splice `s = { u.putCard c b with waste := ws }`. -/
private theorem step_wasteToTab_inv {u : State} {c : Card} {b : Base}
    {s : State} (h : State.step u (Move.wasteToTab c b) = some s) :
    u.wasteIs c = true ∧ u.canPlace c b = true ∧
      ∃ wsl, u.waste = c :: wsl ∧ s = { u.putCard c b with waste := wsl } := by
  simp only [State.step] at h
  split at h
  · rename_i hcond
    rw [Bool.and_eq_true_iff] at hcond
    obtain ⟨hw, hcp⟩ := hcond
    refine ⟨hw, hcp, ?_⟩
    by_cases hwst : u.waste = []
    · rw [hwst] at h
      simp at h
    · obtain ⟨w', wsl, hcon⟩ := list_cons_of_ne_nil hwst
      have hw'c : w' = c := by
        rw [State.wasteIs_cons hcon c] at hw
        exact of_decide_eq_true hw
      rw [hw'c] at hcon
      simp only [hcon, Option.some.injEq] at h
      exact ⟨wsl, hcon, h.symm⟩
  · simp at h


/-! ## This card's own kit -/

/-- A snoc's `chop` is exactly its front — the splice the raise leg
reads off the raised pile. -/
private theorem chop_snoc : ∀ {front : List Card} {c : Card},
    chop (front ++ [c]) = front := by
  intro front
  induction front with
  | nil => intro c; rfl
  | cons x t ih =>
      intro c
      cases t with
      | nil => rfl
      | cons y t' =>
          show x :: chop ((y :: t') ++ [c]) = x :: (y :: t')
          rw [ih (c := c)]

/-- With a nonempty face-up remainder, removing the run keeps the
pile below verbatim — no reveal fires. -/
private theorem afterRunRemoved_pre_ne {p : Pile} {pre : List Card}
    (hne : pre ≠ []) :
    Pile.afterRunRemoved p pre = { p with faceUp := pre } := by
  cases pre with
  | cons x t => rfl
  | nil => exact absurd rfl hne

/-- The `tabToFound` computation: with the rung and the search's
answer in hand, the step is the splice. -/
private theorem step_tabToFound_eq {st : State} {c : Card} {k : Anchor}
    (hnext : st.nextUp c = true) (hpo : st.pileOfTop c = some k) :
    State.step st (Move.tabToFound c) =
      some { st.setFound c.suit (st.found c.suit ++ [c]) with
             piles := fun a' => if a' = k then
                 Pile.afterRunRemoved (st.piles k) (chop (st.piles k).faceUp)
               else st.piles a' } := by
  show (if st.nextUp c then
      match st.pileOfTop c with
      | none => none
      | some a => some { st.setFound c.suit (st.found c.suit ++ [c]) with
          piles := fun a' => if a' = a then
              Pile.afterRunRemoved (st.piles a) (chop (st.piles a).faceUp)
            else st.piles a' }
      else none) = _
  rw [ite_eq_left hnext, hpo]

/-- The `foundToTab` computation: with the foundation top and the
place guard in hand, the step is the chop-back and place. -/
private theorem step_foundToTab_eq {st : State} {c : Card} {b : Base}
    (hcu : st.foundTop c.suit = some c)
    (hcond : (decide (c = c) && st.canPlace c b) = true) :
    State.step st (Move.foundToTab c b) =
      some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b) := by
  show (match st.foundTop c.suit with
      | some c' =>
        if decide (c' = c) && st.canPlace c b then
          some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
        else none
      | none => none) = _
  rw [hcu]
  show (if decide (c = c) && st.canPlace c b then
      some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
    else none) =
    some ((st.setFound c.suit (chop (st.found c.suit))).putCard c b)
  rw [ite_eq_left hcond]

/-- One move runs by stepping it. -/
private theorem run_one {st : State} {m : Move} {s : State}
    (h : State.step st m = some s) :
    st.run [m] = some s := by
  show (match State.step st m with
    | some st' => State.run st' []
    | none => none) = some s
  rw [h]
  rfl

/-- The shuttle's mid state: `u` with its waste head consumed
(`c :: ws` became `ws`) and the card `c` raised onto its own
foundation.  The piles, the stock, and the draw step are `u`'s
verbatim — the raise leg (`raise_tabToFound`) proves the raise never
flips a hidden card, and so restores the piles exactly. -/
def raisedMid (u : State) (ws : List Card) (c : Card) : State :=
  State.mk (fun s' => if s' = c.suit then u.found c.suit ++ [c] else u.found s')
    u.piles u.stock ws u.drawStep

/-! ## The two shuttle legs -/

/-- The raise leg.  From any legal `wasteToTab` landing `s` of the
waste top `c`, the pile top `c` ascends to its foundation: the rung
survived (a tableau placement touches no foundation), the search is
exact (at `u` the card lived in the waste, so `WF` puts it in no
pile — the placement moved it into exactly one), and the raise does
not flip (a king landed on an empty seat, empty hidden stack
included; a non-king landed on a card base that remains below).
So `tabToFound c` lands at the one `raisedMid u ws c`, whatever
the base was. -/
private theorem raise_tabToFound {u : State} {c : Card} {ws : List Card}
    (hwf : u.WF) (hrung : u.nextUp c = true) (hwastee : u.waste = c :: ws)
    {b : Base} {s : State}
    (h : State.step u (Move.wasteToTab c b) = some s) :
    State.step s (Move.tabToFound c) = some (raisedMid u ws c) := by
  obtain ⟨-, hcp, wsl, hw', hs'⟩ := step_wasteToTab_inv h
  rw [hw'] at hwastee
  injection hwastee with _ hws
  cases hws
  have hmemw : c ∈ u.waste := by
    rw [hw']
    exact List.mem_cons_self ..
  -- placements touch neither the found nor the stock nor the draw
  -- step; the splice's waste is `ws`
  have hsFound : s.found = u.found := by rw [hs']; exact putCard_keep.1
  have hsStock : s.stock = u.stock := by rw [hs']; exact putCard_keep.2.1
  have hsWaste : s.waste = ws := by rw [hs']
  have hsDraw : s.drawStep = u.drawStep := by rw [hs']; exact putCard_keep.2.2.2
  cases b with
  | inl a1 =>
      -- the seat was empty: the pile under `c` is `a1`, bare
      have hcpx : ((u.piles a1).isEmpty && decide (c.rank = Rank.king)) = true := hcp
      obtain ⟨hempty, -⟩ := Bool.and_eq_true_iff.mp hcpx
      obtain ⟨hhid, hface⟩ := (Pile.isEmpty_eq _).mp hempty
      have hpilea1 : u.piles a1 = ⟨[], []⟩ := Pile.ext hhid hface
      have hsPile : ∀ a' : Anchor, s.piles a' =
          if a' = a1 then ⟨[], [c]⟩ else u.piles a' := by
        intro a'
        rw [hs']
        rfl
      have hsNext : s.nextUp c = true := by rw [hs']; exact hrung
      have hsTopa1 : s.topOf a1 = some c := by
        rw [hs']
        show Pile.top (if a1 = a1 then ⟨[], [c]⟩ else u.piles a1) = some c
        rw [ite_eq_left rfl]
        rfl
      have hexcl : ∀ x ∈ Anchor.all, x ≠ a1 →
          decide (s.topOf x = some c) = false := by
        intro x _ hne
        apply decide_false_of_not
        intro htopx
        have hpx : (s.piles x).top = some c := htopx
        rw [hsPile x, ite_eq_right hne] at hpx
        exact (mem_pile_unique hwf (Or.inr (Pile.mem_of_top hpx))).2.2.1 hmemw
      have hsSearch : s.pileOfTop c = some a1 := by
        show firstWhere (fun a2 => decide (s.topOf a2 = some c)) Anchor.all
          = some a1
        exact firstWhere_find (Anchor.mem_all a1) (decide_eq_true hsTopa1) hexcl
      rw [step_tabToFound_eq hsNext hsSearch, Option.some.injEq]
      apply State.ext
      · show (fun s1' =>
            if s1' = c.suit then s.found c.suit ++ [c] else s.found s1') = _
        rw [hsFound]
        rfl
      · show (fun a' : Anchor =>
            if a' = a1 then Pile.afterRunRemoved (s.piles a1)
                (chop (s.piles a1).faceUp) else s.piles a') = _
        funext a'
        by_cases haa : a' = a1
        · rw [ite_eq_left haa]
          rw [haa, hsPile a1, ite_eq_left rfl,
            show ((raisedMid u ws c).piles a1) = u.piles a1 from rfl,
            hpilea1]
          rfl
        · show (if a' = a1 then Pile.afterRunRemoved (s.piles a1)
              (chop (s.piles a1).faceUp) else s.piles a') = u.piles a'
          rw [ite_eq_right haa, hsPile a', ite_eq_right haa]
      · show s.stock = u.stock
        rw [hsStock]
      · show s.waste = ws
        rw [hsWaste]
      · show s.drawStep = u.drawStep
        rw [hsDraw]
  | inr z1 =>
      -- a card base: `c` sits on `z1`'s pile, which exists
      simp only [State.canPlace] at hcp
      cases hpo : u.pileOfTop z1 with
      | none =>
          simp only [hpo] at hcp
          exact Bool.noConfusion hcp
      | some k =>
          have hsPile : ∀ a' : Anchor, s.piles a' =
              if a' = k then { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
                else u.piles a' := by
            intro a'
            rw [hs']
            rw [putCard_inr_eq hpo]
            rfl
          have hsNext : s.nextUp c = true := by
            rw [hs']
            rw [putCard_inr_eq hpo]
            exact hrung
          have hsTophold : s.topOf k = some c := by
            have hpx : (s.piles k).top = some c := by
              rw [hsPile k, ite_eq_left rfl]
              show lastOf ((u.piles k).faceUp ++ [c]) = some c
              exact lastOf_snoc
            exact hpx
          have hexcl : ∀ x ∈ Anchor.all, x ≠ k →
              decide (s.topOf x = some c) = false := by
            intro x _ hne
            apply decide_false_of_not
            intro htopx
            have hpx : (s.piles x).top = some c := htopx
            rw [hsPile x, ite_eq_right hne] at hpx
            exact (mem_pile_unique hwf (Or.inr (Pile.mem_of_top hpx))).2.2.1 hmemw
          have hsSearch : s.pileOfTop c = some k := by
            show firstWhere (fun a2 => decide (s.topOf a2 = some c)) Anchor.all
              = some k
            exact firstWhere_find (Anchor.mem_all k) (decide_eq_true hsTophold)
              hexcl
          -- the base card keeps a nonempty face-up run below `c`, so
          -- the raise restores the pile without a reveal
          have hutop : u.topOf k = some z1 :=
            of_decide_eq_true (firstWhere_sound
              (p := fun a2 => decide (u.topOf a2 = some z1)) hpo)
          obtain ⟨front1, hf1⟩ := Pile.top_eq_lastOf_iff.mp hutop
          have hF1ne : (u.piles k).faceUp ≠ [] := by
            rw [hf1]
            cases front1 with
            | nil => simp
            | cons x t => simp
          rw [step_tabToFound_eq hsNext hsSearch, Option.some.injEq]
          apply State.ext
          · show (fun s1' =>
                if s1' = c.suit then s.found c.suit ++ [c] else s.found s1') = _
            rw [hsFound]
            rfl
          · show (fun a' : Anchor =>
                if a' = k then Pile.afterRunRemoved (s.piles k)
                    (chop (s.piles k).faceUp) else s.piles a') = _
            funext a'
            by_cases haa : a' = k
            · rw [ite_eq_left haa]
              rw [haa, hsPile k, ite_eq_left rfl,
                show chop (({ u.piles k with faceUp := (u.piles k).faceUp ++ [c] } :
                    Pile).faceUp) = chop ((u.piles k).faceUp ++ [c]) from rfl,
                chop_snoc, afterRunRemoved_pre_ne hF1ne]
              rfl
            · show (if a' = k then Pile.afterRunRemoved (s.piles k)
                  (chop (s.piles k).faceUp) else s.piles a') = u.piles a'
              rw [ite_eq_right haa, hsPile a', ite_eq_right haa]
          · show s.stock = u.stock
            rw [hsStock]
          · show s.waste = ws
            rw [hsWaste]
          · show s.drawStep = u.drawStep
            rw [hsDraw]

/-- The lower leg.  From the mid state, `foundToTab c b` fires: its
foundation top is exactly `c`, and its `canPlace` is read against
`u`'s verbatim piles — so it lands exactly on the `wasteToTab c b`
successor. -/
private theorem lower_foundToTab {u : State} {c : Card} {ws : List Card}
    (hwastee : u.waste = c :: ws)
    {b : Base} {s : State}
    (h : State.step u (Move.wasteToTab c b) = some s) :
    State.step (raisedMid u ws c) (Move.foundToTab c b) = some s := by
  obtain ⟨-, hcp, wsl, hw', hs'⟩ := step_wasteToTab_inv h
  rw [hw'] at hwastee
  injection hwastee with _ hws
  cases hws
  subst hs'
  -- the mid state's foundation top is exactly `c`, and its target
  -- guard is read against `u`'s verbatim piles
  have hMfc : (raisedMid u ws c).found c.suit = u.found c.suit ++ [c] := by
    show (if c.suit = c.suit then u.found c.suit ++ [c] else u.found c.suit) = _
    rw [ite_eq_left rfl]
  have hMtop : (raisedMid u ws c).foundTop c.suit = some c := by
    show lastOf ((raisedMid u ws c).found c.suit) = some c
    rw [hMfc]
    exact lastOf_snoc
  have hMcp : (raisedMid u ws c).canPlace c b = true := hcp
  rw [step_foundToTab_eq hMtop (by
    rw [show decide (c = c) = true from decide_eq_true rfl, hMcp]
    rfl)]
  -- restore the foundation, then place
  have hchop : chop ((raisedMid u ws c).found c.suit) = u.found c.suit := by
    rw [hMfc, chop_snoc]
  rw [hchop, Option.some.injEq]
  -- the lowered source's found-function and piles are exactly `u`'s
  have hMf : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).found
      = u.found := by
    funext s1'
    show ((raisedMid u ws c).setFound c.suit (u.found c.suit)).found s1'
      = u.found s1'
    by_cases hs1 : s1' = c.suit
    · show (if s1' = c.suit then u.found c.suit
          else (raisedMid u ws c).found s1') = u.found s1'
      rw [ite_eq_left hs1, hs1]
    · show (if s1' = c.suit then u.found c.suit
          else (raisedMid u ws c).found s1') = u.found s1'
      rw [ite_eq_right hs1]
      show (if s1' = c.suit then u.found c.suit ++ [c] else u.found s1') = _
      rw [ite_eq_right hs1]
  have hMsp : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles
      = u.piles := rfl
  cases b with
  | inl a2 =>
      apply State.ext
      · exact hMf
      · show (fun a' : Anchor =>
            if a' = a2 then ⟨[], [c]⟩ else
            ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles a') =
          (fun a' : Anchor => if a' = a2 then ⟨[], [c]⟩ else u.piles a')
        rw [hMsp]
      · rfl
      · rfl
      · rfl
  | inr z2 =>
      simp only [State.canPlace] at hcp
      cases hpo : u.pileOfTop z2 with
      | none =>
          simp only [hpo] at hcp
          exact Bool.noConfusion hcp
      | some k =>
          have hMpo : ((raisedMid u ws c).setFound c.suit (u.found c.suit)).pileOfTop z2
              = some k := by
            show (u.pileOfTop z2 : Option Anchor) = some k
            exact hpo
          rw [putCard_inr_eq hMpo,
            show u.putCard c (.inr z2) =
              u.setPile k { u.piles k with faceUp := (u.piles k).faceUp ++ [c] } from
              putCard_inr_eq hpo]
          apply State.ext
          · exact hMf
          · show (fun a' : Anchor =>
                if a' = k then
                  { ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles k with
                    faceUp :=
                    (((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles k).faceUp ++ [c] }
                else ((raisedMid u ws c).setFound c.suit (u.found c.suit)).piles a') =
              (fun a' : Anchor =>
                if a' = k then { u.piles k with faceUp := (u.piles k).faceUp ++ [c] }
                else u.piles a')
            rw [hMsp]
          · rfl
          · rfl
          · rfl

/-! ## The join -/

/-- **The foundation shuttle join** (`FUTURES-ORIG.md` §3,
candidate B, the route map's first futures theorem).

Two legal tableau landings of the same waste top `c` — onto `b₁`
and onto `b₂` — are one `RevEqW`: at each landing, `tabToFound c`
raises the placed card onto its foundation (legal — the rung
`u.nextUp c` survived the placement, and `c` is now a pile top),
then `foundToTab c` lowers it onto the *other* base (legal — the
round trip restored every pile, so the other target is locatable
exactly as it was at `u`); the two-move play from `s₁` ends at `s₂`,
the mirror play from `s₂` ends at `s₁`, and each move's own
witness is the mirror leg's head — so both plays are `ShufflePlayW`s
and the pair is one explicit `RevEqW` witness.

Premises: `hwf` (the searches and the occurrence bookkeeping run at
`u`), the rung (the load-bearing premise, cf. the route map's fence
F3), and the two landings.  The construction is uniform in
`b₁ = b₂` — a king can only land on empty seats and a non-king only
on card bases, so the two legs always have the same shape, and at
equal bases the shuttle is a round trip that happens to return —
hence no degenerate split is needed. -/
theorem shuttle_join {u : State} {c : Card} {b1 b2 : Base} {s1 s2 : State}
    (hwf : u.WF) (htop : u.wasteIs c = true) (hrung : u.nextUp c = true)
    (h1 : State.step u (.wasteToTab c b1) = some s1)
    (h2 : State.step u (.wasteToTab c b2) = some s2) :
    RevEqW s1 s2 := by
  obtain ⟨ws, hwastee⟩ : ∃ ws, u.waste = c :: ws := by
    by_cases hwst : u.waste = []
    · rw [State.wasteIs_nil hwst] at htop
      exact Bool.noConfusion htop
    · obtain ⟨c', t, hcon⟩ := list_cons_of_ne_nil hwst
      have hc'c : c' = c := by
        rw [State.wasteIs_cons hcon c] at htop
        exact of_decide_eq_true htop
      refine ⟨t, ?_⟩
      rw [hcon, hc'c]
  have hA : State.step s1 (Move.tabToFound c) = some (raisedMid u ws c) :=
    raise_tabToFound hwf hrung hwastee h1
  have hD : State.step s2 (Move.tabToFound c) = some (raisedMid u ws c) :=
    raise_tabToFound hwf hrung hwastee h2
  have hC : State.step (raisedMid u ws c) (Move.foundToTab c b1) = some s1 :=
    lower_foundToTab hwastee h1
  have hB : State.step (raisedMid u ws c) (Move.foundToTab c b2) = some s2 :=
    lower_foundToTab hwastee h2
  refine ⟨[Move.tabToFound c, Move.foundToTab c b2], ?_,
    [Move.tabToFound c, Move.foundToTab c b1], ?_⟩
  · exact ShufflePlayW.cons ⟨_, [Move.foundToTab c b1], hA, run_one hC⟩ hA
      (ShufflePlayW.cons ⟨_, [Move.tabToFound c], hB, run_one hD⟩ hB
        (ShufflePlayW.nil s2))
  · exact ShufflePlayW.cons ⟨_, [Move.foundToTab c b2], hD, run_one hB⟩ hD
      (ShufflePlayW.cons ⟨_, [Move.tabToFound c], hC, run_one hA⟩ hC
        (ShufflePlayW.nil s1))
