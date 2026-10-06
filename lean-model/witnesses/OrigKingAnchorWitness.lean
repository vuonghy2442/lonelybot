import Orig.Fate
import Orig.Combine

/-!
# The king-anchor corner, physically — the collapse of the wave-21 c2 split

The old corpus's `C2KingAnchorWitness` (a PRISTINE all-empty-board
engine state with a stocked `♠K`) refuted four as-stated count
universals because its engine closure `closureEq` — a
STOCK-AND-STACK-ONLY accommodation join — could not move a landed
king, so all seven anchor landings came apart (`wSucc_ne`,
FARM.md:2415-2423).

The physical re-derivation does NOT survive verbatim, and this file
records exactly why: the physical window relation is the full
reversible orbit (`ShufflePlay`, FUTURES-ORIG §5/§6's orbit grading),
and a landed lone king relocates between empty anchors by `tabToTab`
with an explicit one-move return — a `reversibleAtW` witness — so
the anchor landings of one king commitment sit in ONE `RevEqW`
class.  Per FUTURES-ORIG §5.2's orbit-route expectation (and §1
dividend (d)'s Anchor-transposition symmetry), the physical
king-anchor corner SATISFIES the constructive two-option shape; the
old refutation was an artifact of the engine's narrower windows.

## The craft (a crafted, conservative WF corner)

`kaW` is a hand-built WF state of the committed midgame shape: every
one of the 52 cards appears exactly once (`kaW_wf`, by the
census-decide), foundations empty, four `♦3/♣5/♥9/♦J`-topped guard
piles occupy their anchors, THREE anchors (`p0, p1, p3`) stand
empty, and the waste holds the lone `♠K` — the commit under test.
(The pristine all-empty craft is not the physical world to test; the
dealt-initial side's data is carried in `OrigLabeledWitness`.)

## The verdicts (all `#eval`-recorded and decide-proved below)

* three live king landings (`kaW_landings`), and NOTHING else on the
  waste-king's arms (`kaW_kingPow` — the king is the only waste
  card, kings sit on no card base, and no guard top is an ace or a
  king);
* each pair of landings is `RevEqW`-related by an explicit
  move-plus-reverse witness pair (`kaL_revEqW`) — **THE COLLAPSE
  FENCE**: the physical windows join what the engine's stack-only
  closure kept apart;
* per the scope rule (never a count theorem), the two-via-orbit
  positive shape is deliberately NOT stated as a theorem — only the
  pairwise join fences and the census are.

Axioms: permitted `[propext, Classical.choice, Quot.sound]`; the
pins at the end show `[propext, Quot.sound]` and less.  DEDUP NOTE:
`decSt` and the two shape aliases below are the same local
re-derivations as in `OrigExchangeWitness` (self-contained at this
worktree's base, which predates `Orig.Integrity`; see the report's
overlap list).
-/

namespace OrigKingAnchor

/-! ## Cards and the corner -/

/-- Spades. -/
private def S (r : Rank) : Card := ⟨Suit.spade, r⟩
/-- Hearts. -/
private def H (r : Rank) : Card := ⟨Suit.heart, r⟩
/-- Diamonds. -/
private def D (r : Rank) : Card := ⟨Suit.diamond, r⟩
/-- Clubs. -/
private def C (r : Rank) : Card := ⟨Suit.club, r⟩

/-- The stock bulk: the 47 cards not otherwise placed. -/
private def kaStock : List Card :=
  [S .ace, S .two, S .three, S .four, S .five, S .six, S .seven, S .eight,
    S .nine, S .ten, S .jack, S .queen,
   H .ace, H .two, H .three, H .four, H .five, H .six, H .seven, H .eight,
    H .ten, H .jack, H .queen, H .king,
   D .ace, D .two, D .four, D .five, D .six, D .seven, D .eight, D .nine,
    D .ten, D .queen, D .king,
   C .ace, C .two, C .three, C .four, C .six, C .seven, C .eight, C .nine,
    C .ten, C .jack, C .queen, C .king]

/-- The corner's piles: four guarded anchors, three empty ones. -/
private def kaPiles : Anchor → Pile
  | .p0 => ⟨[], []⟩
  | .p1 => ⟨[], []⟩
  | .p2 => ⟨[], [D .three]⟩
  | .p3 => ⟨[], []⟩
  | .p4 => ⟨[], [C .five]⟩
  | .p5 => ⟨[], [H .nine]⟩
  | .p6 => ⟨[], [D .jack]⟩

/-- The corner tip: the lone waste king over the stock bulk. -/
def kaW : State :=
  { found := fun _ => []
    piles := kaPiles
    stock := kaStock
    waste := [S .king]
    drawStep := 1 }

/-- The certified empty anchors. -/
private def KaE (a : Anchor) : Prop :=
  a = Anchor.p0 ∨ a = Anchor.p1 ∨ a = Anchor.p3

/-- The landing state: the king arrived at the certified anchor `a`.
(The default branches make the map total; only certified anchors are
used below.) -/
def kaLz : Anchor → State
  | .p0 =>
      { found := fun _ => []
        piles := fun a =>
          match a with
          | .p0 => ⟨[], [S .king]⟩
          | .p1 => ⟨[], []⟩
          | .p2 => ⟨[], [D .three]⟩
          | .p3 => ⟨[], []⟩
          | .p4 => ⟨[], [C .five]⟩
          | .p5 => ⟨[], [H .nine]⟩
          | .p6 => ⟨[], [D .jack]⟩
        stock := kaStock
        waste := []
        drawStep := 1 }
  | .p1 =>
      { found := fun _ => []
        piles := fun a =>
          match a with
          | .p0 => ⟨[], []⟩
          | .p1 => ⟨[], [S .king]⟩
          | .p2 => ⟨[], [D .three]⟩
          | .p3 => ⟨[], []⟩
          | .p4 => ⟨[], [C .five]⟩
          | .p5 => ⟨[], [H .nine]⟩
          | .p6 => ⟨[], [D .jack]⟩
        stock := kaStock
        waste := []
        drawStep := 1 }
  | .p3 =>
      { found := fun _ => []
        piles := fun a =>
          match a with
          | .p0 => ⟨[], []⟩
          | .p1 => ⟨[], []⟩
          | .p2 => ⟨[], [D .three]⟩
          | .p3 => ⟨[], [S .king]⟩
          | .p4 => ⟨[], [C .five]⟩
          | .p5 => ⟨[], [H .nine]⟩
          | .p6 => ⟨[], [D .jack]⟩
        stock := kaStock
        waste := []
        drawStep := 1 }
  | .p2 => kaW
  | .p4 => kaW
  | .p5 => kaW
  | .p6 => kaW

/-! ## The local instruments (DEDUP-marked: the same re-derivations
as family 1; nothing imported from `Orig.Integrity`) -/

private def decSt (s t : State) : Decidable (s = t) :=
  decidable_of_decidable_of_iff (p :=
    (s.found .spade = t.found .spade ∧ s.found .heart = t.found .heart ∧
     s.found .diamond = t.found .diamond ∧ s.found .club = t.found .club ∧
     s.piles .p0 = t.piles .p0 ∧ s.piles .p1 = t.piles .p1 ∧
     s.piles .p2 = t.piles .p2 ∧ s.piles .p3 = t.piles .p3 ∧
     s.piles .p4 = t.piles .p4 ∧ s.piles .p5 = t.piles .p5 ∧
     s.piles .p6 = t.piles .p6 ∧
     s.stock = t.stock ∧ s.waste = t.waste ∧ s.drawStep = t.drawStep))
    (by
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
        apply State.ext
        · funext σ; cases σ <;> assumption
        · funext a; cases a <;> assumption
        · assumption
        · assumption
        · assumption
      · rintro rfl
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

local instance : DecidableEq State := fun s t => decSt s t

private theorem canPlace_inl_eq (st : State) (c : Card) (a : Anchor) :
    st.canPlace c (.inl a) = ((st.piles a).isEmpty && decide (c.rank = .king)) := rfl

private theorem canPlace_inr_eq (st : State) (c z : Card) :
    st.canPlace c (.inr z) = (match st.pileOfTop z with
      | some _ => canSitOn c z | none => false) := rfl

private theorem step_w2t_eq (st : State) (c : Card) (b : Base) :
    st.step (.wasteToTab c b) =
      (if st.wasteIs c && st.canPlace c b then
        match st.waste with
        | _ :: ws => some { st.putCard c b with waste := ws }
        | [] => none
      else none) := rfl

/-! ## Shape facts -/

/-- The empty anchors: exactly the three certified ones. -/
theorem kaW_empty (a : Anchor) : (kaW.piles a).isEmpty = true ↔ KaE a := by
  cases a with
  | p0 => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | p1 => exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => rfl⟩
  | p2 =>
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      rcases h with h1 | h2 | h3 <;> simp_all
  | p3 => exact ⟨fun _ => Or.inr (Or.inr rfl), fun _ => rfl⟩
  | p4 =>
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      rcases h with h1 | h2 | h3 <;> simp_all
  | p5 =>
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      rcases h with h1 | h2 | h3 <;> simp_all
  | p6 =>
      refine ⟨fun h => absurd h (by decide), fun h => ?_⟩
      rcases h with h1 | h2 | h3 <;> simp_all

theorem kaW_waste : kaW.waste = [S .king] := rfl

/-! ## WF by the census decide -/

/-- **`kaW` is conservative and well-formed** — every one of the 52
cards appears exactly once, the foundations are empty prefixes, the
`runOK` check passes, the draw step is 1.  [axioms: none — the
conservation conjunct is a `List.all` census decide.] -/
theorem kaW_wf : kaW.WF := by
  refine ⟨?_, ?_, ?_, Or.inl rfl⟩
  · intro σ; exact ⟨0, by cases σ <;> rfl⟩
  · intro a; cases a <;> decide
  · intro c hc
    have hball : (Card.universe.all fun c => decide (kaW.cardCount c = 1)) = true := by
      decide
    have hb := List.all_eq_true.mp hball
    exact of_decide_eq_true (hb c hc)

/-! ## The landings and the census -/

/-- **VERDICT (census): each certified empty anchor admits the waste
king.**  [axioms: none — decide.] -/
theorem kaW_landings (a : Anchor) (ha : KaE a) :
    kaW.step (.wasteToTab (S .king) (.inl a)) = some (kaLz a) := by
  rcases ha with rfl | rfl | rfl <;> decide

/-- **The waste-king arms are EXACTLY the three certified landings**:
the waste holds only the king, kings sit on no card base, and the
only empty anchors are the certified ones.  [axioms: none — per-kind
case analysis on the crafted shapes.] -/
theorem kaW_kingPow (c : Card) (b : Base) (t : State)
    (h : kaW.step (.wasteToTab c b) = some t) :
    c = S .king ∧ ∃ a : Anchor, KaE a ∧ b = Sum.inl a := by
  rw [step_w2t_eq] at h
  have hcnd : (kaW.wasteIs c && kaW.canPlace c b) = true := by
    cases hc : (kaW.wasteIs c && kaW.canPlace c b) with
    | true => rfl
    | false => rw [hc] at h; simp at h
  rw [Bool.and_eq_true] at hcnd
  obtain ⟨hw, hp⟩ := hcnd
  have hw2 : kaW.wasteIs c = decide (S .king = c) := State.wasteIs_cons rfl c
  rw [hw2] at hw
  have hck : c = S .king := (of_decide_eq_true hw).symm
  refine ⟨hck, ?_⟩
  subst hck
  cases b with
  | inl a =>
      rw [canPlace_inl_eq] at hp
      rw [Bool.and_eq_true] at hp
      exact ⟨a, (kaW_empty a).mp hp.1, rfl⟩
  | inr z =>
      exfalso
      rw [canPlace_inr_eq] at hp
      cases hpt : kaW.pileOfTop z with
      | none => rw [hpt] at hp; simp at hp
      | some k =>
          rw [hpt] at hp
          have hfit : canSitOn (S .king) z = true := hp
          obtain ⟨h1, -⟩ := (canSitOn_eq (S .king) z).mp hfit
          have h2 : 12 + 1 = z.rank.toIdx := h1
          have hz := Rank.toIdx_lt z.rank
          omega

/-! ## The collapse fence -/

/-- The one-pair join: a king landed at `A` relocates to `B` with
the reverse move as the explicit returning play — a `reversibleAtW`
pair, packed as `RevEqW` witnesses. -/
private theorem relinkPair (A B : Anchor)
    (hfwd : (kaLz A).step (.tabToTab (S .king) (.inl B)) = some (kaLz B))
    (hbwd : (kaLz B).step (.tabToTab (S .king) (.inl A)) = some (kaLz A)) :
    RevEqW (kaLz A) (kaLz B) :=
  have hrfwd : (kaLz B).run [.tabToTab (S .king) (.inl A)] = some (kaLz A) := by
    show (match (kaLz B).step (.tabToTab (S .king) (.inl A)) with
      | some s' => s'.run [] | none => none) = some (kaLz A)
    rw [hbwd]; rfl
  have hrbwd : (kaLz A).run [.tabToTab (S .king) (.inl B)] = some (kaLz B) := by
    show (match (kaLz A).step (.tabToTab (S .king) (.inl B)) with
      | some s' => s'.run [] | none => none) = some (kaLz B)
    rw [hfwd]; rfl
  ⟨[.tabToTab (S .king) (.inl B)],
    .cons ⟨_, [.tabToTab (S .king) (.inl A)], hfwd, hrfwd⟩ hfwd (.nil _),
    [.tabToTab (S .king) (.inl A)],
    .cons ⟨_, [.tabToTab (S .king) (.inl B)], hbwd, hrbwd⟩ hbwd (.nil _)⟩

/-- **THE COLLAPSE FENCE (verdict): the king-anchor landings of one
commitment are pairwise `RevEqW`-related at the physical game** —
joined in one witness-reversible orbit, killing the physical
re-statement of the old `wk_c2` closure-split.  [axioms:
`[propext, Quot.sound]` at most — see pins.] -/
theorem kaL_revEqW {a a' : Anchor} (ha : KaE a) (ha' : KaE a') (hne : a ≠ a') :
    RevEqW (kaLz a) (kaLz a') := by
  rcases ha with rfl | rfl | rfl <;> rcases ha' with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hne
    | exact relinkPair Anchor.p0 Anchor.p1 (by decide) (by decide)
    | exact relinkPair Anchor.p0 Anchor.p3 (by decide) (by decide)
    | exact relinkPair Anchor.p1 Anchor.p0 (by decide) (by decide)
    | exact relinkPair Anchor.p1 Anchor.p3 (by decide) (by decide)
    | exact relinkPair Anchor.p3 Anchor.p0 (by decide) (by decide)
    | exact relinkPair Anchor.p3 Anchor.p1 (by decide) (by decide)

end OrigKingAnchor

/-! ## The census battery (deterministic `#eval` probes) -/

namespace OrigKingAnchor

private def moveCase (st : State) (m : Move) : List (Move × State) :=
  match st.step m with
  | some t => [(m, t)]
  | none => []

/-- The full move enumeration — the census instrument. -/
private def allMoves (st : State) : List (Move × State) :=
  moveCase st .draw
  ++ (Card.universe.flatMap fun c =>
        moveCase st (.wasteToFound c) ++ moveCase st (.tabToFound c))
  ++ ((Card.universe.flatMap fun c => Anchor.all.map fun a => (c, Sum.inl a))
      ++ (Card.universe.flatMap fun c => Card.universe.map fun z => (c, Sum.inr z))
      ).flatMap fun cb =>
      match cb with
      | (c, b) =>
          moveCase st (.wasteToTab c b) ++ moveCase st (.foundToTab c b)
            ++ moveCase st (.tabToTab c b)

/-- info: 4 -/
#guard_msgs in
#eval (allMoves kaW).length

/-- info: 3 -/
#guard_msgs in
#eval (allMoves (kaLz Anchor.p0)).length

/- Axiom pins for the battery. -/
#print axioms OrigKingAnchor.kaW_wf
#print axioms OrigKingAnchor.kaW_landings
#print axioms OrigKingAnchor.kaW_kingPow
#print axioms OrigKingAnchor.kaL_revEqW
#print axioms OrigKingAnchor.kaW_empty

end OrigKingAnchor


