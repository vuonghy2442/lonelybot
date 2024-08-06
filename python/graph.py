from typing import NamedTuple, Literal, List, Tuple, Optional

RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
SUITS = ["H", "D", "C", "S"]


class Card(NamedTuple):
    rank: int
    suit: int

    @staticmethod
    def from_str(card: str) -> "Card":
        return Card(RANKS.index(card[:-1]), SUITS.index(card[-1:].upper()))

    def lower_rank(self) -> Optional["Card"]:
        if self.rank == 0:
            return None
        return Card(self.rank - 1, self.suit)

    def higher_rank(self) -> Optional["Card"]:
        if self.rank + 1 >= len(RANKS):
            return None
        return Card(self.rank + 1, self.suit)

    def swap_suit(self) -> "Card":
        return Card(self.rank, self.suit ^ 1)

    def swap_color(self) -> "Card":
        return Card(self.rank, self.suit ^ 2)

    def __repr__(self) -> str:
        return RANKS[self.rank] + SUITS[self.suit]


# convert game


class Game(NamedTuple):
    tableau: List[Tuple[List[Card], List[Card]]]
    deck: List[Card]

    @staticmethod
    def from_str(game: dict) -> "Game":
        tableau = []
        for column in game["tableau piles"]:
            hidden = []
            visible = []
            for card in column:
                c = Card.from_str(card)
                if card[-1:].islower():
                    hidden.append(c)
                else:
                    visible.append(c)
            tableau.append((hidden, visible))
        deck = list(map(Card.from_str, game["stock"]))
        deck.reverse()
        return Game(tableau, deck)

    def is_hidden(self, card: Card) -> bool:
        for hidden, _ in self.tableau:
            if card in hidden:
                return True
        return False

    def is_first_visible(self, card: Card) -> bool:
        for _, visible in self.tableau:
            if len(visible) > 0 and card == visible[0]:
                return True
        return False

    def find_blocking_visible(self, card: Card) -> Optional[Card]:
        for _, visible in self.tableau:
            try:
                idx = visible.index(card)
                if idx + 1 < len(visible):
                    return visible[idx + 1]
                return None
            except ValueError:
                pass
        return None  # not hidden :)

    def is_deck(self, card: Card) -> bool:
        return card in self.deck

    def find_blocking(self, card: Card) -> Optional[Card]:
        for hidden, visible in self.tableau:
            try:
                idx = hidden.index(card)
                if idx + 1 < len(hidden):
                    return hidden[idx + 1]
                assert len(visible) > 0
                return visible[0]
            except ValueError:
                pass
        return None  # not hidden :)


class Move(NamedTuple):
    action: Literal["Reveal", "FromDeck", "ToStack"]
    card: Card

    def __repr__(self) -> str:
        return self.action + "_" + str(self.card)


class Relation(NamedTuple):
    before: Move
    after: Move

    def reverse(self) -> "Relation":
        return Relation(self.after, self.before)

    def __repr__(self) -> str:
        return str(self.before) + " < " + str(self.after)


# returning cnf form :)
CNF = List[List[Relation]]
CNF_False = [[]]
CNF_True = []


def not_and(clause: CNF) -> CNF:
    if any(len(c) == 0 for c in clause):
        return CNF_True

    assert all(len(c) == 1 for c in clause)

    result = []
    for c in clause:
        result.append(c[0].reverse())
    return [result]


def cnf_or(clause1: CNF, clause2: CNF) -> CNF:
    if len(clause1) == 0 or len(clause2) == 0:
        return CNF_True

    assert len(clause1) == 1, len(clause2) == 1
    return [clause1[0] + clause2[0]]


def doable_reveal(game: Game, card: Card) -> CNF:
    assert game.is_hidden(card) or game.is_first_visible(card)
    this_move = Move("Reveal", card)
    # check for blocking
    # or maybe to stack
    result = []

    blocking = game.find_blocking(card)
    if blocking is not None:
        result.append([Relation(Move("Reveal", blocking), this_move)])

    lower = card.lower_rank()
    if lower is not None:
        to_stack = [[Relation(Move("ToStack", lower), this_move)]]
    else:
        to_stack = CNF_True
    # extra solvable or to stack :)
    result += cnf_or(to_stack, may_solved_at(game, card, this_move))
    return result


def relational_draw(game: Game, step: int) -> CNF:
    deck = game.deck

    result = []
    for i in range(min(len(deck), step) - 1):
        result.append(
            [Relation(Move("FromDeck", deck[i + 1]), Move("FromDeck", deck[i]))]
        )

    pivots = []
    for i in range(step, len(deck) - 1):
        if i % step == 0:
            pivots.append(deck[i])
            continue

        result_or = [Relation(Move("FromDeck", deck[i + 1]), Move("FromDeck", deck[i]))]
        for pivot in pivots:
            result_or.append(
                Relation(Move("FromDeck", pivot), Move("FromDeck", deck[i]))
            )
        result.append(result_or)
    return result


def doable_to_stack(game: Game, card: Card) -> CNF:
    lower = card.lower_rank()

    this_move = Move("ToStack", card)
    result = []
    if lower is not None:
        result.append([Relation(Move("ToStack", lower), this_move)])

    result += may_exists_at(game, card, this_move)

    blocking = game.find_blocking_visible(card)
    if blocking is not None:
        other = card.swap_suit()
        result += cnf_or(
            [[Relation(Move("ToStack", blocking), this_move)]],
            may_exists_at(game, other, this_move),
        )

    return result


def may_have_empty_pile(game: Game, move: Move) -> CNF:
    result = []
    for hidden, visible in game.tableau:
        if len(hidden) == 0 and len(visible) == 0:
            return CNF_True
        result.append(Relation(Move("Reveal", (hidden + visible)[0]), move))

    return [result]


def doable_from_deck(game: Game, card: Card) -> CNF:
    this_move = Move("FromDeck", card)
    result = [[]]
    lower = card.lower_rank()
    if lower is not None:
        result = cnf_or(result, [[Relation(Move("ToStack", lower), this_move)]])

    result = cnf_or(result, may_solved_at(game, card, this_move))

    return result


def may_solved_at(game: Game, card: Card, move: Move) -> CNF:
    higher_card = card.higher_rank()
    if higher_card is not None:
        higher_card = higher_card.swap_color()
        return cnf_or(
            may_exists_at(game, higher_card, move),
            may_exists_at(game, higher_card.swap_suit(), move),
        )
    else:

        # has to reveal one of the stuff
        return may_have_empty_pile(game, move)


def may_exists_at(game: Game, card: Card, move: Move) -> CNF:
    blocking = game.find_blocking(card)
    if blocking is not None:  # hidden card
        return [[Relation(Move("Reveal", blocking), move)]]
    elif game.is_deck(card):
        return [[Relation(Move("FromDeck", card), move)]]
    else:
        return CNF_True


def build_all(game: Game, step: int) -> CNF:
    result = []
    result += relational_draw(game, step)
    for rank in range(len(RANKS)):
        for suit in range(len(SUITS)):
            card = Card(rank, suit)
            if game.is_hidden(card) or game.is_first_visible(card):
                result += doable_reveal(game, card)

            if game.is_deck(card):
                result += doable_from_deck(game, card)
            result += doable_to_stack(game, card)
    return result


def simplifies(all_rel: CNF) -> List[Tuple[Move, List[Move]]]:
    simp = []
    for rel in all_rel:
        assert len(rel) > 0
        after = rel[0].after
        befores = []
        for r in rel:
            assert after == r.after
            befores.append(r.before)

        # clean up self
        simp.append((after, [i for i in befores if i != after]))
    return simp


def solve_simplified(simp):
    ordered = []
    unordered = set()
    for after, befores in simp:
        unordered.add(after)
        unordered.update(befores)
    # ordering
    while len(unordered) > 0:
        found = None
        for e in unordered:
            # check if it's good
            good = True
            for after, _ in simp:
                if e == after:
                    good = False
                    break
            if good:
                found = e
                break
        if found is None:
            print(ordered)
            print(unordered)
            print("failed", len(ordered), len(unordered))
            return None

        ordered.append(e)
        unordered.remove(e)
        # filtering
        simp = [s for s in simp if e not in s[1]]

    return ordered


def main():
    import json

    data = """
    {"tableau piles": [
    ["QS"],
    ["10s","QC"],
    ["As","5s","6S"],
    ["9h","10d","Ad","3S"],
    ["5c","7d","Qd","10c","KS"],
    ["2d","Jc","9s","8c","2h","9C"],
    ["5d","Qh","8d","Kc","4d","8h","6H"]
    ],"stock": ["KH","7C","2S","AH","9D","4C","3D","6C","8S","JD","AC","JS","KD","JH","3H","4S","7H","5H","3C","4H","10H","2C","6D","7S"],
    "foundation": [[],[],[],[]]}
    """

    game = json.loads(data)

    g = Game.from_str(game)
    all_rel = build_all(g, 1)

    simp = simplifies(all_rel)
    solve_simplified(simp)


if __name__ == "__main__":
    main()
