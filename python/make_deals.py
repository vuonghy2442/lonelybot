"""Synthetic deals with known required structure, for model debugging.

deal_A.json: pure-depart game — four descending same-suit piles (4s on
top), deck holds A-3 and J-K of every suit. Zero moves/parks needed;
every card departs directly as its prefix completes.

deal_B.json: exactly-one-move game — the 2S is buried under 4D, and 4D's
prefix (3D) is buried under 6H in another pile; the 6H must move onto
7S (one Reveal), after which 3D, 4D, then 2S peel off. Everything else
departs from descending filler piles as prefixes complete.
"""
import json

RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
SUITS = ["H", "D", "C", "S"]


def card(rank, suit):
    return RANKS[rank] + SUITS[suit]


def deal_A():
    piles = []
    for s in range(4):
        piles.append([card(r, s) for r in range(9, 3, -1)])  # 10..4, top=4
    deck = []
    for r in range(0, 4):        # A,2,3,4?? no: A..3
        pass
    deck = [card(r, s) for r in range(0, 3) for s in range(4)]
    deck += [card(r, s) for r in range(10, 13) for s in range(4)]
    assert len(deck) == 24, len(deck)
    return {"tableau piles": piles, "stock": deck, "foundation": [[], [], [], []]}


def deal_B():
    # the designed core: 6H must move onto 7S exactly once
    p0 = ["2" + "s", "4D"]           # 2S hidden under 4D
    p1 = ["3" + "d", "6H"]           # 3D hidden under 6H
    p2 = ["7S"]                        # 7S top: 6H's host
    used = {
        ("2", "S"), ("4", "D"), ("3", "D"), ("6", "H"), ("7", "S"),
    }
    leftover = [
        (r, s)
        for r in range(13)
        for s in range(4)
        if (RANKS[r], SUITS[s]) not in used
    ]
    # filler piles: descending by rank so peeling works; 4 piles
    leftover.sort(key=lambda rs: -rs[0])
    fillers = [[], [], [], []]
    for i, (r, s) in enumerate(leftover[:20]):
        fillers[i % 4].append(card(r, s))
    rest = leftover[20:]
    assert len(rest) == 24, len(rest)
    piles = [p0, p1, p2] + fillers
    deck = [card(r, s) for r, s in rest]
    return {"tableau piles": piles, "stock": deck, "foundation": [[], [], [], []]}


if __name__ == "__main__":
    with open("deal_A.json", "w") as f:
        json.dump(deal_A(), f)
    with open("deal_B.json", "w") as f:
        json.dump(deal_B(), f)
    print("written deal_A.json deal_B.json")
