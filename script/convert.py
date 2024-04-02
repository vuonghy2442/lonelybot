game_json = """{"tableau piles": [
["KC"],
["6s","8C"],
["9s","Ah","5S"],
["5d","Js","5h","QD"],
["Ac","7c","Jc","7h","KD"],
["10c","3h","4d","4h","6c","QS"],
["7d","3c","6h","5c","10h","9c","3S"]
],"stock": ["JD","10D","7S","10S","AD","8S","JH","2D","AS","3D","9D","9H","6D","KS","QH","2H","2S","4S","4C","KH","2C","8H","8D","QC"],
"foundation": [[],[],[],[]]}"""

SUIT_MAP = {"h": 0, "d": 1, "c": 2, "s": 3}

N_SUITS = len(SUIT_MAP)
RANK_MAP = {
    "A": 0,
    "2": 1,
    "3": 2,
    "4": 3,
    "5": 4,
    "6": 5,
    "7": 6,
    "8": 7,
    "9": 8,
    "10": 9,
    "J": 10,
    "Q": 11,
    "K": 12,
}

N_RANKS = len(RANK_MAP)
N_CARDS = N_SUITS * N_RANKS

import json

game = json.loads(game_json)

import itertools

cards = list(itertools.chain.from_iterable(game["tableau piles"])) + game["stock"][::-1]
cards = list(map(lambda c: RANK_MAP[c[:-1]] * N_SUITS + SUIT_MAP[c[-1].lower()], cards))
assert len(set(cards)) == len(cards) == N_CARDS


encode = 0

for i in range(N_CARDS - 1, 0, -1):
    pos = cards[: (i + 1)].index(i)
    encode = encode * (i + 1) + pos
    cards[pos], cards[i] = cards[i], cards[pos]

print(encode)
