from engine import Solitaire, FAKE_CARD
import torch
from torch import nn

CARD_DIM = 1 + 4


def encode_cards(cards, n_size, dtype=torch.float32):
    if cards[0][0] == 13:
        cards = cards[1:]

    assert n_size >= len(cards)
    encoded = torch.zeros((n_size, CARD_DIM), dtype=dtype)

    for i, (u, v) in enumerate(cards):
        if u < 0 or u >= 13:
            continue
        encoded[i, 0] = u
        encoded[i, v + 1] = 1
    return encoded


def encode_game(game: Solitaire, dtype=torch.float32, device="cuda:0"):
    n_deck = 52 - game.n_piles * (game.n_piles + 1) // 2
    deck = encode_cards(game.deck, n_deck, dtype=dtype)
    pos = game.draw_next - 1
    if pos >= 0:
        draw_card = deck[pos:pos+1]
    else:
        draw_card = FAKE_CARD

    final_stack = encode_cards(
        [(j - 1, i) for i, j in enumerate(game.final_stack[:4])], 4, dtype=dtype
    )

    n_hidden = torch.tensor([len(p) for p in game.hidden_piles], dtype=dtype)

    visible = torch.stack(
        [encode_cards(p, 13, dtype=dtype) for p in game.visible_piles]
    )

    visible_rev = torch.stack(
        [encode_cards(p, 13, dtype=dtype) for p in game.visible_piles[::-1]]
    )


    valid_moves = torch.zeros((5 + game.n_piles) * (5 + game.n_piles), dtype=torch.bool)
    for move in game.gen_moves():
        valid_moves[move[0] * (5 + game.n_piles) + move[1]] = 1

    enc = {
        "deck": deck,
        "mask": draw_card,
        "final": final_stack,
        "hidden": n_hidden,
        "visible": visible,
        "visible_rev": visible_rev,
    }
    return torch.concatenate([x.flatten() for x in enc.values()]).to(
        device
    ), valid_moves.to(device)


class LonelyBot(nn.Module):
    def __init__(self, n_piles=7):
        super(LonelyBot, self).__init__()
        # input is the shuffled deck stack
        n_deck = 52 - n_piles * (n_piles + 1) // 2
        # the cards in the deck: (n_deck, card_dim)

        # mask for the current draw card (n_deck)

        # cards on the final stack (4, card_dim)
        # n number of cards in the hidden piles (n_piles,)
        # visible cards in the stack (n_piles, 13, card_dim)

        self.n_deck = n_deck
        self.n_piles = n_piles
        self.input_dim = (
            (n_deck + 1) * (CARD_DIM) + 4 * CARD_DIM + n_piles + n_piles * 13 * CARD_DIM * 2
        )
        self.output_dim = (1 + 4 + n_piles) * (1 + 4 + n_piles)

        self.net = nn.Sequential(
            nn.Linear(self.input_dim, 256),
            nn.Mish(True),
            nn.Linear(256, 256),
            nn.Mish(True),
            nn.Linear(256, 256),
            nn.Mish(True),
            nn.Linear(256, 256),
            nn.Mish(True),
            nn.Linear(256, self.output_dim),
        )

    def forward(self, x, y):
        policy = self.net(x)
        policy[~y] = -torch.inf
        return policy
