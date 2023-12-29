from engine import Solitaire
import torch
from torch import nn
from torch.nn import functional as F

CARD_DIM = 13 + 4


def encode_cards(cards, n_size, dtype=torch.float32):
    assert n_size >= len(cards)
    encoded = torch.zeros((n_size, CARD_DIM), dtype=dtype)
    for i, (u, v) in enumerate(cards):
        if u < 0 or u >= 13:
            continue
        encoded[i, u] = 1
        encoded[i, v + 13] = 1
    return encoded


def encode_game(game: Solitaire, dtype=torch.float32):
    n_deck = 52 - game.n_piles * (game.n_piles + 1) // 2
    deck = encode_cards(game.deck, n_deck, dtype=dtype)
    draw_mask = torch.zeros((n_deck,), dtype=dtype)
    pos = game.cur_draw + game.cur_draw_step - 1
    if pos >= 0:
        draw_mask[pos] = 1

    final_stack = encode_cards(
        [(j - 1, i) for i, j in enumerate(game.final_stack[:4])], 4, dtype=dtype
    )

    n_hidden = torch.tensor([len(p) for p in game.hidden_piles], dtype=dtype)


    visible = torch.stack([encode_cards(p, 13, dtype=dtype) for p in game.visible_piles])


    return {"deck": deck, "mask": draw_mask, "final": final_stack, "hidden": n_hidden, "visible": visible}


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
        self.input_dim = n_deck * (CARD_DIM + 1) + 4 * CARD_DIM + n_piles + n_piles * 13 * CARD_DIM
        self.output_dim = (1+ 4 + n_piles) * (1+ 4 + n_piles)

        self.net = nn.Sequential(
            nn.Linear(self.input_dim, 256),
            nn.Mish(True),
            nn.Linear(256, 256),
            nn.Mish(True),
            nn.Linear(256, self.output_dim)
        )
    def forward(self, x):
        full = torch.concatenate([x.flatten() for x in enc.values()])

        return self.net(x)




g = Solitaire(12)

enc = encode_game(g)
bot = LonelyBot()

bot
print(full.shape)