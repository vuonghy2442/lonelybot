import random
import colorama
from copy import deepcopy
from colorama import Fore, Back, Style
from typing import  Tuple, Generator, Optional
import os
import time
import numba as nb
import numpy as np



CardType = nb.types.UniTuple(nb.uint8, 2)
CardPile = nb.types.ListType(CardType)

MoveType = nb.types.UniTuple(nb.uint8, 2)
MoveList = nb.types.ListType(MoveType)

COLOR = [Fore.RED, Fore.RED, Fore.BLACK, Fore.BLACK, Fore.WHITE]
SYMBOLS = "♥♦♣♠X"
NUMBERS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "X"]

N_SUITS = 4
N_RANKS = 13

FAKE_CARD = (np.uint8(N_RANKS), np.uint8(N_SUITS))

def print_card(card: CardType, end=" "):
    u, v = card
    if u >= 0:
        print(
            f"{Back.WHITE}{COLOR[v]}{NUMBERS[u]}{SYMBOLS[v]}{Style.RESET_ALL}", end=end
        )
    else:
        print(f"  ", end=end)


@nb.njit
def fit_after(card_a: CardType, card_b: CardType):
    return card_a[0] == card_b[0] + 1 and card_a[1] ^ card_b[1] >= 2


@nb.experimental.jitclass(
    {
        'n_piles': nb.uint8,
        'draw_step': nb.uint8,
        'draw_next': nb.uint8,
        'hidden_piles':  nb.types.ListType(CardPile),
        'visible_piles': nb.types.ListType(CardPile),
        'final_stack': nb.uint8[:],
        'deck': CardPile
    }
)
class Solitaire:
    # __slots__ = 'n_piles', 'hidden_piles', 'visible_piles', 'final_stack', 'deck', 'draw_step', 'draw_next'

    def __init__(self, seed: int, draw_step: int = 3, n_piles: int =7):
        if seed == 0 and draw_step == 0 and n_piles == 0:
            return

        np.random.seed(seed)

        # shuffled = [(nb.uint8(i),nb.uint8(j)) for i in range(13) for j in range(4)]


        shuffled = np.random.permutation(N_RANKS * N_SUITS)
        shuffled = nb.typed.List([(np.uint8(card // N_SUITS), np.uint8(card % N_SUITS)) for card in shuffled])

        self.n_piles = n_piles # constant
        self.hidden_piles = nb.typed.List.empty_list(CardPile)
        self.visible_piles = nb.typed.List.empty_list(CardPile)

        self.final_stack = np.zeros((N_SUITS + 1,), dtype=np.uint8)  # how many cards stacked

        used_cards = 0
        for i in range(n_piles):
            self.hidden_piles.append(nb.typed.List.empty_list(CardType))
            self.hidden_piles[-1].append(FAKE_CARD)
            self.hidden_piles[-1].extend(shuffled[used_cards : used_cards + i])
            self.visible_piles.append(shuffled[used_cards + i : used_cards + i + 1])
            used_cards += i + 1

        self.deck = shuffled[used_cards:]
        self.draw_step = draw_step # constant
        self.draw_next = draw_step

    def gen_moves(self) -> MoveList:
        result = nb.typed.List.empty_list(MoveType)
        result.append((np.uint8(0), np.uint8(0)))

        for src in range(5):
            # move deck to final stack
            if src == 0:
                draw_pos = self.draw_next - 1
                if draw_pos < 0:
                    continue
                else:
                    # can actually draw from the deck
                    u, v = self.deck[draw_pos]
            else:
                v = src - 1
                u = self.final_stack[v] - 1
                if u < 0:
                    continue

            # move to final stack :)
            if src == 0 and self.final_stack[v] == u:
                result.append((0, v + 1))

            for id, pile in enumerate(self.visible_piles):
                if fit_after(pile[-1], (u, v)):
                    result.append((src, id + 5))

        for src, src_pile in enumerate(self.visible_piles):
            # move to the final stack
            u, v = src_pile[-1]
            if self.final_stack[v] == u:
                result.append((src + 5, v + 1))

            for dst, dst_pile in enumerate(self.visible_piles):
                if src_pile == dst_pile:
                    continue

                pos_move = src_pile[0][0] - (dst_pile[-1][0] - 1)
                if pos_move < 0 or pos_move >= len(src_pile):
                    continue
                if not fit_after(dst_pile[-1], src_pile[pos_move]):
                    continue

                result.append((src + 5, dst + 5))
        return result

    def copy(self):
        copied = Solitaire(0, 0, 0)
        copied.n_piles = self.n_piles
        copied.draw_step = self.draw_step
        copied.draw_next = self.draw_next
        copied.hidden_piles = nb.typed.List([p.copy() for p in self.hidden_piles])
        copied.visible_piles =  nb.typed.List([p.copy() for p in self.visible_piles])
        copied.deck = self.deck.copy()
        copied.final_stack = self.final_stack.copy()
        return copied


    def is_won(self) -> bool:
        return np.all(self.final_stack[:N_SUITS] == N_RANKS)

    def move(self, src: int, dst: int) -> (bool, int):
        # special encoding:
        # 0 = deck
        # 1, 2, 3, 4 = the final stack
        # 5, ... = the piles
        # return if the move is valid
        # if src == dst == 0 then it is drawing new deck

        reward = 0

        if src == dst == 0:
            if self.draw_next >= len(self.deck):
                self.draw_next = 0
                # decrease the score :3
                reward -= 2
            self.draw_next = min(self.draw_next + self.draw_step, len(self.deck))
            return True, reward

        if (
            dst == 0
            or src == dst
            or src < 0
            or dst < 0
            or src >= self.n_piles + 5
            or dst >= self.n_piles + 5
        ):
            return False, reward

        # handle drawing from deck or maybe from the final stack
        if src < 5:
            if src == 0:
                draw_pos = self.draw_next - 1
                if draw_pos < 0:
                    return False, reward  # nothing left to draw

                u, v = self.deck[draw_pos]
            else:
                v = src - 1
                if self.final_stack[v] == 0:
                    return False, reward  # nothing to draw
                u = self.final_stack[v] - 1

            # final stack
            if dst < 5:
                # if doesn't match the number of card put, or the destination is wrong type
                if v != dst - 1 or u != self.final_stack[v]:
                    return False, reward
                self.final_stack[v] += 1
            else:
                dst_pos = dst - 5

                # can't really be empty because of fake cards
                assert len(self.visible_piles[dst_pos]) > 0

                if not fit_after(self.visible_piles[dst_pos][-1], (u, v)):
                    return False, reward
                self.visible_piles[dst_pos].append((u, v))

            if src == 0:
                del self.deck[draw_pos]
                self.draw_next -= 1
                reward += 5 if dst > 5 else 20  # yay improve score
            else:
                self.final_stack[v] -= 1
                reward -= 15  # reduce score

            return True, reward
        else:
            src_pos = src - 5
            # moving from the empty pile
            src_pile = self.visible_piles[src_pos]

            n_moved = 0

            if dst < 5:
                # moving to the stack
                u, v = src_pile[-1]
                if v != dst - 1 or u != self.final_stack[v]:
                    return False, reward
                self.final_stack[v] += 1
                n_moved = 1
                # yay more score
                reward += 15
            else:
                dst_pos = dst - 5
                # finding the good position to move :)
                dst_pile = self.visible_piles[dst_pos]
                assert len(dst_pile) > 0

                pos_move = src_pile[0][0] - (dst_pile[-1][0] - 1)
                if pos_move < 0 or pos_move >= len(src_pile):
                    # the source pile is too small to move to the dst
                    return False, reward
                if not fit_after(dst_pile[-1], src_pile[pos_move]):
                    # wrong type
                    return False, reward
                n_moved = len(src_pile) - pos_move

                # move :)
                dst_pile.extend(src_pile[-n_moved:])

            del src_pile[-n_moved:]
            if len(src_pile) == 0 and len(self.hidden_piles[src_pos]) > 0:
                # unlocking new score :))
                reward += 5
                src_pile.append(self.hidden_piles[src_pos].pop())
        return True, reward


def display(self):
    print("Deck 0: ", end="")

    for i, j in self.deck[max(0, self.draw_next - self.draw_step) : self.draw_next]:
        print_card((i, j))

    print("\t\t", end="")

    for i in range(4):
        print(f"{i+1}.", end="")
        print_card((self.final_stack[i] - 1, i))
    print()

    for i in range(self.n_piles):
        print(f"{i+5}\t", end="")
    print()

    i = 1  # skip the hidden layer
    while True:
        is_print = False
        for j in range(self.n_piles):
            cur_pile = self.visible_piles[j]

            n_hidden = len(self.hidden_piles[j])
            n_visible = len(cur_pile)
            if n_hidden > i:
                print("**\t", end="")
                is_print = True
            elif i < n_hidden + n_visible:
                print_card(cur_pile[i - n_hidden], end="\t")

                is_print = True
            else:
                print("  \t", end="")
        print()
        i += 1
        if not is_print:
            break

def slow_gen_move(game):
    for i in range(5 + game.n_piles):
        for j in range(5 + game.n_piles):
            g = game.copy()
            if g.move(i, j)[0]:
                yield (i, j)


def check_gen_move(game):
    g = game.copy()
    all_move = list(game.gen_moves())
    slow_move = list(slow_gen_move(g))
    if set(all_move) != set(slow_move):
        print(all_move, slow_move)
        assert False
    return all_move



def game_loop(game):

    # seed 12
    # game.move(11, 2)
    # game.move(10, 11)
    # game.move(11, 5)
    # game.move(11, 9)
    # game.move(11, 3)
    # game.move(0, 0)
    # game.move(0, 7)
    # game.move(0, 0)
    # game.move(0, 0)
    # game.move(0, 0)
    # game.move(0, 0)
    # game.move(0, 0)
    # game.move(0, 9)
    # game.move(0, 0)
    # game.move(0, 9)
    # game.move(0, 0)
    # game.move(0, 0)
    # game.move(0, 0)
    # game.move(0, 11)
    # game.move(0, 11)
    # game.move(6, 11)
    # game.move(6, 4)

    display(game)

    while True:
        move = map(int, input("Move here: ").strip().split(" "))
        try:
            print(game.move(*move))
        except:
            print('Invalid')
        game.display()


def test(seed=17, n_piles=7, verbose=True):
    total_reward = 0

    start = time.time()

    game = Solitaire(seed, n_piles=n_piles)
    moves = check_gen_move(game)
    print('Init time', time.time() - start)

    start = time.time()

    game = Solitaire(seed, n_piles=n_piles)
    for _ in range(100):
        moves = check_gen_move(game)
        move = random.choice(moves)

        if verbose:
            game.display()
            print(moves)
            print(move)

        valid, reward = game.move(*move)
        assert valid
        total_reward += reward

    print('Simulating time', time.time()-start)
    print(seed, total_reward)
    game_loop(game)

if __name__ == '__main__':
    colorama.init()
    seed = int.from_bytes(os.urandom(4), byteorder='little')
    print(seed)
    test(seed=seed, verbose=0)
    # game = Solitaire(seed)
    # game_loop(game)
