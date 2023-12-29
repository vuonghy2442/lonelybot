import random
import colorama
from colorama import Fore, Back, Style

colorama.init()

CARDS = [(i, j) for i in range(13) for j in range(4)]

COLOR = [Fore.RED, Fore.RED, Fore.BLACK, Fore.BLACK]
SYMBOLS = "♥♦♣♠"
NUMBERS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]


def print_card(card, end=" "):
    u, v = card
    if u >= 0:
        print(
            f"{Back.WHITE}{COLOR[v]}{NUMBERS[u]}{SYMBOLS[v]}{Style.RESET_ALL}", end=end
        )
    else:
        print(f"  ", end=end)


def fit_after(card_a, card_b):
    return card_a[0] == card_b[0] + 1 and card_a[1] ^ card_b[1] >= 2


class Solitaire:
    def __init__(self, seed, draw_step=3, n_piles=7):
        random.seed(seed)
        shuffled = CARDS.copy()
        random.shuffle(shuffled)

        self.n_piles = n_piles
        self.hidden_piles = [None] * n_piles
        self.visible_piles = [None] * n_piles

        self.final_stack = [0] * 4  # how many cards stacked

        used_cards = 0
        for i in range(n_piles):
            self.hidden_piles[i] = shuffled[used_cards : used_cards + i]
            self.visible_piles[i] = shuffled[used_cards + i : used_cards + i + 1]
            used_cards += i + 1

        self.deck = shuffled[used_cards:]
        self.draw_step = draw_step
        self.cur_draw_step = draw_step
        self.cur_draw = 0
        self.score = 0

    def display(self):
        print("Score: ", self.score)
        print("Deck 0: ", end="")

        if self.cur_draw_step > 0:
            for i, j in self.deck[self.cur_draw : self.cur_draw + self.cur_draw_step]:
                print_card((i, j))
        elif self.cur_draw + self.cur_draw_step - 1 >= 0:
            print_card(self.deck[self.cur_draw + self.cur_draw_step - 1])

        print("\t\t", end="")

        for i in range(4):
            print(f"{i+1}.", end="")
            print_card((self.final_stack[i] - 1, i))
        print()

        for i in range(self.n_piles):
            print(f"{i+5}\t", end="")
        print()

        i = 0
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

    def move(self, src: int, dst: int) -> bool:
        # special encoding:
        # 0 = deck
        # 1, 2, 3, 4 = the final stack
        # 5, ... = the piles
        # return if the move is valid
        # if src == dst == 0 then it is drawing new deck

        if src == dst == 0:
            self.cur_draw += self.cur_draw_step
            if self.cur_draw >= len(self.deck):
                self.cur_draw = 0
                # decrease the score :3
                self.score -= 2

            self.cur_draw_step = min(len(self.deck) - self.cur_draw, self.draw_step)
            return True

        if (
            dst == 0
            or src == dst
            or src < 0
            or dst < 0
            or src >= self.n_piles + 5
            or dst >= self.n_piles + 5
        ):
            return False

        # handle drawing from deck or maybe from the final stack
        if src < 5:
            if src == 0:
                draw_pos = self.cur_draw + self.cur_draw_step - 1
                if draw_pos < 0:
                    return False  # nothing left to draw

                u, v = self.deck[draw_pos]
            else:
                v = src - 1
                if self.final_stack[v] == 0:
                    return False  # nothing to draw
                u = self.final_stack[v] - 1

            # final stack
            if dst < 5:
                # if doesn't match the number of card put, or the destination is wrong type
                if v != dst - 1 or u != self.final_stack[v]:
                    return False
                self.final_stack[v] += 1
            else:
                dst_pos = dst - 5

                # only king can move to empty pile
                if len(self.visible_piles[dst_pos]) == 0 and u != 12:
                    assert (
                        len(self.hidden_piles[dst_pos]) == 0
                    )  # can't have any other cards
                    return False
                elif not fit_after(self.visible_piles[dst_pos][-1], (u, v)):
                    print("Yoooo", u, v)
                    return False
                self.visible_piles[dst_pos].append((u, v))

            if src == 0:
                del self.deck[draw_pos]
                self.cur_draw_step -= 1
                self.score += 5 if dst > 5 else 20  # yay improve score
            else:
                self.final_stack[v] -= 1
                self.score -= 15  # reduce score

            return True
        else:
            src_pos = src - 5
            # moving from the empty pile
            src_pile = self.visible_piles[src_pos]
            if len(src_pile) == 0:
                assert (
                    len(self.hidden_piles[src_pos]) == 0
                )  # can't have any other cards
                return False

            n_moved = 0

            if dst < 5:
                # moving to the stack
                u, v = src_pile[-1]
                if v != dst - 1 or u != self.final_stack[v]:
                    return False
                self.final_stack[v] += 1
                n_moved = 1
                # yay more score
                self.score += 15
            else:
                dst_pos = dst - 5
                # finding the good position to move :)
                dst_pile = self.visible_piles[dst_pos]
                if len(dst_pile) == 0:
                    # move to empty pos then should move everything
                    if src_pile[0][0] != 12:  # king
                        return False
                    n_moved = len(src_pile)  # move everything
                else:
                    pos_move = (dst_pile[-1][0] - 1) - src_pile[0][0]
                    if pos_move < 0 or pos_move >= len(src_pile):
                        # the source pile is too small to move to the dst
                        return False
                    if not fit_after(dst_pile[-1], src_pile[pos_move]):
                        # wrong type
                        return False
                    n_moved = len(src_pile) - pos_move

                # move :)
                dst_pile.extend(src_pile[-n_moved:])

            del src_pile[-n_moved:]
            if len(src_pile) == 0 and len(self.hidden_piles[src_pos]) > 0:
                # unlocking new score :))
                self.score += 5
                src_pile.append(self.hidden_piles[src_pos].pop())


# 17
game = Solitaire(12)

game.move(11, 2)
game.move(10, 11)

game.display()

while True:
    move = map(int, input("Move here: ").strip().split(" "))
    print(game.move(*move))
    game.display()
