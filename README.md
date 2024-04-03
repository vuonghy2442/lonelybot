Lonelybot
=========
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

## Crates
- Lonelybot is a library crate with #no_std support, and can be use in webassembly
- Lonecli is a wrapper on lonelybot to provide features

## Build mode
- release: use lto (cargo build --release)
- dev: thin lto + debug info => for easy profiling (cargo build --profile=dev)
- release-with-debug: Release + debug info (cargo build --profile=release-with-debug)
- debug: default rust debug (cargo build)
- bench: For micro-benchmarking (cargo bench)

## Seed
There are 5 seed types
- ``default``: using Rust rng
- ``legacy``: similar to default, for compatibility with older version of this engine
- ``solvitaire``: re-implementation of [Solvitaire](https://github.com/thecharlieblake/Solvitaire) random
- ``klondike``-solver: re-implementation of [Klondike-Solver](https://github.com/ShootMe/Klondike-Solver) random
- ``greenfelt``: re-implementation of [Greenfelt](https://greenfelt.net/) based on [Minimal-Klondike](https://github.com/ShootMe/MinimalKlondike) source code
- ``exact``: converting a 256-bit integer (< 52!) to exact corresponding 52-card permutation

To input your own game, you can use `convert.py` in `script`, to convert the Solvitaire json format into an exact seed, which then you can input into `lonecli`. Currently it only support convert the initial state of the game.

## Run methods
This solver has a few modes

### Exact
Turn a seed into the exact permutation number
```sh
lonecli exact [seed_type] [seed]
```

Example run
```
lonecli exact solvitaire 22
```

Example output
```
75815935119064350470717521029623259780400326814603147288883495865917
```

### Random
Do random play on 10000 different games from seed to seed + 10000 to see how many games it can win

```sh
lonecli random [seed_type] [seed]
```

Example run
```
lonecli exact default 0
```

Example output
```
Total win 1109/10000
```


### Print
```sh
lonecli print [seed_type] [seed]
```
This will print the board in json format (in solvitaire format)

Example output
```json
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
```
The format:
- Card: <rank><suit>
    - Rank: A, 1..10, J, Q, K
    - Suit: H (heart), D (diamond), C (club), S (spade)
    - Upper case suit => face up card
    - Lower case suit => face down card
- Pile:  An array of cards in order of top-down
- Tableau piles: an array of piles in order of left-right
- Stock: an array of cards in the dealing stock, dealing from the end.
- Foundation: an array of 4 arrays (corresponding to the suits)


### Bench
```sh
lonecli bench [seed_type] [seed]
```

Example input
```sh
lonecli bench default 25
```

Example output
```
3555 9858569.0515807 op/s
```

The first number is the number of move made. The second one is the rate of move making.

### Solve

```sh
lonecli solve [seed_type] [seed]
```

First it will print the game. Then it will solve it.

Example run
```sh
lonecli solve default 41
```

Example impossible output
```
Run in 7.4628000000000005 ms
Statistic
Total visit: 88354
Transposition hit: 51853 (rate 0.5868777870837766)
Miss state: 36501
Max depth search: 32
Current progress: 1/1 5/5 5/5 6/6 5/5 3/3 3/3 3/3
Impossible
```

It will print the progress every 1 second.

You can early terminate the search by pressing ctrl-C

The progress consists of:
- Total visit: the number of states visited
- Transposition hit: the number of states skipped due to transposition hit and its ratio compare to total visit
- Miss state: the number of states that don't hit transposition table (total visit - transposition hit)
- Max depth search: the maximum number of move made in the search
- Current progress: a list of first 8 current move position/total move in the current search path.

Example run
```sh
lonecli solve default 12
```

Example solved output
```
Run in 0.1812 ms
Statistic
Total visit: 118
Transposition hit: 5 (rate 0.0423728813559322)
Miss state: 113
Max depth search: 91
Current progress: 0/1 0/5 0/1 0/5 0/4 0/4 0/4 0/3
Solvable in 92 moves
PS A♦, R 5♠, PS A♠, ....
Pile(4) Stack(1) A♦, Pile(6) Pile(5) 5♠, ....
```

There are two type of solution notation:
- The first line is the specialized notation (explained bellow)
- The second line is the standardized notation with the format as a tuple of source position, destination position, moving card.

The special move of drawing from the stock is represent as a move from the stock (Deck) to the stock (Deck)

There are 3 position: Deck (the stock), Pile (the 0-indexed tableaus), Stack (the 0-indexed foundation stack)

### Solve loop
```sh
lonecli rate [seed_type] [seed]
```

This will sequentially solve the random game generate from seed, seed+1,...

You can still terminate solving the current game by pressing ctrl-C.

To terminate the whole process, pressing ctrl-C twice in a short amount of time (< 500ms)

Example run
```sh
lonecli rate default 0
```

Example output
```
Run D-0 Solved: (1-0/1 ~ 0.2065<=1.0000<=1.0000) 96 96 95 in 0.20 ms.
Run D-1 Solved: (2-0/2 ~ 0.3424<=1.0000<=1.0000) 10804 6188 87 in 1.05 ms.
Run D-2 Solved: (3-0/3 ~ 0.4385<=1.0000<=1.0000) 52426 26220 81 in 4.32 ms.
Run D-3 Solved: (4-0/4 ~ 0.5101<=1.0000<=1.0000) 192 164 87 in 0.24 ms.
Run D-4 Solved: (5-0/5 ~ 0.5655<=1.0000<=1.0000) 3141 1938 93 in 0.54 ms.
Run D-5 Solved: (6-0/6 ~ 0.6097<=1.0000<=1.0000) 2835 1582 92 in 0.37 ms.
Run D-6 Solved: (7-0/7 ~ 0.6457<=1.0000<=1.0000) 14953 6102 89 in 1.23 ms.
Run D-7 Unsolvable: (7-0/8 ~ 0.5291<=0.8750<=0.9776) 3439 1928 28 in 0.45 ms.
...
```

Each row correspond to a game
```
Run [game_seed] [solve_result]: ([solvable]-[terminated]/[total] ~ [solvable_lb_95%]<=[solvable_rate]<=[solvable_ub_95%]) [total_states] [unique_states] [max_depth] in [run_time] ms.
```

### Play

You can play out the game.
Due the optimizations, the available actions are quite unusual, and performing them may result in weird results
- One action can be equivalent to multiple actions combined in standard game
- The result of the action is impossible but it is equivalent to the possible result in the standard game.
- Missing some actions (should be inferior to the available actions)


```sh
lonecli play [seed_type] [seed]
```

Example run
```sh
lonecli play default 0
```

Example output
```
0 Q♣  1 8♦ >2 8♥  3 2♣  4 K♥ >5 4♣  6 4♠  7 2♠ >8 2♥  9 Q♥  10 K♠ >11 6♦  12 9♥  13 9♦ >14 3♦  15 A♠  16 2♦ >17 J♥  18 8♠  19 A♦ >20 10♠  21 7♠  22 10♦ >23 J♦
                1.   2.   3.   4.
5       6       7       8       9       10      11
K♣      **      **      **      **      **      **
        8♣      **      **      **      **      **
                5♠      **      **      **      **
                        Q♦      **      **      **
                                K♦      **      **
                                        Q♠      **
                                                3♠

0.R Q♠, 1.R Q♦, 2.DP 2♥, 3.DP J♥, 4.DP J♦,
Hash: 1729382259552616448
Move:
```

You enter the move number to move:

There are currently 5 types of move:
- R ``card``: Revealing the hidden card about the ``card``
- SP ``card``: Moving the ``card`` from the foundation stack into the tableau (the pile in my term)
- DP ``card``: Moving the ``card`` from the stock (the deck in my term) to the tableau
- DS ``card``: Moving the ``card`` from the stock to the foundation stack
- PS ``card``: Moving the ``card`` from the tableau to the stack (potentially also do a reveal)

### HOP solver
In this mode it will try to solve the game with no undo. (actually it is using something more like MCTS not HOP)
```sh
lonecli hop [seed_type] [seed]
```

Example run
```sh
lonecli hop default 0
```

Example output
```
DP J♥,
DP 2♦,
DS A♠,
...
Solved
```

Example run
```sh
lonecli hop default 5
```

Example output
```
DP 3♦,
DP 5♦,
DS A♥,
...
Lost
```

### HOP loop
```sh
lonecli hop-loop [seed_type] [seed]
```

- In this mode it will try to solve the game with no undo from the given seed and moving on to the next seed
Example run
```sh
lonecli hop-loop default 0
```

Example output
```
1/1 ~ 0.2065 < 1.0000 < 1.0000 in 3.3991924s
2/2 ~ 0.3424 < 1.0000 < 1.0000 in 2.0126367s
3/3 ~ 0.4385 < 1.0000 < 1.0000 in 3.6193054s
4/4 ~ 0.5101 < 1.0000 < 1.0000 in 2.4423182s
...
119/239 ~ 0.4351 < 0.4979 < 0.5608 in 3.4916281s
...
```


### Graph
Create a game graph of the game from the seed
```sh
lonecli graph [seed_type] [seed] [file.csv]
```

Example run
```sh
lonecli graph klondike-solver 338 test.csv
```

Example output
```
Run in 14.779499999999999 ms
Statistic
Total visit: 175203
Transposition hit: 87772 (rate 0.500973156852337)
Miss state: 87431
Max depth search: 118
Current progress: 5/5 4/4 4/4 4/4 4/4 6/6 4/4 4/4
Graphed in 175205 edges
Save done
```

Output file
```cs
s,t,e,id
1729382259552616448,1729382259552550912,Reveal,0
1729382259552550912,1729382259505364992,Reveal,1
1729382259505364992,1729382259505233920,Reveal,2
1729382259505233920,1729382259497369600,Reveal,3
...
1693353462533652480,1693353462533259264,Reveal,175203
```

There are 4 columns:
- s: The source id
- t: The destination id
- e: The move type (with more distinction between PileStack PileStackReveal)
- id: The DFS ordering


## Limitations

- Cannot disallow worrying back
- May not find the shortest solution

## Running results

As far as my knowledge goes, up to March 2024, this solver is the state of the art for checking solvability of a standard 3-card klondike game. I didn't test much on the general case of n-card game, but it is likely to be the best as well.

I cross-checked my package with Solvitaire (published result) using the Klondike-Solver seed from 0 to 50k, and with the 1M games with Solvitaire seed from 1 to 1M. And I also cross-checked between different versions of my own package up to much more games (at least 100k and can be up to 2M games).

However, due to having a lot of specific optimizations that haven't been rigorously proven (but I intended to make sure it's always correct, not just a "very good heuristic" but can be wrong in extremely few cases). So any wrong solvability result is a bug.


### Thoughtful Klondike
Run with Solvitaire seed
Run S-1071884 Solved: (878240-0/1071884 ~ 0.8186<=0.8193<=0.8201) 12711939 4517405 93 in 10356.75 ms.

Run with Klondike Solver seed
Run K-3544902 Solved: (2904790-0/3544903 ~ 0.8190<=0.8194<=0.8198) 5062 3001 93 in 4.44 ms.

So this is the new state of the art result for solvability: 81.94 ± 0.04 (compared to the previous from Solvitaire 81.945 ± 0.084) at 95% confidence

This result is computed on 1 cpu core for a few days. With more resources, it can be easily improved.

One other notable thing is that there's no game that it can't decide in a reasonable amount of time that I'm aware of.

### Random Klondike
So with my hop/MCTS solver, I also achieve the state of the art for random Klondike

25319/56932 ~ 0.4406 < 0.4447 < 0.4488 in 7.359837524s

So the solvability is 44.47 ± 0.41 (compared to the previous 36.97 ± 1.92 from [this paper](https://ojs.aaai.org/index.php/ICAPS/article/view/13363/13211))

The average running time for one game is only a few seconds.

However due to significant improvement, I think this needs more verification.

## Method

It started from implementing the ideas from the Solvitaire paper in Rust (which is tagged as version 0.1). Then I figure out a suit symmetry in the game state, combining with more dominances (technical term in the Solvitaire paper) and move pruning. This allows me to vastly reduced the states (around an order of magnitude) compared to the original method, combining with highly optimized implementation (around 2 orders of magnitude faster in search rate). In total, it runs around 3 orders of magnitude faster. Also after a lot of move pruning, the game tree is now a DAG (when remove cycles of 2).

I will try to find some time to write a more detailed description of the method.