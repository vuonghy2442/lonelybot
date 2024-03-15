# lonelybot solver
## Build mode
- release: use lto (cargo build --release)
- dev: minor optimization + thin lto + debug info => for easy profiling (cargo build --profile=dev)
- release-with-debug: Release + debug info (cargo build --profile=release-with-debug)
- debug: default rust debug (cargo build)
- bench: For microbenchmarking (cargo bench)

## Seed
There are 5 seed types
- ``default``: using simple Rust rng
- ``legacy``: similar to default, for combatibility with older version of this engine
- ``solvitaire``: reimplemenation of [Solvitaire](https://github.com/thecharlieblake/Solvitaire) random
- ``klondike``-solver: reimplementation of [Klondike-Solver](https://github.com/ShootMe/Klondike-Solver) random
- ``greenfelt``: reimplementation of [Greenfelt](https://greenfelt.net/) based on [Minimal-Klondike](https://github.com/ShootMe/MinimalKlondike) source code

## Run methods
This solver has a few modes

### Print
```sh
lonelybot print [seed_type] [seed]
```
This will print the board in json format (in solvitaire format)

Example output
```json
{"tableau piles": [
["7D"],
["Kc","3C"],
["6s","8c","6H"],
["9s","Ah","5s","5C"],
["5d","Js","5h","Qd","10H"],
["Ac","7c","Jc","7h","Kd","9C"],
["10c","3h","4d","4h","6c","Qs","3S"]
],"stock": ["JD","10D","7S","10S","AD","8S","JH","2D","AS","3D","9D","9H","6D","KS","QH","2H","2S","4S","4C","KH","2C","8H","8D","QC"]}
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


### Bench
```sh
lonelybot bench [seed_type] [seed]
```

Example input
```sh
lonelybot bench default 25
```

Example output
```
4030 3508313.7459737095 op/s
```

The first number is the number of move made. The second one is the rate of move making.

### Solve

```sh
lonelybot solve [seed_type] [seed]
```

First it will print the game. Then it will solve it.

Example run
```sh
loneybot solve legacy 28
```

Example output
```
{"tableau piles": [
["AS"],
["2d","KD"],
["10d","8c","KC"],
["10h","Jc","Js","8H"],
["10c","7s","4h","3s","5C"],
["4c","9h","7h","5s","Qd","7D"],
["9d","3d","7c","6d","Ks","Qh","9S"]
],"stock": ["6C","2H","AD","QS","4D","3C","5D","JD","2C","6H","5H","8S","9C","6S","QC","8D","AH","10S","4S","3H","2S","KH","AC","JH"]}
Run in 300.3384 ms
Statistic
Total visit: 1513174
Transposition hit: 943785 (rate 0.6237121441420485)
Miss state: 569389
Max depth search: 26
Current progress: 1/1 7/7 5/5 3/3 4/4 3/3 2/2 4/4
Impossible
```

It will print the progress every 1 second.

You can early terminate the search by pressing ctrl-C

The progress consists of:
- Total visit: the number of states visited
- Transposition hit: the number of states skipped due to transposition hit and its ratio compare to total visit
- Miss state: the number of stats that don't hit transposition table (total visit - transposition hit)
- Max depth search: the maximum number of move made in the search
- Current progress: a list of first 8 current move position/total move in the current search path.

### Solve loop
```sh
lonelybot rate [seed_type] [seed]
```

This will sequentially solve the random game generate from seed, seed+1,...

You can still terminate solving the current game by pressing ctrl-C.

To terminate the whole process, pressing ctrl-C twice in a short amount of time (< 500ms)

Example run
```sh
loneybot rate legacy 0
```

Example output
```
Run 0 in 0.66 ms. Solved: (1-0/1 ~ 0.2065<=1.0000<=1.0000)
Run 1 in 1.66 ms. Solved: (2-0/2 ~ 0.3424<=1.0000<=1.0000)
Run 2 in 0.56 ms. Solved: (3-0/3 ~ 0.4385<=1.0000<=1.0000)
Run 3 in 1.01 ms. Solved: (4-0/4 ~ 0.5101<=1.0000<=1.0000)
Run 4 in 5.70 ms. Unsolvable: (4-0/5 ~ 0.3755<=0.8000<=0.9638)
Run 5 in 0.14 ms. Unsolvable: (4-0/6 ~ 0.3000<=0.6667<=0.9032)
Run 6 in 17.40 ms. Unsolvable: (4-0/7 ~ 0.2505<=0.5714<=0.8418)
Run 7 in 0.65 ms. Unsolvable: (4-0/8 ~ 0.2152<=0.5000<=0.7848)
Run 8 in 0.24 ms. Unsolvable: (4-0/9 ~ 0.1888<=0.4444<=0.7334)
Run 9 in 1.24 ms. Solved: (5-0/10 ~ 0.2366<=0.5000<=0.7634)
Run 10 in 0.26 ms. Solved: (6-0/11 ~ 0.2801<=0.5455<=0.7873)
Run 11 in 0.84 ms. Solved: (7-0/12 ~ 0.3195<=0.5833<=0.8067)
Run 12 in 0.22 ms. Solved: (8-0/13 ~ 0.3552<=0.6154<=0.8229)
Run 13 in 4.27 ms. Solved: (9-0/14 ~ 0.3876<=0.6429<=0.8366)
Run 14 in 0.26 ms. Solved: (10-0/15 ~ 0.4171<=0.6667<=0.8482)
Run 15 in 0.69 ms. Solved: (11-0/16 ~ 0.4440<=0.6875<=0.8584)
Run 16 in 0.81 ms. Solved: (12-0/17 ~ 0.4687<=0.7059<=0.8672)
Run 17 in 0.26 ms. Solved: (13-0/18 ~ 0.4913<=0.7222<=0.8750)
Run 18 in 0.36 ms. Solved: (14-0/19 ~ 0.5121<=0.7368<=0.8819)
Run 19 in 0.22 ms. Solved: (15-0/20 ~ 0.5313<=0.7500<=0.8881)
Run 20 in 1.55 ms. Solved: (16-0/21 ~ 0.5491<=0.7619<=0.8937)
Run 21 in 0.25 ms. Solved: (17-0/22 ~ 0.5656<=0.7727<=0.8988)
Run 22 in 5055.55 ms. Terminated: (17-1/23 ~ 0.5353<=0.7391<=0.9034)
...
```

Each row correspond to a game
```
Run [game_seed] in [run_time] ms. [solve_result]: ([solvable]-[terminated]/[total] ~ [solvable_lb_95%]<=[solvable_rate]<=[solvable_ub_95%])
```

### Play

You can play out the game.
Due the optimizations, the available actions are quite unsual, and performing them may result in weird results
- One action can be equivalent to multiple actions combined in standard game
- The result of the action is impossible but it is equivalent to the possible result in the standard game.
- Missing some actions (should be inferior to the available actions)


```sh
lonelybot play [seed_type] [seed]
```

Example run
```sh
loneybot play legacy 0
```

Example output
```sh
loneybot rate legacy 0
```

```
{"tableau piles": [
["7D"],
["Kc","3C"],
["6s","8c","6H"],
["9s","Ah","5s","5C"],
["5d","Js","5h","Qd","10H"],
["Ac","7c","Jc","7h","Kd","9C"],
["10c","3h","4d","4h","6c","Qs","3S"]
],"stock": ["JD","10D","7S","10S","AD","8S","JH","2D","AS","3D","9D","9H","6D","KS","QH","2H","2S","4S","4C","KH","2C","8H","8D","QC"]}
0 Q♣ 1 8♦ 2 8♥ 3 2♣ 4 K♥ 5 4♣ 6 4♠ 7 2♠ 8 2♥ 9 Q♥ 10 K♠ 11 6♦ 12 9♥ 13 9♦ 14 3♦ 15 A♠ 16 2♦ 17 J♥ 18 8♠ 19 A♦ 20 10♠ 21 7♠ 22 10♦ 23 J♦
                1.   2.   3.   4.
5       6       7       8       9       10      11
7♦      **      **      **      **      **      **
        3♣      **      **      **      **      **
                6♥      **      **      **      **
                        5♣      **      **      **
                                10♥     **      **
                                        9♣      **
                                                3♠

0.R 5♣, 1.R 9♣, 2.DP 2♥, 3.DP 8♥,
Hash: 2642345984
Move:
```

You enter the move number to move:

There are currently 5 types of move:
- R ``card``: Revealing the hidden card about the ``card``
- SP ``card``: Moving the ``card`` from the foundation stack into the tableau (the pile in my term)
- DP ``card``: Moving the ``card`` from the stock (the deck in my term) to the tableau
- DS ``card``: Moving the ``card`` from the stock to the foundation stack
- PS ``card``: Moving the ``card`` from the tableau to the stack (potentially also do a reveal)

# To do
Custom game input without seed
Converting the compressed actions into standard actions