from engine import Solitaire
import torch
from torch import nn, optim
from torch.nn import functional as F
import math
from collections import namedtuple, deque
import random
from itertools import count
import matplotlib
import matplotlib.pyplot as plt

is_ipython = "inline" in matplotlib.get_backend()
if is_ipython:
    from IPython import display
plt.ion()

Transition = namedtuple("Transition", ("state", "action", "next_state", "reward"))


class ReplayMemory(object):
    def __init__(self, capacity):
        self.memory = deque([], maxlen=capacity)

    def push(self, *args):
        """Save a transition"""
        self.memory.append(Transition(*args))

    def sample(self, batch_size):
        return random.sample(self.memory, batch_size)

    def __len__(self):
        return len(self.memory)


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
    draw_mask = torch.zeros((n_deck,), dtype=dtype)
    pos = game.cur_draw + game.cur_draw_step - 1
    if pos >= 0:
        draw_mask[pos] = 1

    final_stack = encode_cards(
        [(j - 1, i) for i, j in enumerate(game.final_stack[:4])], 4, dtype=dtype
    )

    n_hidden = torch.tensor([len(p) for p in game.hidden_piles], dtype=dtype)

    visible = torch.stack(
        [encode_cards(p, 13, dtype=dtype) for p in game.visible_piles]
    )

    valid_moves = torch.zeros((5 + game.n_piles) * (5 + game.n_piles), dtype=torch.bool)
    for move in game.gen_moves():
        valid_moves[move[0] * (5 + game.n_piles) + move[1]] = 1

    enc = {
        "deck": deck,
        "mask": draw_mask,
        "final": final_stack,
        "hidden": n_hidden,
        "visible": visible,
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
            n_deck * (CARD_DIM + 1) + 4 * CARD_DIM + n_piles + n_piles * 13 * CARD_DIM
        )
        self.output_dim = (1 + 4 + n_piles) * (1 + 4 + n_piles)

        self.net = nn.Sequential(
            nn.Linear(self.input_dim, 256),
            nn.Mish(True),
            nn.Linear(256, 256),
            nn.Mish(True),
            nn.Linear(256, self.output_dim),
        )

    def forward(self, x, y):
        policy = self.net(x)
        policy[~y] = -torch.inf
        return policy


# g = Solitaire(12)

# bot = LonelyBot()

# # sampling games
# with torch.no_grad():
#     enc, valid = encode_game(g)
#     enc = torch.concatenate([x.flatten() for x in enc.values()])[None,]
#     valid = valid[None]

#     policies = bot(enc)
#     policies[~valid.reshape(-1, 12*12)] = -torch.inf
#     move = torch.argmax(policies, dim=1)
#     m = move.detach().cpu().numpy()
#     g.move(m[0] // 12, m[0] % 12)


BATCH_SIZE = 128
GAMMA = 0.99
EPS_START = 0.9
EPS_END = 0.05
EPS_DECAY = 1000
TAU = 0.005
LR = 1e-4

device = "cuda:0"

# Get number of actions from gym action space
# Get the number of state observations
policy_net = LonelyBot().to(device)
target_net = LonelyBot().to(device)

optimizer = optim.AdamW(policy_net.parameters(), lr=LR, amsgrad=True)
memory = ReplayMemory(10000)


steps_done = 0


def select_action(env: Solitaire):
    global steps_done
    sample = random.random()
    eps_threshold = EPS_END + (EPS_START - EPS_END) * math.exp(
        -1.0 * steps_done / EPS_DECAY
    )
    steps_done += 1
    with torch.no_grad():
        if sample > eps_threshold:
            # t.max(1) will return the largest column value of each row.
            # second column on max result is index of where max element was
            # found, so we pick action with the larger expected reward.
            state = encode_game(env, device=device)
            policies = policy_net(state[0][None], state[1][None])
            # policies[~valid.view(1, -1)] = -torch.inf
            return policies.max(1).indices.view(1, 1)
        else:
            move = random.choice(list(env.gen_moves()))
            return torch.tensor(
                [[move[0] * (5 + env.n_piles) + move[1]]],
                device=device,
                dtype=torch.long,
            )


episode_durations = []


def optimize_model():
    if len(memory) < BATCH_SIZE:
        return
    transitions = memory.sample(BATCH_SIZE)
    # Transpose the batch (see https://stackoverflow.com/a/19343/3343043 for
    # detailed explanation). This converts batch-array of Transitions
    # to Transition of batch-arrays.
    batch = Transition(*zip(*transitions))

    # Compute a mask of non-final states and concatenate the batch elements
    # (a final state would've been the one after which simulation ended)
    non_final_mask = torch.tensor(
        tuple(map(lambda s: s is not None, batch.next_state)),
        device=device,
        dtype=torch.bool,
    )
    non_final_next_states = torch.cat([s[0] for s in batch.next_state if s is not None])
    non_final_next_valids = torch.cat([s[1] for s in batch.next_state if s is not None])
    state_batch = torch.cat([s[0] for s in batch.state])
    valid_batch = torch.cat([s[1] for s in batch.state])
    action_batch = torch.cat(batch.action)
    reward_batch = torch.cat(batch.reward)

    # Compute Q(s_t, a) - the model computes Q(s_t), then we select the
    # columns of actions taken. These are the actions which would've been taken
    # for each batch state according to policy_net
    state_action_values = policy_net(state_batch, valid_batch).gather(1, action_batch)

    # Compute V(s_{t+1}) for all next states.
    # Expected values of actions for non_final_next_states are computed based
    # on the "older" target_net; selecting their best reward with max(1).values
    # This is merged based on the mask, such that we'll have either the expected
    # state value or 0 in case the state was final.
    next_state_values = torch.zeros(BATCH_SIZE, device=device)
    with torch.no_grad():
        next_state_values[non_final_mask] = (
            target_net(non_final_next_states, non_final_next_valids).max(1).values
        )
    # Compute the expected Q values
    expected_state_action_values = (next_state_values * GAMMA) + reward_batch

    # Compute Huber loss
    criterion = nn.SmoothL1Loss()
    loss = criterion(state_action_values, expected_state_action_values.unsqueeze(1))

    # Optimize the model
    optimizer.zero_grad()
    loss.backward()
    # In-place gradient clipping
    torch.nn.utils.clip_grad_value_(policy_net.parameters(), 100)
    optimizer.step()


def plot_durations(show_result=False):
    plt.figure(1)
    durations_t = torch.tensor(episode_durations, dtype=torch.float)
    if show_result:
        plt.title("Result")
    else:
        plt.clf()
        plt.title("Training...")
    plt.xlabel("Episode")
    plt.ylabel("Duration")
    plt.plot(durations_t.numpy())
    # Take 100 episode averages and plot them too
    if len(durations_t) >= 100:
        means = durations_t.unfold(0, 100, 1).mean(1).view(-1)
        means = torch.cat((torch.zeros(99), means))
        plt.plot(means.numpy())

    plt.pause(0.001)  # pause a bit so that plots are updated
    if is_ipython:
        if not show_result:
            display.display(plt.gcf())
            display.clear_output(wait=True)
        else:
            display.display(plt.gcf())


if torch.cuda.is_available():
    num_episodes = 600
else:
    num_episodes = 50

for i_episode in range(num_episodes):
    # Initialize the environment and get it's state
    env = Solitaire(i_episode + 123)
    state = encode_game(env)

    total_reward = 0

    n_pos = 5 + env.n_piles
    for t in count():
        action = select_action(env)

        val = action.item()
        valid, reward = env.move(val // n_pos, val % n_pos)
        reward = reward if valid else -1

        # observation, reward, terminated, truncated, _ = env.step(action.item())
        total_reward += reward
        reward = torch.tensor([reward], device=device)
        terminated = env.is_won()

        done = terminated or t > 100

        if terminated:
            next_state = None
        else:
            next_state = encode_game(env)

        # Store the transition in memory
        memory.push(
            (state[0].unsqueeze(0), state[1].unsqueeze(0)),
            action,
            (next_state[0].unsqueeze(0), next_state[1].unsqueeze(0)),
            reward,
        )

        # Move to the next state
        state = next_state

        # Perform one step of the optimization (on the policy network)
        optimize_model()

        # Soft update of the target network's weights
        # θ′ ← τ θ + (1 −τ )θ′
        target_net_state_dict = target_net.state_dict()
        policy_net_state_dict = policy_net.state_dict()
        for key in policy_net_state_dict:
            target_net_state_dict[key] = policy_net_state_dict[
                key
            ] * TAU + target_net_state_dict[key] * (1 - TAU)
        target_net.load_state_dict(target_net_state_dict)

        if done:
            episode_durations.append(total_reward)
            plot_durations()
            break

print("Complete")
plot_durations(show_result=True)
plt.ioff()
plt.show()
