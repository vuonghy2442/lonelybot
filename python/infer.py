from engine import Solitaire
from network import LonelyBot, encode_game
import torch

target_net = torch.load("checkpoint.pth")

g = Solitaire(124)

total_reward = 0

for i in range(100):
    if g.is_won():
        break
    state = encode_game(g)
    move = target_net(state[0][None], state[1][None]).max(1).indices.item()
    g.display()
    print(move)
    input()
    valid, reward = g.move(move // 12, move % 12)
    total_reward += reward
    print(total_reward)
