import torch

device = torch.device("cuda")

# Deterministic behavior
torch.manual_seed(42)
torch.backends.cudnn.deterministic = True
torch.backends.cudnn.benchmark = False

dataset_filename = "../files/datasets/dataset-2024-09-16-09:54:56.npz"

num_features = 9

# 1.5s per epoch, seems best so far
batch_size = 2048

# Andrej says "baby networks can afford to go a bit higher"
learning_rate = 1e-3

# On the higher end of what ChatGPT recommends because it's a small network
weight_decay = 1e-3
