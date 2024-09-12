import numpy as np
import torch
from torch.utils.data import DataLoader, TensorDataset

import config


def dataloader():
    """
    Create a DataLoader with all the data from one particular log file in it.
    """
    # Load the .npz file
    data = np.load("../data/dataset-2024-09-11-15:11:57.npz")

    # Access the "features" and "labels"
    features = data["features"]
    labels = data["labels"]

    # Display their shapes to verify
    print("Features shape:", features.shape)
    print("Labels shape:", labels.shape)
    positive = labels.sum()
    negative = (~labels).sum()
    print(f"{positive} positive examples, {negative} negative examples")

    features_tensor = torch.tensor(features, dtype=torch.float32).to(config.device)
    labels_tensor = torch.tensor(labels, dtype=torch.float32).to(config.device)

    nbytes = features_tensor.nbytes + labels_tensor.nbytes
    mib = nbytes / (2**20)
    print(f"data loaded with {mib:.1f} MiB")

    dataset = TensorDataset(features_tensor, labels_tensor)
    return DataLoader(dataset, batch_size=32, shuffle=True)
