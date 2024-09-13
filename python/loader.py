import numpy as np
import torch
from torch.utils.data import DataLoader, TensorDataset

import config


def dataloaders():
    """
    Create two DataLoaders from a file, one train and one validation.
    """
    # Load the .npz file
    data = np.load(config.dataset_filename)

    # Access the "features" and "labels"
    features = data["features"]
    assert (
        features.shape[1] == config.num_features
    ), f"Expected {config.num_features} features, got {features.shape[1]}"
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

    # Split into train and val
    num_datapoints = len(features)
    indices = torch.randperm(num_datapoints)
    train_size = int(num_datapoints * 0.9)
    train_indices = indices[:train_size]
    val_indices = indices[train_size:]
    train_features = features_tensor[train_indices]
    train_labels = labels_tensor[train_indices]
    val_features = features_tensor[val_indices]
    val_labels = labels_tensor[val_indices]

    train_dataset = TensorDataset(train_features, train_labels)
    train_loader = DataLoader(train_dataset, batch_size=config.batch_size, shuffle=True)

    val_dataset = TensorDataset(val_features, val_labels)
    val_loader = DataLoader(val_dataset, batch_size=config.batch_size, shuffle=False)

    return train_loader, val_loader
