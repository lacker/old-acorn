from datetime import datetime
import torch
from torch import nn, optim

import config


# Define the model
class SimpleNN(nn.Module):
    hidden1 = 16
    hidden2 = 16

    def __init__(self):
        super(SimpleNN, self).__init__()

        self.fc1 = nn.Linear(config.num_features, self.hidden1)
        self.fc2 = nn.Linear(self.hidden1, self.hidden2)
        self.fc3 = nn.Linear(self.hidden2, 1)
        self.relu = nn.ReLU()  # Activation function
        self.sigmoid = nn.Sigmoid()  # Sigmoid for binary classification

    def forward(self, x):
        x = self.relu(self.fc1(x))
        x = self.relu(self.fc2(x))
        x = self.sigmoid(self.fc3(x))
        return x

    def save(self):
        """
        Saves the model to a file chosen by timestamp.
        """
        timestamp = datetime.now().strftime("%Y-%m-%d-%H:%M:%S")
        path = f"../files/models/model-{timestamp}.onnx"

        # The dummy input has just a single feature vector
        dummy_input = torch.randn(1, config.num_features, device=config.device)
        dynamic_axes = {
            "input": {0: "batch_size"},
            "output": {0: "batch_size"},
        }
        torch.onnx.export(
            self,
            dummy_input,
            path,
            input_names=["input"],
            output_names=["output"],
            dynamic_axes=dynamic_axes,
        )
        print(f"Model saved to {path}")


def create():
    """
    Return model, criterion, optimizer.
    """
    # Create the model
    model = SimpleNN().to(config.device)
    total_params = sum(p.numel() for p in model.parameters())
    print(f"Total number of parameters: {total_params}")

    # Define loss function and optimizer
    criterion = nn.BCELoss()  # Binary Cross Entropy loss for binary classification
    optimizer = optim.AdamW(
        model.parameters(), lr=config.learning_rate, weight_decay=config.weight_decay
    )

    return model, criterion, optimizer
