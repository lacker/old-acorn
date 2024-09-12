from torch import nn, optim

import config


# Define the model
class SimpleNN(nn.Module):
    def __init__(self):
        super(SimpleNN, self).__init__()
        self.fc1 = nn.Linear(9, 32)  # 9 input features, 32 hidden units
        self.fc2 = nn.Linear(32, 16)  # 32 hidden units, 16 hidden units in second layer
        self.fc3 = nn.Linear(16, 1)  # 16 hidden units, 1 output unit
        self.relu = nn.ReLU()  # Activation function
        self.sigmoid = nn.Sigmoid()  # Sigmoid for binary classification

    def forward(self, x):
        x = self.relu(self.fc1(x))
        x = self.relu(self.fc2(x))
        x = self.sigmoid(self.fc3(x))
        return x


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
