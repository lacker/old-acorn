def one_pass(dataloader, model, criterion, optimizer=None):
    """
    Do a pass through all the data.
    Return the average loss.
    If optimizer is provided, we do a round of training.
    """
    if optimizer is None:
        model.eval()
    else:
        model.train()

    total_loss = 0
    total_samples = 0
    for inputs, labels in dataloader:
        # Forward pass
        outputs = model(inputs)
        loss = criterion(outputs, labels.unsqueeze(1))

        if optimizer is not None:
            # Backward pass
            optimizer.zero_grad()
            loss.backward()
            optimizer.step()

        # Track the loss
        total_loss += loss.item() * inputs.size(0)
        total_samples += inputs.size(0)

    return total_loss / total_samples
