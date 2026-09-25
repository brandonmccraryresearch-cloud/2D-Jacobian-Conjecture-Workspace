#!/bin/bash
# Setup script for 2D Jacobian Conjecture Workspace

echo "Setting up 2D Jacobian Conjecture Workspace..."
echo "=============================================="

# Step 1: Update Anaconda
echo ""
echo "Step 1: Updating Anaconda..."
conda update -n base -c defaults conda

# Step 2: Create/update the conda environment
echo ""
echo "Step 2: Creating/updating conda environment..."
conda env create -f environment.yml --force

# Step 3: Activate the environment
echo ""
echo "Step 3: Activating conda environment..."
conda activate jacobian-conjecture-2d

# Step 4: Update Lean 4 via elan
echo ""
echo "Step 4: Installing/updating Lean 4..."
elan self update
elan update

# Step 5: Initialize Lake project
echo ""
echo "Step 5: Initializing Lake project dependencies..."
lake update

# Step 6: Build Lean project
echo ""
echo "Step 6: Building Lean project..."
lake build

echo ""
echo "=============================================="
echo "Setup complete!"
echo "To activate the environment, run: conda activate jacobian-conjecture-2d"
echo "=============================================="
