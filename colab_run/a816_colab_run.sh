#!/bin/bash
# ============================================================================
# a816_colab_run.sh — Automated exact a_{8,16} Gröbner lift on Google Colab Pro
# ============================================================================
# Runs the full 75-generator Rabinowitsch lift over Q(w) via Singular,
# writing all output to Google Drive (survives runtime restarts).
#
# Usage (in Colab terminal):
#   wget -q https://raw.githubusercontent.com/brandonmccraryresearch-cloud/2D-Jacobian-Conjecture-Workspace/main/colab_run/a816_colab_run.sh
#   chmod +x a816_colab_run.sh
#   ./a816_colab_run.sh
#
# Output:
#   /content/drive/MyDrive/a816_colab_run/a816_lift.txt      (76 cofactors)
#   /content/drive/MyDrive/a816_colab_run/a816_generators.txt (75 generators)
#   /content/drive/MyDrive/a816_colab_run/singular_output.log (full log)
# ============================================================================

set -e  # Exit on error

# --- Config ---
DRIVE_DIR="/content/drive/MyDrive/a816_colab_run"
SING_URL="https://raw.githubusercontent.com/brandonmccraryresearch-cloud/2D-Jacobian-Conjecture-Workspace/main/colab_run/a816_full_lift.sing"
TIMEOUT_SEC=7200  # 2 hours max for the lift

echo "============================================================"
echo " a816 Colab Pro Lift — $(date)"
echo "============================================================"

# --- Cell 1: Mount Google Drive ---
echo ""
echo "[1/5] Mounting Google Drive..."
if [ ! -d "/content/drive/MyDrive" ]; then
    python3 -c "from google.colab import drive; drive.mount('/content/drive')"
else
    echo "  Drive already mounted."
fi
mkdir -p "$DRIVE_DIR"
echo "  Working directory: $DRIVE_DIR"

# --- Cell 2: Download the Singular script ---
echo ""
echo "[2/5] Downloading a816_full_lift.sing..."
cd "$DRIVE_DIR"
wget -q "$SING_URL" -O a816_full_lift.sing
ls -lh a816_full_lift.sing
echo "  Downloaded."

# --- Cell 3: Install Singular ---
echo ""
echo "[3/5] Installing Singular..."
if ! command -v Singular &> /dev/null; then
    echo "  Running apt-get (takes several minutes)..."
    apt-get update -qq > /dev/null 2>&1
    apt-get install -y -qq singular > /dev/null 2>&1
    echo "  Installed."
else
    echo "  Singular already installed."
fi
Singular --version 2>&1 | head -2

# --- Cell 4: Run the lift ---
echo ""
echo "[4/5] Running the exact Q(w) lift..."
echo "  Timeout: ${TIMEOUT_SEC}s. Output -> singular_output.log"
echo "  This is the long step. Monitoring..."
cd "$DRIVE_DIR"

# Run in background with nohup so it survives terminal disconnect
nohup bash -c "timeout $TIMEOUT_SEC Singular -q a816_full_lift.sing < /dev/null > singular_output.log 2>&1; echo \"EXIT_CODE: \$?\" >> singular_output.log" > /dev/null 2>&1 &
LIFT_PID=$!
echo "  Lift started (PID $LIFT_PID). Tailing log..."

# Tail the log until the process finishes or timeout
# We check every 30s; tail -f would block, so we poll
while kill -0 $LIFT_PID 2>/dev/null; do
    sleep 30
    # Show last line as progress
    LAST=$(tail -1 singular_output.log 2>/dev/null || echo "...")
    echo "  [$(date +%H:%M:%S)] still running. Last log line: $LAST"
done

echo ""
echo "  Lift process finished. Checking output..."

# --- Cell 5: Verify ---
echo ""
echo "[5/5] Verifying output..."
echo "------------------------------------------------------------"
ls -lh "$DRIVE_DIR/"
echo "------------------------------------------------------------"

if [ -f "$DRIVE_DIR/a816_lift.txt" ]; then
    LINES=$(wc -l < "$DRIVE_DIR/a816_lift.txt")
    echo "  a816_lift.txt: $LINES lines"
    if [ "$LINES" -eq 76 ]; then
        echo "  ✓ SUCCESS: 76 cofactors (exact Q(w) lift complete)"
    else
        echo "  ✗ FAIL: expected 76 lines, got $LINES"
    fi
else
    echo "  ✗ FAIL: a816_lift.txt not found"
fi

if [ -f "$DRIVE_DIR/a816_generators.txt" ]; then
    GLINES=$(wc -l < "$DRIVE_DIR/a816_generators.txt")
    echo "  a816_generators.txt: $GLINES lines"
fi

echo ""
echo "  Tail of singular_output.log:"
tail -8 "$DRIVE_DIR/singular_output.log"
echo ""
echo "============================================================"
echo " Done. Files in: $DRIVE_DIR"
echo "============================================================"
