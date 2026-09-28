#!/bin/bash
# verify_branch_c.sh — verify Branch (c) scripts and fast Singular checks.
set -e
cd "$(dirname "$0")"
echo "=== Checksums ==="
sha256sum -c CHECKSUMS.sha256
echo "=== Prong 1 (t=0 slice) ==="
~/miniconda3/envs/cas/bin/Singular -q scripts/stage6d_prong1.sing < /dev/null
echo "=== Prong 2 (t1=1 patch, expect G[1]=1) ==="
~/miniconda3/envs/cas/bin/Singular -q scripts/stage6e_prong2_k0.sing < /dev/null
echo "=== ALL CHECKS DONE ==="
