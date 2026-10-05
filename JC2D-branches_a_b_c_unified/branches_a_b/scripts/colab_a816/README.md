# Colab a816 Lift Scripts (moved from repo root)

These scripts were previously at the repository root under `colab_run/`.
They have been moved here to integrate with the branch-(a,b) script hierarchy,
per the project convention against new top-level directories.

- `a816_colab_run.sh` — Colab execution wrapper for the exact lift
- `a816_full_lift.sing` — Singular script for the 76-cofactor lift over Q(w)

Note: The exact lift via Colab timed out twice (2-hour limit). The successful
exact certificate was produced by Claude (Opus 5.5) via the layer-structured
method; see `../a816_certificate/` for the verified 76-line `a816_lift.txt`.
