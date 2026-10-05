# Colab a816 Lift Scripts (moved from repo root)

These scripts were previously at the repository root under `colab_run/`.
They have been moved here to integrate with the branch-(a,b) script hierarchy,
per the project convention against new top-level directories.

- `a816_colab_run.sh` — Colab execution wrapper for the exact lift
- `a816_full_lift.sing` — Singular script for the 76-cofactor lift over Q(w)
- `a816_lift_attempts_2026-10-04.ipynb` — archived Colab notebook of the attempts

Note: The exact lift via Colab timed out twice (2-hour limit). The successful
exact certificate was produced by Claude (Opus 5.5) via the layer-structured
method; see `../a816_certificate/` for the verified 76-line `a816_lift.txt`.

**What the notebook records (annotated 2026-10-05):**

- **Characteristic-0 run (cell 4).** The run over `(0,w)` reached `G[1]=1`. The run was then stopped at the 2-hour
  limit during `lift`, with `EXIT_CODE: 124`, and no lift was written.
- **Modular run (cells 8–10).** The same script was then run with the ring changed to `(32003,w)`.
  - **Output.** That run finished and wrote a 76×1 lift to a Colab-only file, also named `a816_lift.txt`
    (179,433 bytes). It is not in this repository.
  - **The quotient ring is not a field.** The minimal polynomial $R=w^5-w^4+3w^3+3w^2+26$ of $w$ factors mod 32003
    into irreducible factors of degrees $1,1,3$. So `F_32003[w]/(R)` is a product of three fields, and Singular does
    not check that a `minpoly` is irreducible.
  - **Status.** That file is a modular computation and not a certificate in characteristic 0.
  - **Use the exact certificate instead.** It is `../a816_certificate/a816_lift.txt`: 3464 terms, sha256
    `62bf975a042f9079ff9133da1cd009836ab3953c02cfd94f0a4b0b2c457d48cc`, checked by
    `../a816_certificate/verify_bundle.sh`.
