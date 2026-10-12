# Blind replication report

Fill in a copy of this file **before** you open `answer_key/`. Leave blank any target you did not do, and write "not
done". Then compute `sha256sum report.md`. Send the hash to the project, or post it, through any channel that records
the date (guide §0.1). Do not edit the file after that. Put any later remarks in a second file.

## 0. About the replication

| | |
|---|---|
| Replicator(s) | |
| Date(s) of the work | |
| Guide version used | 1.0 |
| SHA-256 of `answer_key/ANSWER_KEY.md` as printed at the end of the guide (copy it now; check it when you open the key) | |
| Did you read anything of the repository beyond the guide, GGHV v1 and the inputs the guide allows? If yes, what? | |
| Software and versions (CAS, libraries) | |
| Hardware (CPU, cores, memory) | |
| Total time spent (human / machine) | |
| Code available at (optional) | |

## 1. Common definitions (guide §1)

- Bracket convention used: [P,Q] = ____________
- Weight of x^A y^B: ____________
- Did you check the top-layer equation αβ + u(2αβ′ − 3α′β) = λ yourself? ____  How? ____________

## 2. Branches (a,b)

### R1. Lattice points
| Quantity | Your value |
|---|---|
| \|N(P) ∩ ℤ²\|, \|N(Q) ∩ ℤ²\| | |
| Unknowns of the top layer / depth 1 / depth 2 / depth 3 | |
| Unknowns that never occur in [P,Q], and why | |

### R2. Equations by weight
| Weight | 4 | 3 | 2 | 1 | 0 | −1 | other |
|---|---|---|---|---|---|---|---|
| Nonzero coefficients | | | | | | | |

Total: ____. Weights that do not occur, and why: ____________

### R3. Top layer
**R3a (chart α₀ = β₀ = α₇ = 1):**
- solutions over ℚ̄ with multiplicity: ____
- all simple? ____
- degree of the eliminant in α₆: ____
- polynomial in α₆⁷? ____
- V (paste, or attach as a file): ____________
- V irreducible? ____
- real roots of V: ____; of the eliminant: ____
- single Galois orbit? ____
- method, and whether exact over ℚ or modulo p (which p): ____________

**R3b (chart α₀ = β₀ = α₁ = 1, α₇ ≠ 0):**
- solutions: ____
- field polynomial (polredabs): ____________
- discriminant: ____
- signature: ____
- class number: ____
- Galois group: ____

**R3c (optional):** covers for m = 3 / 5 / 7: ____ / ____ / ____. Method: ____________

**R3d (optional):**
- m = 3: solutions ____, eliminant ____________
- m = 5: solutions ____, eliminant ____________

### R4. Linear layers at the top-layer point
Point used (your own R3b solution, or the guide's Appendix A): ____________

| Weight | Size | Rank | Kernel dim | Left-null dim |
|---|---|---|---|---|
| 3 | | | | |
| 2 | | | | |
| 1 | | | | |

Weight 2 consistent for every value of the depth-1 unknowns? ____  How checked? ____________

### R5. Weights 3, 2, 1
| Quantity | Your value |
|---|---|
| Number of generators | |
| dim V(I) | |
| b₁₂,₂₄ ∈ √I? b₁₂,₂₄ ∈ I? | |
| t₁ ∈ √I? t₂ ∈ √I? | |
| least k with t₁ᵏ ∈ I; with t₂ᵏ ∈ I | |
| I ∩ K[t₁,t₂]: Hilbert function of the quotient; degrees of minimal generators | |
| (optional) reduced GB degrees and leading monomials, with the monomial order | |
| (optional) degrees of b_i, M_i, L_i; rank of the 35 × 6 minor matrix | |

### R6. Weights 3, 2, 1, 0
| Quantity | Your value |
|---|---|
| Number of generators | |
| dim V(I′) | |
| every lower unknown in √I′? | |
| a₈,₁₆ ∈ I′? a₈,₁₆² ∈ I′? | |
| b₁₂,₂₄ ∈ I′? | |

## 3. Branch (c)

### C1. Lattice points and equations
- \|N(P) ∩ ℤ²\|, \|N(Q) ∩ ℤ²\|: ____
- equations by weight (attach the list): ____________
- total: ____; equations in weights 3 … −3: ____; lowest weight: ____

### C2a. Operators
| Weight | Equations | New unknowns | Rank | Equations without new unknowns |
|---|---|---|---|---|
| 3 | | | | |
| 2 | | | | |
| 1 | | | | |
| 0 | | | | |
| −1 | | | | |
| −2 | | | | |
| −3 | | | | |

### C2b. Conditions (optional, longer)
| Weight | Conditions contributed | Unknowns that stay free |
|---|---|---|
| 3 | | |
| 2 | | |
| 1 | | |
| 0 | | |
| −1 | | |
| −2 | | |
| −3 | | |

- Shape of the weight-0 condition: ____________
- κ (at your point): ____________
- κ · b₁₂,₂₁ (at your point): ____

### C2c. Unit ideals mod p (evidence)
- Primes and roots tried: ____________
- Unit ideal at ____ of ____ pairs. Pairs excluded as bad, and why: ____________

### C3. Rank computation
Route used: A (`conds_c.json`) / B (`CondsC.lean`) / own conditions: ____

| Quantity | p = 32003, w₀ = 11147 | p = 1000003, w₀ = 806739 |
|---|---|---|
| R(w₀) ≡ 0 mod p checked | | |
| o₂² = 4o₁o₃? κ mod p | | |
| Nonzero terms of the six F_n | | |
| Weighted degrees of the six F_n | | |
| F_n(1,2,3,4,5) mod p | | |
| M₂₄: rows × columns, nnz | | |
| W = 22: rank / rank of [M \| e₁] / rows | | |
| W = 23 | | |
| W = 24 | | |
| Planted-zero control: rank of M₂₄ | | |

- κ in K₅ (coefficients of 1, w, …, w⁴): ____________
- The lifting lemma: do you accept it? ____  Conditions checked (R irreducible, p-integrality): ____________

## 4. Optional: Lean rebuild
| Script | Exit code | Theorems on standard axioms | Warnings |
|---|---|---|---|
| | | | |

## 5. Anything else
Problems with the guide, ambiguities, disagreements you expect, comments:
