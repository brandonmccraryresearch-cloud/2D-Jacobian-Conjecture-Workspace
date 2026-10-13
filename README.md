# 2D Jacobian Conjecture Workspace

Research workspace for the two-dimensional Jacobian conjecture, organized around
the elimination of the surviving degree-$(72,108)$ candidate configurations of
Guccione–Guccione–Horruitiner–Valqui (GGHV) Proposition 4.3, case (1), plus a
claimed theorem on dicritical divisors of Keller maps (false as worded, and its proof is incomplete; see below)
and an independent blind
verification of GGHV Proposition 4.3, normal form (2).

**Author:** Brandon D. McCrary (ORCID: 0009-0008-2804-7165)

## Scope

GGHV Proposition 4.3 (case (1)) lists the surviving configurations for a
counterexample pair to the planar Jacobian conjecture at degree pair
$(72,108)$. In this repository's formalization they are organized as
**branches**:

| Branch | GGHV normal form | Case | Status |
|---|---|---|---|
| (a), (b) | form (2) | degree-$(8,28)$ | **Eliminated** — Lean 4 `main_theorem`, no remaining hypothesis |
| (c) | form (1) | degree-$(72,108)$ | **Closed under stated computational premises** — Lean proves the descent chain; the chart-emptiness premise is proved outside Lean (grade B) |

All branches work over $K_5 = \mathbb{Q}[w]/(R)$ with
$R(w) = w^5 - w^4 + 3w^3 + 3w^2 + 26$ irreducible over $\mathbb{Q}$ (it is irreducible mod 67 and mod 109;
irreducibility over $\mathbb{Q}$ is kernel-checked since 2026-10-12, `branch_c/grade_a/`).
The Jacobian condition is $[P,Q] = \lambda x^2$ with $\lambda \neq 0$.

**What this is not.** This workspace eliminates one case (case (1)) of one
proposition (GGHV Prop. 4.3). It is not a proof of the two-dimensional Jacobian
conjecture: GGHV Proposition 4.3's other cases and the reduction from the
conjecture to Prop. 4.3 are outside scope.

## Repository layout

| Path | Contents |
|---|---|
| `JC2D-branches_a_b_c_unified/` | The unified branch-elimination workspace (branches (a), (b), (c)) |
| `JC2D-branches_a_b_c_unified/branches_a_b/` | Branch (a),(b) elimination package (v19, revised 2026-10-05 to 2026-10-07). Contents: a 34-page paper, a Lean 4 machine-checked $m=7$ chart classification (Prop. 6.1), Lean $m=3,5$ classifications, the Lean proof of Corollary 1.2 ($a_{8,16}=0$, lower-edge rigidity), four certificates, the explicit $a_{8,16}$ certificate, audits, logs, `verify_v19.sh`. Published on Zenodo: 10.5281/zenodo.23023490 |
| `branch_ab_v19/` | Byte-identical copy of `JC2D-branches_a_b_c_unified/branches_a_b/`, at the path cited by the Zenodo record. The two copies are updated together. |
| `JC2D-branches_a_b_c_unified/branch_c/` | Branch (c) elimination package: v3.1 bundle (byte-for-byte reviewer bundle) with Lean 4 symbolic elimination (`Descent2R`, `T1Zero`, `Bridge`, `Combine`) + numerical elimination (exact/modular certificates, Macaulay rank lemma at two primes), 18-page paper, `verify_branch_c.sh` |
| `JC2D-branches_a_b_c_unified/TECHNICAL_MAP.md` | Exhaustive technical map: the mathematics, every component, the symbolic and numerical eliminations branch by branch, the trust base, and how to reproduce everything |
| `JC2D-branches_a_b_c_unified/TODO_correspondence_guide.md` | The original to-do for the branch-(c) correspondence guide: done 2026-10-07 (`branch_c/correspondence_guide/`), corrected 2026-10-12 |
| `JC2D-branches_a_b_c_unified/replication/` | Blind replication guide for an outside party, with a separate answer key recomputed in fresh code (2026-10-12) |
| `JC2D-branches_a_b_c_unified/reviews/` | Reviews of the work, with their evidence (the review of 2026-10-12 covers PRs #12–#15 and the A1–A5 and two-dicritical drafts) |
| `REPRODUCTION_GUIDE.md`, `REPRODUCTION_ANSWER_KEY.md`, `reproduction_key_checks.py` | Protocol for re-running the project's own scripts on another machine (reproducibility, I1), with its answer key and comparator |
| `branch_two_dicritical/` | **Claimed** theorem: no Keller map admits two dicritical divisors. As worded the statement is false, and the proof is incomplete (see the status section below). 6-page paper, 18 executed SymPy scripts with outputs, `verify_all.sh`, `CORRESPONDENCE.md` mapping each script to its paper statement |
| `tier1_blind_gghv43_nf2/` | Independent blind verification of GGHV Proposition 4.3, normal form (2): verdict DO NOT EXIST (run 2026-09-25, logged in `LOG.md`) |
| `environment.yml`, `lean.toml`, `setup.sh` | Compute environment setup (conda environment, Lean 4 toolchain) |

## Status of each line of work

### Branches (a), (b) — eliminated

For polynomials $P, Q \in L[x,y]$ over a field $L$ of characteristic $0$ in GGHV
normal form (2) with $[P,Q] = \lambda x^2$, $\lambda \neq 0$, there is **no
solution**. The Lean 4 formalization proves, independently of GGHV Proposition
4.3:

- `chartClassification_holds`: every solution of the 17-equation normalized
  chart is one of the five $K_5$-conjugate points ($m=7$ case of Prop. 6.1),
  kernel-checked on the standard axioms only.
- `main_theorem`: the NewtonNF2 form of Theorem 1.1 with no remaining
  hypothesis, kernel-checked on the standard axioms only.

Conditional on GGHV Proposition 4.3, this eliminates branches (a),(b). The
paper went through an independent final blind review (2026-09-28, no fatal
flaw found) and was published on Zenodo as v19 (10.5281/zenodo.23023490).

### Branch (c) — closed under stated computational premises

In Lean 4 (no `sorry`, only `propext`, `Classical.choice`, `Quot.sound`):

$$\text{ChartEmptyC\_T1ne0} \to \text{ChartEmptyC} \to \text{DescentClaimC} \to \neg\exists\, P\, Q\, \lambda,\ \lambda \neq 0 \wedge \text{NewtonNFc}\, P\, Q \wedge [P,Q] = \lambda x^2.$$

The stratum $b_{11,20} = 0$ is kernel-checked (`T1Zero`); `Combine` isolates
exactly what Lean does not check. Outside Lean (grade B): `ChartEmptyC` follows
from the fixed-degree Macaulay rank lemma plus full row rank of the Macaulay
matrix at two primes ($p = 1000003$ and $p = 32003$), with two independent
implementations and planted-zero controls. The 18-page paper
(`branch_c/paper/branch_c_elimination.pdf`) carries the full account and four finished figures. Its §6
paragraph "Formalization seam" (degree-19 rigidity not in Lean) is out of date: `degree19_rigidity`,
`vertex_12_24_forces_t2` and the branch-(a,b) classification are kernel-checked and used by
`main_theorem_c_of_claim` (`branch_c/correspondence_guide/CORRESPONDENCE_GUIDE.md`, §6).

Since 2026-10-12, `branch_c/grade_a/` proves the generic half of `ChartEmptyC_T1ne0` in Lean: $R$ is irreducible
over $\mathbb{Q}$; a polynomial in $\mathbb{Z}[X]$ that vanishes at a root of $R$ in characteristic $0$ vanishes at
every root of $R$ in every ring; and a modular left inverse of a Macaulay block at one prime excludes common zeros in
characteristic $0$ (`no_common_zero_of_certificate`). The chart reduction is kernel-checked too: a chart point is a
common zero of the six chart generators, with $b_{11,20}$ free (`chart_gens_vanish`). The interface theorem
`chartEmptyC_T1ne0_of_certificate` then gives the premise from the Macaulay data (rows, pivot columns, support) and
two finite deliverables: A1, the packed kernel check read as $C\cdot M_S = I$ modulo 32003; and A2, $M_S$ is the
evaluated Macaulay block of the generators, up to one nonzero scale per generator. Until those are supplied, the
premise stays grade B (`branch_c/grade_a/README.md`).

### Two dicritical divisors — claimed; false as worded, and the proof is incomplete

The claim: let $K$ be a field of characteristic $0$ and $P, Q \in K[x,y]$ with
$[P,Q] = c \in K^\times$ (a Keller map). Then the resolution of the pencil
$\lambda P + \mu Q$ contains no two distinct dicritical divisors. The proposed proof:
$m \geq 2$ is impossible (constant-leading-form on $E_k$, $k \geq 2$; $E_1$
degree obstruction), and the $m = 1$ bridge is empty for every $d \geq 2$
(descending induction on $W = 2J+K$; diagonal blocks reduce to scaled
Vandermonde, full rank; nullspace $= \mathrm{span}\{1,y\}$, $J = 0$).

Status (review of 2026-10-12, corrected 2026-10-13; `JC2D-branches_a_b_c_unified/reviews/REVIEW_2026-10-12_handoff.md`
§5 and §9, and `branch_two_dicritical/lean/README.md`):
- **as worded, the statement is false for every Keller map of degree $\geq 2$.** Its pencil has a base point at
  infinity and, once the target is translated so that $0$ is a value, an affine one; every base point carries a
  dicritical (`JC2D-branches_a_b_c_unified/reviews/two_dicritical/base_point_at_infinity_check.py`;
  `main_statement_check.py` there works out $(x-y^2,\ y)$ and $(x,\ y+x^2)$). Read literally, the statement would
  imply the Jacobian conjecture outright, and every non-affine automorphism refutes it. The intended statement
  (presumably about dicriticals at infinity) has to be written down;
- **Theorem `thm:e1` (the $E_1$ obstruction) is false as stated.** Its proof reads $\nu_{E_1}\geq -2$ as "total
  degree $\geq 2$" instead of "$x$-degree $\leq 2$", and $P=(x+y^2)^2+y$, $Q=P+x+y^2$ is a Keller pair in its open
  subset. The intended conclusion holds for every $m$: $E_1$ is never dicritical for a Keller map. Its algebraic step
  is now proved in Lean (`E1Keller.lean`); the chart step is executed only;
- the adjacent $m = 1$ case is computed at $d = 3$ only, while the theorem is stated for every degree;
- the constant-leading-form proposition, which carries $m \geq 2$, has a proof sketch only;
- the Lean drafts of 2026-10-12 rested their bridge induction on two axioms that are false as stated. Since
  2026-10-12, `branch_two_dicritical/lean/` proves the bridge collapse from the paper's explicit equations with no
  axioms, together with the block-rank lemma. That proof also closes a gap at weight $W = 2$. Read geometrically, the
  bridge assumes two dicriticals over **free** points of the second exceptional curve $E_2$, with pole order at most
  1 for every member of the pencil. The second premise is asserted, not derived. Under these premises one such
  dicritical already forces degree $\leq 2$. Dicriticals over the satellite points of $E_2$ are not treated. The
  hypothesis "both centers nonzero" marks where the formula applies: the formal witness $(x-a_4y^2,\ y)$ with a center
  at $a = 0$ is not a geometric bridge (`branch_two_dicritical/lean/check_satellite.py`).

So the theorem is open, and its statement must first be corrected.

## Papers

All papers are typeset with Fira Sans (text), Fira Mono (code), and Fira Math
(mathematics) exclusively.

| Paper | Location | Pages |
|---|---|---|
| Branch (a),(b) elimination (v19, revised 2026-10-05 to 2026-10-07) | `JC2D-branches_a_b_c_unified/branches_a_b/paper/branch_ab_elimination_v3.pdf` (same file in `branch_ab_v19/paper/`) | 34 |
| Branch (c) elimination | `JC2D-branches_a_b_c_unified/branch_c/paper/branch_c_elimination.pdf` | 18 |
| No Keller map admits two dicritical divisors | `branch_two_dicritical/paper/two_dicritical_closure.pdf` | 6 |

## Reproducibility

Each package ships its own verification entry point:

```bash
# Branch (a),(b) (or branch_ab_v19/verify_v19.sh, the identical copy)
JC2D-branches_a_b_c_unified/branches_a_b/verify_v19.sh

# Branch (c)
JC2D-branches_a_b_c_unified/branch_c/verify_branch_c.sh

# Two dicritical divisors
branch_two_dicritical/verify_all.sh
```

Checksums (`CHECKSUMS.md5`, `CHECKSUMS.sha256`) and build records
(`BUILD_STATUS.md`) are kept in each package directory.

## Note on removed directories

The legacy top-level `branch_ab/` and `branch_c/` directories were removed;
their contents are superseded by `JC2D-branches_a_b_c_unified/branches_a_b/`
and `JC2D-branches_a_b_c_unified/branch_c/` respectively.

`branch_ab_v19/` was restored at the root on 2026-10-03 because the Zenodo
record cites that path. It is kept byte-identical to
`JC2D-branches_a_b_c_unified/branches_a_b/`; the last sync was 2026-10-05.
To check that the two copies agree, run
`diff -r -x __pycache__ -x .lake branch_ab_v19 JC2D-branches_a_b_c_unified/branches_a_b`.
