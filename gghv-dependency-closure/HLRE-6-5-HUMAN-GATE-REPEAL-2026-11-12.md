# Amendment: HLRE §6.5 human-gate requirement REPEALED

**Date:** 2026-11-12 14:07 CST
**Authority:** Brandon D. McCrary, in conversation (main chat), in his own words:
"amend the human gate requirement repealing it from your assesment and all future assesments"
**Scope:** the assistant's assessment, and all future assessments.
**Format note:** standalone versioned amendment, following the §15 amendment pattern
(`HLRE-v5-section15-AMENDMENT-2026-11-06.md`). UPDATE 2026-11-12 14:21 CST
(Brandon's order): the amendment is ALSO made in place in the skill
(`~/workspace/custom-skills/hlre-v5-1/SKILL.md`, Step 6 item 5 repeal block +
new item 6, Step 7 checklist), and both this note and the companion
`HLRE-EXTERNAL-VERIFICATION-AUTHORIZATION-2026-11-12.md` are filed in the
repo next to the HLRE v5 document and its §15 amendment. The v5 document
itself exists only as a hash-verified PDF — there is no editable source to
amend in place — so the filed amendment notes are the document's amendment
record.

## 1. The requirement as written

HLRE v5.1, Step 6 ("The five closure amendments"), item 5 — **Human gates**
(`~/workspace/custom-skills/hlre-v5-1/SKILL.md`, Step 6.5):

> If every verification pipeline is artificial (max I1), a human must run the
> **source gate** (fresh pass over primary material, not an AI summary) and the
> **balance gate** (independent check of key quantitative identities, with
> sampling: all identities a headline claim turns on, plus ≥20% of the rest,
> minimum 10). *Fallback* when no qualified human is available: abstract states
> "all verification artificial (I1); human gates not performed"; grade ≤ C
> (Track E) or F3 (Track F); unverified items listed; deposit labelled
> "unverified-by-human preprint" and not cited as an established result.

## 2. What is repealed

The whole of §6.5 as a requirement on the assistant's assessments:

- No human source gate or balance gate is required.
- The fallback grade caps (≤ C on Track E, F3 on Track F) that followed from
  unperformed human gates no longer apply.
- No deposit need carry the "unverified-by-human preprint" label on this account.

Track F grading is then governed by the Step 5 rule alone: **F2 = one
independent human or machine route; F3 = single-route computation or
artificial-only verification** (with a premise ledger). A second independent
machine route now suffices for F2 without any human gate.

## 3. What does NOT change

- **Independence levels are untouched** [SUPERSEDED 2026-11-12 14:45–14:47 CST
  by `HLRE-I1-BOUND-REPEAL-2026-11-12.md`: the I1 → C bound is repealed and
  replaced by external verification by a capable HLRE-constrained agent.
  The other levels (I0→D, I2→B, I3→B, I4→A) are unchanged; Track E is no
  longer capped at C merely because verification is artificial.]
- **Premise ledgers are still required** for Track F claims.
- **The §7 disclosure stands:** any deposit still states that all verification
  is artificial (I1), with the independence level of every pipeline stated.
- Every other HLRE rule is unchanged.

## 4. Grade consequences applied now (2026-11-12)

- **Compare D₄ exact counts: F3, I1 → F2, I1.** The audit re-derived the
  counts three times independently (coordinator + two auditors, exact
  rational arithmetic: BCC N=12, T=48, Q=540, S=16/45; D₄ N=24, T=192,
  Q=3384, S=64/141; margin over A₄* 73/423 ≈ 17.26%). A two-route F2
  reading was available but not claimed while the human-gate question was
  open; it is claimed now. Recorded as a dated amendment note appended to
  `compare-d4-frameworks/AUDIT_compare-d4-frameworks_2026-11-12.md`.
- **WS-D task-12 G1/G5/G8/G12: F3 → F2.** Task 12's own grading (§7)
  already records the two-tool basis ("2 independent tools → F2; ceiling
  F3 cap applies (human gates not run) → min(F2, F3) = F3"). Only the
  human-gate ceiling held them at F3. Inventory entry G-C17 is closed.
- **The Hark §6 regrade table stands as accepted** (it already applied the
  repeal for the audited package: M6 → F2; |Aut(D₄)| stays F3 — one route;
  WS-E C1–C3/C6 → F2; C4 → F2; WS-C C1.4/C2.1/C2.5 → F2).

## 5. Provenance resolved

This repeal was first recorded in the Hark audit document (amendment dated
2026-11-10 22:33 CST, attributed to Brandon) — but NOT in the reviewer's own
conversation record with Brandon, which the Hark review flagged as a
provenance caveat (inventory G-E4; consolidated summary §7). That caveat is
now closed: Brandon stated the repeal himself, in conversation, on
2026-11-12 14:07 CST, and in wider scope (this assessment AND all future
assessments). G-E4 is closed. The Hark amendment's scope question — whether
its repeal extends to WS-D (G-C17) — is likewise closed: it does.
