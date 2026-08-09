# Phase 1 baseline record

## Sorry/suppression census (per-file, `scripts/check-sorry-suppressions.sh --list --scope ...`)

Format: `markers sorries file`

```
0 2 Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean
0 1 Cslib/Logics/Propositional/Tableau/Intuitionistic/Completeness.lean
0 1 Cslib/Logics/Propositional/Tableau/Minimal/Completeness.lean
```

Whole-tree gate (`scripts/check-sorry-suppressions.sh`, no args): `markers: 18 (baseline ceiling
18); sorries: 27 (baseline ceiling 28)` — OK, matches baseline.

## Over-100-column census (`awk 'length($0)>100'`)

All three files: 0 lines over 100 columns.

## Hunk inventory confirmation

Grepped the three files for
`PERMANENTLY DEFERRED|unprovable as stated|REFUTED|refuted|DISPOSITION UNDECIDED|terminal deferral|UNVERIFIED|no follow-up`.

The plan's 10 named hunks (H1-H10) account for every `DISPOSITION UNDECIDED`, `PERMANENTLY
DEFERRED`, `unprovable as stated`, `terminal deferral`, `no follow-up`, and `UNVERIFIED` hit, plus
the `refuted`/`REFUTED` hits that fall inside those same hunk line ranges (confirmed by exact line
number below). Additional bare `refuted`/`REFUTED` hits in `Scheme.lean` at lines 1939, 2088,
2454, 2547, 2550, 2557, 2565, 2752, 3143, 3623, 4252, 4269, 6797 are OUTSIDE the 10 hunks — they
describe genuine, unrelated refutations elsewhere in the file (e.g. other counterexamples) and are
NOT edited by this task; the plan's `file_scope` covers the file but not every occurrence of the
word "refuted" in it.

Hunk line confirmation (pre-edit):
- H1/H2 `Scheme.lean` 7844, 7845, 7849 (docstring) / 7928, 7933 (proof-site) — matches plan's
  7844-7858 / 7928-7939 ranges.
- H3 `Scheme.lean` 744, 746 — matches plan's 744-760 range.
- H4 `Scheme.lean` 585 — matches plan's 583-585 range (line 569's `refuted` is the unrelated
  fuel-sufficiency historical note, not part of H4).
- H5 `Intuitionistic/Completeness.lean` 46, 55 — matches plan's 46-57 range.
- H6 `Intuitionistic/Completeness.lean` 140, 143, 146, 148 — matches plan's 139-149 range.
- H7 `Intuitionistic/Completeness.lean` 154, 157, 158, 160 — matches plan's 154-160 range.
- H8 `Minimal/Completeness.lean` 50 — matches plan's 50-60 range.
- H9 `Minimal/Completeness.lean` 136, 137, 140, 143 — matches plan's 136-143 range.
- H10 `Minimal/Completeness.lean` 148, 153, 154 — matches plan's 148-154 range.

**Verdict: exactly 10 hunks confirmed, matching the plan's Scope Hypothesis. No inventory
correction needed.**

## Sorry count and position sanity

Four `sorry`s total, matching plan's expectation:
- `Scheme.lean` — 2 (`openBranch_countermodel`'s conjunct-1 `sorry` at the end of the proof
  [line ~761 pre-edit region H3], and the DP-3/DP-4-feeding proof `sorry` at end of
  `openBranch_countermodel` body [line ~7940 pre-edit region H2]).
- `Intuitionistic/Completeness.lean` — 1 (DP-3, end of `intuitionisticTableau_complete`).
- `Minimal/Completeness.lean` — 1 (DP-4, end of `minimalTableau_complete`).
