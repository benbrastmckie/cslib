---
title: "Executing a Cslib decision procedure in CslibTests: dual imports, #eval, no decide"
created: 2026-07-26
tags: [CONFIG, cslib, CslibTests, conformance-harness, decision-procedure, tableau]
topic: "CSLib CslibTests conformance harness for decision procedures"
source: "Task 552: tableau_calculus_conformance_rule_completeness_repair"
modified: 2026-07-26
---

# Executing a Cslib decision procedure in CslibTests: dual imports, #eval, no decide

To execute a Cslib decision procedure inside a `CslibTests` file, the file needs **both**
`import X` and `public meta import X` for the **same** module:

- Without the plain `import`, defs referencing constructors fail with
  `may not access declaration ... imported as meta`.
- Without the meta import, `#eval` fails with
  `Invalid meta definition _eval, ... is not accessible here`.

`decide` / `native_decide` / `rfl` do **not** work on tableau drivers — they compile to
`WellFounded.fix` via nested `let rec` and stall in the kernel. This is documented at
`CslibTests/ModalFrameSeparation.lean:19-35`.

The assertion idiom is `#guard_msgs in #eval` with a `String`- or `Bool`-valued verdict
adapter, since the result types derive neither `Repr` nor `BEq`.

## Connections
<!-- Add links to related memories using [[filename]] syntax -->
- [[executed-conformance-before-completeness-proofs]]
