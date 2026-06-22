# Product Construction & Model Checking — Literature Sources

## Primary Sources

### Vardi 1996 — An Automata-Theoretic Approach to Linear Temporal Logic
Expanded tutorial version of Vardi-Wolper 1986. Covers the full automata-theoretic framework:
LTL-to-Büchi translation, product construction of system with property automaton, and the
model checking reduction theorem. This is the best single reference for task 251.

- `~/Projects/Literature/sources/vardi_1996/Vardi_1996_Automata_Theoretic_LTL.md` (1295 lines)

### Baier & Katoen 2008 — Principles of Model Checking
The definitive textbook treatment. Relevant chapters:
- Ch. 4 (§4.3–4.4): ω-automata, NBA, product construction, persistence checking
- Ch. 5: LTL syntax/semantics, positive normal form, fairness
- Ch. 5 (continued): Automata-based LTL model checking, the Vardi-Wolper reduction

Parts covering relevant material:
- `~/Projects/Literature/sources/baier_katoen_2008/Baier_Katoen_2008_part03.md` (4000 lines) — Ch. 4: ω-automata, NBA definition, product automaton (Theorem 4.19+), intersection, persistence checking
- `~/Projects/Literature/sources/baier_katoen_2008/Baier_Katoen_2008_part04.md` (4000 lines) — Ch. 5: LTL syntax/semantics, positive normal form, fairness

### Gerth et al. 1995 — Simple On-the-Fly Automatic Verification of LTL
The on-the-fly tableau construction for LTL-to-GNBA. Relevant for understanding the
LTL-to-NBA translation that feeds into the product construction (task 242 dependency).

- `~/Projects/Literature/sources/gerth_1995/Gerth_1995_OnTheFly_LTL_Verification.md` (771 lines)

## Secondary Sources

### Vardi & Wolper 1986 — An Automata-Theoretic Approach to Automatic Program Verification
The original foundational paper. Available as stub only (scanned image PDF, no OCR).
Vardi 1996 above supersedes this with expanded treatment.

- `~/Projects/Literature/sources/vardi_wolper_1986/Vardi_Wolper_1986_Automata_Theoretic_Verification.md` (31 lines — stub)

### Courcoubetis et al. 1992 — Memory-Efficient Algorithms for the Verification of Temporal Properties
Introduces the nested DFS algorithm for emptiness checking on product automata.
Relevant for the algorithmic side of model checking (connects to task 248 emptiness).

- `~/Projects/Literature/sources/courcoubetis_1992/Courcoubetis_1992_Memory_Efficient_Verification.md` (713 lines)

### Schwoon & Esparza 2005 — A Note on On-the-Fly Verification Algorithms
Corrects and clarifies the nested DFS approach from Courcoubetis et al. Useful companion
to the emptiness checking component.

- `~/Projects/Literature/sources/schwoon_esparza_2005/Schwoon_Esparza_2005_Note_OnTheFly_Verification.md` (800 lines)

### Tarjan 1972 — Depth-First Search and Linear Graph Algorithms
Foundation for SCC-based algorithms used in emptiness checking. Background reference.

- `~/Projects/Literature/sources/tarjan_1972/Tarjan_1972_Depth_First_Search_Linear_Graphs.md` (739 lines)

## Not Available (Gaps)

| Reference | Notes |
|-----------|-------|
| Clarke, Grumberg & Peled 1999 (Model Checking, MIT Press) | Textbook; Baier-Katoen 2008 covers the same material |
| Vardi & Wolper 1986 (full text) | Scanned image; Vardi 1996 supersedes |
