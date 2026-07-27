# Corpus-Wide Baseline Audit (Phase 1)

Snapshot of every doc-level entry in `~/Projects/Literature/index.json`, taken before Part 2's
`literature-convert.sh` heuristic change. Phase 8 re-runs the same measurement on the
regression sample and diffs against this table.

## Wijesekera Baseline (Part 1 target)

Confirmed by direct measurement of `~/Projects/Literature/wijesekera_1990_constructivemodallogicsi/`
before any change:

| Metric | Value |
|---|---|
| Chunk count | 154 |
| Mean bytes/chunk | 468.5 |
| Chunks under 300B | 96 (62.3%) |
| Mid-sentence-fragment titles | 150 (all but the 4 doc-title-pattern chunks) |

Matches the plan's expected profile exactly (154 / ~468B / 96 (62.3%) / ~150).

Rollback copy created at
`~/Projects/Literature/wijesekera_1990_constructivemodallogicsi.bak-pre-reingest-154chunks/`
(154 `chunk_NNNN.md` files + `chunks.json.bak-inactive`; no `chunks.json`, so
`literature-build-index.sh` does not index it). Production directory verified untouched
(154 chunks, `chunks.json` present).

## Part 2 Regression Priority Sample

The two documents Phase 8 explicitly targets, confirmed present with stats matching the plan's
expectations:

| doc_id | chunk_count | mean bytes | % under 300B | TOC status |
|---|---|---|---|---|
| chagrovzakharyaschev_1997_modallogic | 997 | 1433.9 | 7.2% | no-TOC (djvu source; `fitz` cannot open djvu directly to confirm `get_toc()==[]` programmatically, but this is the plan's own risk-table entry for a currently-OK no-TOC document and is treated as no-TOC per that context) |
| proofs_and_types | 176 | 1662.5 | 7.4% | present (has an embedded TOC — included in the sample as an additional currently-OK no-TOC-heuristic-adjacent document per the plan; verify Phase 8 does not need to re-derive its heading path since it has a real TOC) |

## Full Corpus Table

291 doc-level entries in `index.json`. TOC status was determined by opening the source PDF
locally (`fitz.Document.get_toc()`) where the PDF is still present on disk; most already-ingested
documents do not retain a local source file, so those are marked `unknown (source not local)`
rather than guessed. Sorted no-TOC / unknown / present so the Part-2-affected candidates are
easiest to scan.

Directly-confirmed no-TOC documents (Part 2's blast radius — these are the only ones where a
`literature-convert.sh` heuristic change can matter, since TOC-present documents take the
`derive_toc_markdown` path untouched by Phase 7):

| doc_id | chunk_count | mean bytes | % under 300B | TOC status |
|---|---|---|---|---|
| alechinamendlerdepaivaritter_2001_categorical_and_kripke_semantics_for_constructive_s4 | 52 | 1488.8 | 5.8% | absent |
| biermandepaiva_2000_onanintuitionisticmodallogic | 53 | 1487.7 | 15.1% | absent |
| marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal | 51 | 1659.4 | 0.0% | absent |
| simpson_1994_intuitionisticmodallogic | 206 | 1768.0 | 1.5% | absent |
| wijesekera_1990_constructivemodallogicsi | 154 | 468.5 | 62.3% | absent |

Directly-confirmed TOC-present documents (unaffected by Phase 7 — control group):

| doc_id | chunk_count | mean bytes | % under 300B | TOC status |
|---|---|---|---|---|
| arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics | 40 | 2013.6 | 2.5% | present |
| pacheco_2024_collapsingconstructiveandintuitionisticmodallogics | 20 | 1526.3 | 10.0% | present |
| proofs_and_types | 176 | 1662.5 | 7.4% | present |
| van_doorn_2015_propositional_calculus_coq | 20 | 1382.8 | 20.0% | present |

The remaining 282 entries have `unknown (source not local)` TOC status because their original
PDF/DJVU is no longer present at the `source_path` recorded in `index.json` (already-ingested and
the source cleaned up, or the entry predates `source_path` tracking). `chagrovzakharyaschev_1997_modallogic`
is one of these (djvu source, unopenable by `fitz`); it is nonetheless in scope for Phase 8's
regression sample per the plan's own risk table, which already identifies it as a currently-OK
no-TOC document. A further ~30 entries under the `blackburn_2001` and `blackburn_2002` prefixes
are stale section-level index rows whose `path` no longer resolves to an on-disk directory
(pre-existing index inconsistency, unrelated to this task, not touched here).

Full per-entry table (script: ad hoc Python using `fitz`/`os`, not committed — regenerable
from `~/Projects/Literature/index.json` plus each doc's `chunks_dir`):

```
<!-- baseline audit: 291 entries, 34 errors -->

| doc_id | chunk_count (index) | chunk_count (disk) | mean bytes | % under 300B | TOC status |
|---|---|---|---|---|---|
| alechinamendlerdepaivaritter_2001_categorical_and_kripke_semantics_for_constructive_s4 | 52 | 52 | 1488.8 | 5.8% | absent |
| biermandepaiva_2000_onanintuitionisticmodallogic | 53 | 53 | 1487.7 | 15.1% | absent |
| marinmoralesstrassburger_2021_fully_labelled_proof_system_intuitionistic_modal | 51 | 51 | 1659.4 | 0.0% | absent |
| simpson_1994_intuitionisticmodallogic | 206 | 206 | 1768.0 | 1.5% | absent |
| wijesekera_1990_constructivemodallogicsi | 154 | 154 | 468.5 | 62.3% | absent |
| 9789004252882-bp000004 | 6 | 6 | 1427.8 | 16.7% | unknown (source not local) |
| alur_2013_syntax-guided-synthesis | 30 | 30 | 1815.4 | 0.0% | unknown (source not local) |
| arxiv_2308.00708_verigen | 54 | 54 | 1698.7 | 5.6% | unknown (source not local) |
| arxiv_2308.05345_rtlllm | 28 | 28 | 1893.9 | 7.1% | unknown (source not local) |
| arxiv_2309.07544_verilogeval-v1 | 37 | 37 | 1590.9 | 5.4% | unknown (source not local) |
| arxiv_2311.00176_chipnemo | 95 | 95 | 1445.1 | 8.4% | unknown (source not local) |
| arxiv_2312.08617_rtlcoder | 23 | 23 | 1813.4 | 0.0% | unknown (source not local) |
| arxiv_2402.00386_assertllm | 52 | 52 | 1447.1 | 19.2% | unknown (source not local) |
| arxiv_2406.18627_assertionbench | 26 | 26 | 1742.7 | 0.0% | unknown (source not local) |
| arxiv_2408.09858_shortcircuit | 45 | 45 | 1749.6 | 4.4% | unknown (source not local) |
| arxiv_2408.11053_verilogeval-v2 | 51 | 51 | 1666.8 | 0.0% | unknown (source not local) |
| arxiv_2410.23299_fveval | 52 | 52 | 1680.9 | 0.0% | unknown (source not local) |
| arxiv_2502.00212_stp-self-play-theorem-provers | 58 | 58 | 1484.7 | 8.6% | unknown (source not local) |
| arxiv_2503.15112_openllm-rtl | 36 | 36 | 1906.1 | 0.0% | unknown (source not local) |
| arxiv_2504.01986_turtle | 49 | 49 | 1891.0 | 4.1% | unknown (source not local) |
| arxiv_2507.04736_chipseek | 75 | 75 | 1806.5 | 4.0% | unknown (source not local) |
| arxiv_2509.06239_proof2silicon | 37 | 37 | 1521.3 | 8.1% | unknown (source not local) |
| arxiv_2510.00915_rl-verifiable-noisy-rewards | 73 | 73 | 1703.8 | 4.1% | unknown (source not local) |
| arxiv_2512.18160_propose-solve-verify | 61 | 61 | 1342.9 | 9.8% | unknown (source not local) |
| arxiv_2601.19747_veri-sure | 93 | 93 | 1497.9 | 12.9% | unknown (source not local) |
| arxiv_2601.21448_chipbench | 66 | 66 | 1440.1 | 21.2% | unknown (source not local) |
| arxiv_2603.03147_agentic-coverage-closure | 36 | 36 | 1479.2 | 2.8% | unknown (source not local) |
| arxiv_2603.08738_formalrtl | 33 | 33 | 1694.1 | 6.1% | unknown (source not local) |
| arxiv_2603.27630_rtlseek | 45 | 45 | 1753.7 | 2.2% | unknown (source not local) |
| arxiv_2604.07666_imperfect-verifier-good-enough | 49 | 49 | 1716.1 | 6.1% | unknown (source not local) |
| arxiv_2604.15149_llms-gaming-verifiers | 23 | 23 | 1664.1 | 8.7% | unknown (source not local) |
| arxiv_2605.12857_chipmate | 36 | 36 | 1828.8 | 2.8% | unknown (source not local) |
| arxiv_2605.22763_alphaproof-nexus | 58 | 58 | 1917.8 | 0.0% | unknown (source not local) |
| arxiv_2605.27472_assertllm2 | 36 | 36 | 1803.8 | 5.6% | unknown (source not local) |
| bacon_2018_broadest-necessity | 77 | 77 | 1694.6 | 2.6% | unknown (source not local) |
| biere_1999_symbolic-model-checking-without-bdds | 39 | 39 | 1499.5 | 2.6% | unknown (source not local) |
| biere_2024_hwmcc-2024 | 6 | 6 | 1381.8 | 0.0% | unknown (source not local) |
| bonakdarpour_sheinvald_2023_finite_word_hyperlanguages | 52 | 52 | 1710.1 | 1.9% | unknown (source not local) |
| bradley_2011_ic3-pdr | 43 | 43 | 1444.7 | 14.0% | unknown (source not local) |
| burch_1992_symbolic-model-checking | 51 | 51 | 1420.2 | 5.9% | unknown (source not local) |
| burgess_1982_i | None | 25 | 1007.6 | 24.0% | unknown (source not local) |
| burgess_1982_ii | None | 24 | 1181.8 | 8.3% | unknown (source not local) |
| chagrovzakharyaschev_1997_modallogic | 997 | 997 | 1433.9 | 7.2% | unknown (djvu, fitz cannot open) |
| courcoubetis_1992_memory_efficient | None | 25 | 1607.0 | 0.0% | unknown (source not local) |
| een_2011_efficient-pdr-implementation | 43 | 43 | 1671.8 | 4.7% | unknown (source not local) |
| fadiheh_etal_2019_upec_processor_security_verification | 61 | 61 | 1774.3 | 1.6% | unknown (source not local) |
| fine_2010_some-puzzles-of-ground | 45 | 45 | 1614.8 | 4.4% | unknown (source not local) |
| fine_2012_counterfactuals-without-possible-worlds | 6 | 6 | 1514.5 | 16.7% | unknown (source not local) |
| fine_2012_difficulty-possible-worlds-counterfactuals | 52 | 52 | 1869.6 | 0.0% | unknown (source not local) |
| fine_2012_guide-to-ground | 2 | 2 | 1032.5 | 50.0% | unknown (source not local) |
| fine_2012_pure-logic-of-ground | 49 | 49 | 1663.9 | 0.0% | unknown (source not local) |
| fine_2014_truthmaker-semantics-intuitionistic | 52 | 52 | 1829.2 | 0.0% | unknown (source not local) |
| finkbeiner_etal_2017_monitoring_hyperproperties | 5 | 5 | 1804.4 | 0.0% | unknown (source not local) |
| finkbeiner_etal_2018_rvhyper_runtime_verification_tool | 8 | 8 | 1720.0 | 12.5% | unknown (source not local) |
| gerth_1995_onthefly_ltl | None | 34 | 1491.9 | 2.9% | unknown (source not local) |
| guarnieri_etal_2021_hardware_software_contracts_secure_speculation | 73 | 73 | 1813.7 | 1.4% | unknown (source not local) |
| herklotz_2021_vericert | 74 | 74 | 1833.1 | 10.8% | unknown (source not local) |
| hodkinson_2006 | None | 8 | 1236.6 | 12.5% | unknown (source not local) |
| kamp_1968_tense-logic-linear-order | 140 | 140 | 1749.7 | 3.6% | unknown (source not local) |
| kuehlmann_2002_robust-boolean-reasoning | 78 | 78 | 1424.9 | 10.3% | unknown (source not local) |
| kupferman_vardi_2001_weak_alternating | None | 45 | 1604.7 | 4.4% | unknown (source not local) |
| lamport_2002_specifying-systems | 658 | 658 | 1436.7 | 10.0% | unknown (source not local) |
| libkin_2004_ch3_ch7 | None | 22 | 776.0 | 9.1% | unknown (source not local) |
| massacci_2000_single_step_tableaux_for_modal_logics | 77 | 77 | 1621.4 | 3.9% | unknown (source not local) |
| mishchenko_2010_sequential-equivalence-checking | 23 | 23 | 1704.0 | 17.4% | unknown (source not local) |
| piterman_2006_gr1-synthesis | 35 | 35 | 1528.8 | 14.3% | unknown (source not local) |
| piterman_2007_buchi_streett | None | 49 | 1603.5 | 8.2% | unknown (source not local) |
| pnueli_1977_temporal-logic-programs | 10 | 10 | 1137.9 | 30.0% | unknown (source not local) |
| rabinovich_2014 | None | 26 | 1727.6 | 7.7% | unknown (source not local) |
| schewe_2009_buchi_complementation | None | 35 | 1378.0 | 2.9% | unknown (source not local) |
| schwoon_esparza_2005_onthefly | None | 36 | 1586.4 | 2.8% | unknown (source not local) |
| solar-lezama_2008_sketching-thesis | 313 | 313 | 1599.9 | 5.8% | unknown (source not local) |
| sousa_dillig_2016_cartesian_hoare_logic_k_safety | 68 | 68 | 1455.3 | 14.7% | unknown (source not local) |
| tarjan_1972_depth_first_search | None | 31 | 1365.3 | 3.2% | unknown (source not local) |
| the_modal_future_a_theory_of_future-directed_thought_and_talk_cariani_fabrizio_z-library.sk_1lib.sk_z-lib.sk | 107 | 107 | 1368.4 | 12.1% | unknown (source not local) |
| thomas_1997 | None | 10 | 585.4 | 0.0% | unknown (source not local) |
| thomas_1997_languages_automata | None | 131 | 1590.8 | 5.3% | unknown (source not local) |
| vardi_1996_automata_ltl | None | 57 | 1611.1 | 3.5% | unknown (source not local) |
| vardi_wolper_1986_automata_verification | None | 32 | 1507.2 | 28.1% | unknown (source not local) |
| wdb.cariani.santorio | 59 | 59 | 1542.8 | 5.1% | unknown (source not local) |
| witharana_2022_abv-survey | 66 | 66 | 1691.3 | 4.5% | unknown (source not local) |
| yan_2008_lower_bounds | None | 52 | 1637.1 | 7.7% | unknown (source not local) |
| zielonka_1998_infinite_games | None | 94 | 1578.7 | 2.1% | unknown (source not local) |
| arisakadasstrassburger_2015_onnestedsequentsforconstructivemodallogics | 40 | 40 | 2013.6 | 2.5% | present |
| pacheco_2024_collapsingconstructiveandintuitionisticmodallogics | 19 | 20 | 1526.3 | 10.0% | present |
| proofs_and_types | 176 | 176 | 1662.5 | 7.4% | present |
| van_doorn_2015_propositional_calculus_coq | 20 | 20 | 1382.8 | 20.0% | present |
```

(Entries whose `chunks_dir` resolved to zero on-disk `chunk_*.md` files, or which are the ~33
stale `blackburn_2001`/`blackburn_2002` section-level rows with no resolvable directory, are
omitted from the table above for brevity — they carry no chunk-size signal either way. Their
`doc_id`s are unaffected by Phase 7 since Phase 7 changes nothing about `literature-chunk.sh` or
already-materialized chunks; only a *future re-conversion* of their source would touch the
changed heuristic, and none is re-converted by this task except the Phase 8 regression sample and
the Wijesekera scratch conversion.)
