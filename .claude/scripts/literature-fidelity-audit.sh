#!/usr/bin/env bash
# literature-fidelity-audit.sh - Re-runnable provenance/fidelity detector and stamper
# for the ~/Projects/Literature corpus (task #835).
#
# Usage:
#   literature-fidelity-audit.sh [--dry-run]   # report-only (default): classify every
#                                               # sources/<dir>/ and print a TSV/JSON
#                                               # report to stdout. index.json is never
#                                               # touched.
#   literature-fidelity-audit.sh --write       # backup index.json, then idempotently
#                                               # stamp .provenance_fidelity and
#                                               # .word_ratio onto every parent entry
#                                               # (see "Target entry resolution" below).
#   literature-fidelity-audit.sh --legacy-schema [--dry-run|--write]
#                                               # Classify the legacy doc_id/chunks_dir-
#                                               # schema entries instead of the sources/
#                                               # schema. --dry-run/--write remain
#                                               # orthogonal (same report-vs-write
#                                               # semantics as above). See "Legacy schema
#                                               # mode" below.
#
# What this computes (see report 01_provenance-fidelity-audit.md for full rationale):
#   For each sources/<dir>/ directory, classify into one of five provenance_fidelity
#   values using a conservative three-signal detector:
#     1. Whole-DOCUMENT word-ratio (md_words summed over ALL .md in the dir, divided by
#        pdf_words summed over ALL *.pdf/*.djvu in the dir via `pdftotext -layout`).
#        NEVER sampled from a single file — single-file sampling is a known false-
#        discriminator (see report "Correction to Pre-Verified Evidence").
#     2. Disclosure check (only when ratio < 0.75): does the .md content or the
#        matching index.json summary text admit to being a selective/partial
#        conversion? If so -> verified_conversion (disclosed partial).
#     3. Proof/body-completeness check (only when ratio < 0.75 and undisclosed): for
#        headings matching Definition/Lemma/Theorem/Proposition/Corollary N[.N...],
#        Lemma/Theorem/Proposition/Corollary headings are adequate only if an explicit
#        "Proof" marker follows in their body (a claim without a proof is not proved,
#        regardless of how many lines it spans); Definition headings are adequate if
#        they carry real defining content (>=2 non-blank lines or >=15 words). If the
#        fraction of adequate numbered statements is below 0.6 -> unverified_summary.
#
#   `chunk_*.md` filename presence/absence and a standalone leading "## Overview"
#   heading are deliberately NOT used as signals (both are false discriminators in
#   this corpus — see report). This is intentional; do not add them back without
#   re-reading the report's "Detector Design" section.
#
# Six-value enum: verified_conversion, unverified_summary, no_source_pdf,
# not_yet_converted, unverified_no_baseline, unadjudicated.
#
# Target entry resolution (which index.json entries get stamped):
#   A directory's entries are all index.json entries whose `.path` starts with
#   "sources/<dir>/" (robust to id-naming drift — some directories host multiple
#   independent top-level docs, e.g. thomas_2003_reactive -> thomas_2003_ch01 +
#   thomas_2003_ch03, each stamped independently with the SAME directory-aggregated
#   ratio). Among matched entries:
#     - If any matched entry has no `parent_doc` (a true root), stamp only those root
#       entries. This is the common case and matches the plan's "parent entries only"
#       design exactly.
#     - If NO matched entry is a root (a pre-existing, orthogonal corpus data gap: some
#       directories' children carry a `parent_doc` value with no corresponding
#       top-level `id` row at all — e.g. doets_1987, venema_1991, thomason_1984 in the
#       current corpus), fall back to stamping every matched child entry directly. This
#       is a deliberate, documented deviation from a strict "parent-only" reading,
#       necessary so that literature-search.sh's per-chunk doc_id lookup (which will
#       return one of these child rows) resolves the correct fidelity value instead of
#       fail-open-defaulting an entire legitimate disclosed-partial document to
#       unverified. See the implementation summary for the full directory list this
#       applies to.
#     - If no entry's path matches the directory at all, nothing is stamped (the
#       directory has no index.json presence yet); this is reported, not treated as an
#       error.
#   Only entries under sources/<dir>/ are ever touched. Entries using the unrelated
#   legacy `doc_id`/`chunks_dir` schema (no `path`/`id` fields, from a different
#   ingestion pipeline, live outside sources/) are never matched or written -- UNLESS
#   --legacy-schema is passed, in which case ONLY those entries are matched/written
#   (see "Legacy schema mode" below); the two schemas' write paths never interleave.
#
# Legacy schema mode (--legacy-schema):
#   Some index.json entries come from an unrelated ingestion pipeline: they carry
#   `doc_id` + `chunks_dir` (an absolute path to a directory of chunk_NNNN.md files)
#   and no `path`/`id` fields at all. --legacy-schema enumerates exactly those entries
#   (doc_id and chunks_dir both present, path and id both absent-or-null -- this gate
#   is the entire safety boundary between the two schemas) and classifies each by:
#     - Resolving its source as $LITERATURE_DIR/.sources-recovered/<doc_id>.pdf (or
#       .djvu). No source present -> no_source_pdf.
#     - Summing word_count_text() over ALL chunk_*.md in chunks_dir as md_words (the
#       chunk-exclusion filter used for the sources/ schema is deliberately NOT
#       applied here -- for this schema the chunks ARE the document, there is no
#       separate whole-document .md).
#     - Reusing the same word-ratio / disclosure_check / proof_completeness_fraction
#       pipeline as the sources/ schema, unchanged, against that chunk text.
#     - A .djvu (or any source producing 0 extracted words, e.g. no djvu text
#       extractor installed) is classified unadjudicated with an explicit
#       "[blocked]" stderr note -- never unverified_no_baseline, since a baseline
#       (the .djvu file) does exist; only the extractor is missing.
#   --write stamps provenance_fidelity/word_ratio directly onto the matched entry by
#   doc_id equality (resolve_legacy_targets(), never resolve_targets() -- the latter's
#   path-prefix/id-presence logic is for the other schema). no_source_pdf and the
#   djvu-blocked unadjudicated case are deliberately left unstamped (reported
#   explicitly in the write summary, not silently skipped) -- their disposition is a
#   separate, explicit decision outside this script's scope.
#
# Idempotency: re-running --write on an already-stamped corpus is a no-op relative to
# the first --write's output (same values, stable key order, no diff). The FIRST
# --write will reformat the whole file (json.dump normalizes indentation/unicode
# escaping across all 280 entries, not just the ~100 stamped ones) since a full
# parse/re-serialize is required to add fields; this is a one-time, backed-up,
# content-preserving formatting normalization, not a data change.
#
# Safety:
#   - Backup-first: index.json is copied to index.json.bak.<UTC timestamp> and the
#     copy is verified byte-identical before any write proceeds.
#   - Atomic: writes go to a temp file in the same directory, then `mv` over
#     index.json.
#   - Fail-open is a RETRIEVAL-side property (literature-search.sh / literature-
#     briefing.sh treat an absent field as unverified). This script's own job is only
#     to compute and stamp; it does not implement fail-open itself.
#   - Never touches anything under sources/ (read-only pdftotext/wc access only).
#   - Never deletes any entry, PDF, or markdown file. Quarantine is a retrieval-time
#     concern handled entirely by the two retrieval scripts.
#
# Environment:
#   LITERATURE_DIR  Path to the global Literature/ repo (default: ~/Projects/Literature)

set -euo pipefail

LITERATURE_DIR="${LITERATURE_DIR:-$HOME/Projects/Literature}"
MODE="report"
LEGACY_SCHEMA="false"

usage() {
  cat <<'EOF'
Usage: literature-fidelity-audit.sh [--dry-run|--write] [--legacy-schema] [-h|--help]

  --dry-run       Report-only (default). Classify every sources/<dir>/ and print a
                  per-directory report to stdout. index.json is never modified.
  --write         Backup index.json, then idempotently stamp provenance_fidelity and
                  word_ratio onto the resolved target entries for every directory.
  --legacy-schema Classify the legacy doc_id/chunks_dir-schema entries instead of the
                  sources/ schema. Orthogonal to --dry-run/--write. Requires
                  .sources-recovered/ under LITERATURE_DIR.
  -h, --help      Show this help.
EOF
}

for arg in "$@"; do
  case "$arg" in
    --write)
      MODE="write"
      ;;
    --dry-run | --report)
      MODE="report"
      ;;
    --legacy-schema)
      LEGACY_SCHEMA="true"
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      echo "Unknown argument: $arg" >&2
      usage
      exit 1
      ;;
  esac
done

if [ ! -d "$LITERATURE_DIR" ]; then
  echo "Error: LITERATURE_DIR not found: $LITERATURE_DIR" >&2
  exit 1
fi

SOURCES_DIR="$LITERATURE_DIR/sources"
if [ ! -d "$SOURCES_DIR" ]; then
  echo "Error: sources/ not found under LITERATURE_DIR: $SOURCES_DIR" >&2
  exit 1
fi

RECOVERED_DIR="$LITERATURE_DIR/.sources-recovered"
if [ "$LEGACY_SCHEMA" = "true" ] && [ ! -d "$RECOVERED_DIR" ]; then
  echo "Error: --legacy-schema requires .sources-recovered/ under LITERATURE_DIR: $RECOVERED_DIR" >&2
  exit 1
fi

INDEX_FILE="$LITERATURE_DIR/index.json"
if [ ! -f "$INDEX_FILE" ]; then
  echo "Error: index.json not found: $INDEX_FILE" >&2
  exit 1
fi

if ! command -v pdftotext >/dev/null 2>&1; then
  echo "Error: pdftotext not found on PATH (required for word-ratio computation)" >&2
  exit 1
fi

BACKUP_FILE=""
if [ "$MODE" = "write" ]; then
  ts="$(date -u +%Y%m%d-%H%M%S)"
  BACKUP_FILE="$INDEX_FILE.bak.$ts"
  cp -p "$INDEX_FILE" "$BACKUP_FILE"
  if ! cmp -s "$INDEX_FILE" "$BACKUP_FILE"; then
    echo "Error: backup verification failed ($BACKUP_FILE does not match $INDEX_FILE); aborting, no write performed" >&2
    exit 1
  fi
  echo "[fidelity-audit] Backup created and verified: $BACKUP_FILE" >&2
fi

LITERATURE_DIR="$LITERATURE_DIR" \
SOURCES_DIR="$SOURCES_DIR" \
RECOVERED_DIR="$RECOVERED_DIR" \
INDEX_FILE="$INDEX_FILE" \
MODE="$MODE" \
LEGACY_SCHEMA="$LEGACY_SCHEMA" \
python3 <<'PYEOF'
import json
import os
import re
import subprocess
import sys
from collections import Counter

LITERATURE_DIR = os.environ["LITERATURE_DIR"]
SOURCES_DIR = os.environ["SOURCES_DIR"]
RECOVERED_DIR = os.environ["RECOVERED_DIR"]
INDEX_FILE = os.environ["INDEX_FILE"]
MODE = os.environ["MODE"]
LEGACY_SCHEMA = os.environ.get("LEGACY_SCHEMA", "false") == "true"

RATIO_THRESHOLD = 0.75
PROOF_ADEQUACY_THRESHOLD = 0.6

# The six values this script's own detector computes. A legacy entry whose CURRENT
# provenance_fidelity is already set to something outside this set (e.g. the
# out-of-band "ocr_rescanned_reflowed_partial_symbol_loss" some legacy entries carry
# from an earlier, more specific manual/OCR-provenance assessment) is an
# already-honestly-stamped entry this detector must never clobber with its own
# coarser six-value classification -- see main_legacy()'s write loop.
SIX_VALUE_ENUM = {
    "verified_conversion", "unverified_summary", "no_source_pdf",
    "not_yet_converted", "unverified_no_baseline", "unadjudicated",
}

DISCLOSURE_RE = re.compile(
    r"selective conversion|extracted:?\s*chapter|truncated|excerpt|chapters?\s+\d+\s+and\s+\d+",
    re.IGNORECASE,
)
HEADING_RE = re.compile(
    r"^(#+)\s*(Definition|Lemma|Theorem|Proposition|Corollary)\s+([\d.]+)", re.IGNORECASE
)
PROOF_MARKER_RE = re.compile(r"\bProof\b", re.IGNORECASE)


def word_count_text(text):
    return len(text.split())


def pdf_word_count(pdf_path):
    if pdf_path.lower().endswith(".djvu"):
        # No djvutxt dependency assumed available; no .djvu files exist in the
        # current corpus. Best-effort: skip (contributes 0 words) rather than
        # crash, with a warning so a future .djvu addition is visible.
        print(f"[warn] .djvu extraction not implemented, skipping: {pdf_path}", file=sys.stderr)
        return 0
    try:
        out = subprocess.run(
            ["pdftotext", "-layout", pdf_path, "-"],
            capture_output=True, text=True, timeout=180,
        )
        return word_count_text(out.stdout)
    except Exception as e:
        print(f"[warn] pdftotext failed for {pdf_path}: {e}", file=sys.stderr)
        return 0


def disclosure_check(md_texts, index_summaries):
    combined = "\n".join(md_texts) + "\n" + "\n".join(index_summaries)
    return bool(DISCLOSURE_RE.search(combined))


def proof_completeness_fraction(md_texts):
    """Fraction of numbered Definition/Lemma/Theorem/Proposition/Corollary headings
    (across all .md files of the document) that have an adequate body before the
    next equal-or-higher-level heading.

    Lemma/Theorem/Proposition/Corollary are *claims*: adequate only if an explicit
    'Proof' marker appears directly in the body. A list of unproved clauses with no
    'Proof' text is NOT adequate no matter how many lines it spans -- this is the
    decisive discriminator for a hand-authored paraphrase that states results
    without proving them (see report exemplar: Lemma 3.2 in rabinovich_2014, three
    bare unproved clauses).

    Definition headings are not claims and carry no proof; adequate if the body has
    real defining content (>=2 non-blank lines or >=15 words), not a one-line gloss.
    """
    total = 0
    adequate = 0
    for text in md_texts:
        lines = text.splitlines()
        i, n = 0, len(lines)
        while i < n:
            m = HEADING_RE.match(lines[i])
            if m:
                level = len(m.group(1))
                heading_type = m.group(2).lower()
                total += 1
                j = i + 1
                body_lines = []
                while j < n:
                    hm = re.match(r"^(#+)\s", lines[j])
                    if hm and len(hm.group(1)) <= level:
                        break
                    body_lines.append(lines[j])
                    j += 1
                body_text = "\n".join(body_lines)
                nonblank = [ln for ln in body_lines if ln.strip()]
                has_proof_marker = bool(PROOF_MARKER_RE.search(body_text))

                if heading_type == "definition":
                    is_adequate = len(nonblank) >= 2 or word_count_text(body_text) >= 15
                else:
                    is_adequate = has_proof_marker

                if is_adequate:
                    adequate += 1
                i = j
            else:
                i += 1
    if total == 0:
        return None, 0, 0
    return adequate / total, adequate, total


def load_index_entries():
    with open(INDEX_FILE, encoding="utf-8") as f:
        idx = json.load(f)
    return idx


def summaries_for_dir(idx, dirname):
    prefix = f"sources/{dirname}/"
    out = []
    for e in idx.get("entries", []):
        p = e.get("path")
        if isinstance(p, str) and p.startswith(prefix) and e.get("summary"):
            out.append(e["summary"])
    return out


def classify_dir(dirname, idx):
    dirpath = os.path.join(SOURCES_DIR, dirname)
    try:
        entries_on_disk = os.listdir(dirpath)
    except OSError as e:
        print(f"[warn] cannot list {dirpath}: {e}", file=sys.stderr)
        entries_on_disk = []

    pdfs = sorted(
        os.path.join(dirpath, e) for e in entries_on_disk
        if e.lower().endswith((".pdf", ".djvu"))
    )
    mds = sorted(
        os.path.join(dirpath, e) for e in entries_on_disk
        if e.lower().endswith(".md")
        and not re.match(r"^chunk_\d+\.md$", e, re.IGNORECASE)
    )

    has_pdf = len(pdfs) > 0
    has_md = len(mds) > 0

    result = {
        "dir": dirname,
        "has_pdf": has_pdf,
        "has_md": has_md,
        "pdf_words": None,
        "md_words": None,
        "word_ratio": None,
        "proof_fraction": None,
        "disclosed": None,
        "provenance_fidelity": None,
    }

    if not has_pdf and has_md:
        result["provenance_fidelity"] = "no_source_pdf"
        return result
    if has_pdf and not has_md:
        result["provenance_fidelity"] = "not_yet_converted"
        return result
    if not has_pdf and not has_md:
        # Anomalous (empty or non-pdf/md-only directory). Fail open: never
        # silently "verified".
        result["provenance_fidelity"] = "unverified_no_baseline"
        return result

    md_texts = []
    md_words_total = 0
    for md in mds:
        t = ""
        try:
            with open(md, encoding="utf-8", errors="replace") as f:
                t = f.read()
        except OSError as e:
            print(f"[warn] read failed for {md}: {e}", file=sys.stderr)
        md_texts.append(t)
        md_words_total += word_count_text(t)

    pdf_words_total = sum(pdf_word_count(p) for p in pdfs)

    result["md_words"] = md_words_total
    result["pdf_words"] = pdf_words_total

    if pdf_words_total == 0:
        result["provenance_fidelity"] = "unverified_no_baseline"
        return result

    ratio = md_words_total / pdf_words_total
    result["word_ratio"] = round(ratio, 4)

    if ratio >= RATIO_THRESHOLD:
        result["provenance_fidelity"] = "verified_conversion"
        return result

    index_summaries = summaries_for_dir(idx, dirname)
    disclosed = disclosure_check(md_texts, index_summaries)
    result["disclosed"] = disclosed
    if disclosed:
        result["provenance_fidelity"] = "verified_conversion"
        return result

    frac, adequate, total = proof_completeness_fraction(md_texts)
    result["proof_fraction"] = frac
    if frac is None:
        # No numbered statements to check at all: the proof-completeness signal
        # cannot fire. This is the ABSENCE of a signal, not a positive finding --
        # a low-ratio, undisclosed document with no numbered statements to check
        # has not been adjudicated by any of the three signals. Fail CLOSED:
        # stamp "unadjudicated" rather than reading silence as a pass. (Task
        # #839 fix -- previously fell through to verified_conversion here, which
        # was a fail-open misclassification; see report 01_provenance-fidelity-audit.md
        # and specs/839_fix_fidelity_audit_fail_open/ for the realized-risk record.)
        result["provenance_fidelity"] = "unadjudicated"
        return result

    if frac < PROOF_ADEQUACY_THRESHOLD:
        result["provenance_fidelity"] = "unverified_summary"
    else:
        result["provenance_fidelity"] = "verified_conversion"
    return result


def resolve_targets(idx, dirname):
    """Return (target_entries, resolution_kind) for a directory. See the script
    header's "Target entry resolution" section for the full rationale."""
    prefix = f"sources/{dirname}/"
    matched = [
        e for e in idx.get("entries", [])
        if isinstance(e.get("path"), str) and e["path"].startswith(prefix) and "id" in e
    ]
    if not matched:
        return [], "no_match"
    roots = [e for e in matched if not e.get("parent_doc")]
    if roots:
        return roots, "root"
    return matched, "phantom_parent_fallback"


def enumerate_legacy_entries(idx):
    """Return every index.json entry using the legacy doc_id/chunks_dir schema. This
    gate is the entire safety boundary between the two schemas -- it must never match
    a sources/-schema entry: doc_id and chunks_dir both present, AND path is
    absent-or-null, AND id is absent-or-null."""
    out = []
    for e in idx.get("entries", []) or []:
        if not e.get("doc_id") or not e.get("chunks_dir"):
            continue
        if e.get("path") is not None:
            continue
        if e.get("id") is not None:
            continue
        out.append(e)
    return out


def classify_legacy(entry):
    """Classify one legacy doc_id/chunks_dir-schema entry. Mirrors classify_dir()'s
    ratio/disclosure/proof-completeness pipeline exactly, but resolves the source PDF
    from RECOVERED_DIR by doc_id and sums word_count_text() over ALL chunk_*.md in
    chunks_dir (no chunk-exclusion filter -- for this schema the chunks ARE the
    document)."""
    doc_id = entry["doc_id"]
    chunks_dir = entry["chunks_dir"]

    result = {
        "dir": doc_id,
        "doc_id": doc_id,
        "has_pdf": False,
        "has_md": False,
        "pdf_words": None,
        "md_words": None,
        "word_ratio": None,
        "proof_fraction": None,
        "disclosed": None,
        "provenance_fidelity": None,
        "djvu_blocked": False,
    }

    src_pdf = os.path.join(RECOVERED_DIR, f"{doc_id}.pdf")
    src_djvu = os.path.join(RECOVERED_DIR, f"{doc_id}.djvu")
    if os.path.isfile(src_pdf):
        src = src_pdf
    elif os.path.isfile(src_djvu):
        src = src_djvu
    else:
        result["provenance_fidelity"] = "no_source_pdf"
        return result
    result["has_pdf"] = True

    try:
        chunk_files = sorted(
            e for e in os.listdir(chunks_dir)
            if re.match(r"^chunk_\d+\.md$", e, re.IGNORECASE)
        )
    except OSError as e:
        print(f"[warn] cannot list {chunks_dir}: {e}", file=sys.stderr)
        chunk_files = []

    md_texts = []
    md_words_total = 0
    for cf in chunk_files:
        p = os.path.join(chunks_dir, cf)
        t = ""
        try:
            with open(p, encoding="utf-8", errors="replace") as f:
                t = f.read()
        except OSError as e:
            print(f"[warn] read failed for {p}: {e}", file=sys.stderr)
        md_texts.append(t)
        md_words_total += word_count_text(t)

    result["has_md"] = len(chunk_files) > 0
    result["md_words"] = md_words_total

    pdf_words_total = pdf_word_count(src)
    result["pdf_words"] = pdf_words_total

    if pdf_words_total == 0:
        # A baseline (the recovered PDF/DJVU) exists but the extractor produced zero
        # words -- e.g. a .djvu with no djvutxt/djvups/working PyMuPDF codec on this
        # machine. This is NOT the same as no_source_pdf/unverified_no_baseline
        # (which mean "no baseline exists at all"): fail closed with an explicit
        # blocked-reason note rather than silently picking either quarantined value.
        print(
            f"[blocked] {doc_id}: source {src} produced 0 extracted words "
            "(no working text extractor for this source format) -- classified "
            "unadjudicated, NOT unverified_no_baseline; a baseline exists, the "
            "extractor does not",
            file=sys.stderr,
        )
        result["djvu_blocked"] = True
        result["provenance_fidelity"] = "unadjudicated"
        return result

    ratio = md_words_total / pdf_words_total
    result["word_ratio"] = round(ratio, 4)

    if ratio >= RATIO_THRESHOLD:
        result["provenance_fidelity"] = "verified_conversion"
        return result

    index_summaries = [entry["summary"]] if entry.get("summary") else []
    disclosed = disclosure_check(md_texts, index_summaries)
    result["disclosed"] = disclosed
    if disclosed:
        result["provenance_fidelity"] = "verified_conversion"
        return result

    frac, adequate, total = proof_completeness_fraction(md_texts)
    result["proof_fraction"] = frac
    if frac is None:
        result["provenance_fidelity"] = "unadjudicated"
        return result

    if frac < PROOF_ADEQUACY_THRESHOLD:
        result["provenance_fidelity"] = "unverified_summary"
    else:
        result["provenance_fidelity"] = "verified_conversion"
    return result


def resolve_legacy_targets(idx, doc_id):
    """Return the single legacy-schema entry whose doc_id equals the classified
    doc_id AND which passes the enumerate_legacy_entries() gate, or None. Never call
    resolve_targets() in legacy mode -- its path-prefix/id-presence logic is for the
    other schema."""
    for e in idx.get("entries", []) or []:
        if e.get("doc_id") != doc_id:
            continue
        if not e.get("chunks_dir"):
            continue
        if e.get("path") is not None:
            continue
        if e.get("id") is not None:
            continue
        return e
    return None


def print_report(results):
    print("dir\tprovenance_fidelity\tword_ratio\tmd_words\tpdf_words\tdisclosed\tproof_fraction")
    for r in results:
        print(
            f"{r['dir']}\t{r['provenance_fidelity']}\t{r['word_ratio']}\t"
            f"{r['md_words']}\t{r['pdf_words']}\t{r['disclosed']}\t{r['proof_fraction']}"
        )

    counts = Counter(r["provenance_fidelity"] for r in results)
    print("\n--- Population summary ---", file=sys.stderr)
    for k in ("verified_conversion", "unverified_summary", "no_source_pdf",
              "not_yet_converted", "unverified_no_baseline", "unadjudicated"):
        print(f"{k}: {counts.get(k, 0)}", file=sys.stderr)
    print(f"Total directories: {len(results)}", file=sys.stderr)


def main_default():
    """sources/-schema mode: unchanged behavior, routed through resolve_targets()."""
    idx = load_index_entries()

    dirs = sorted(
        d for d in os.listdir(SOURCES_DIR)
        if os.path.isdir(os.path.join(SOURCES_DIR, d))
    )

    results = [classify_dir(d, idx) for d in dirs]
    print_report(results)

    if MODE != "write":
        return

    stamped = 0
    changed = 0
    unchanged = 0
    no_match_dirs = []
    phantom_fallback_dirs = []

    for r in results:
        targets, kind = resolve_targets(idx, r["dir"])
        if kind == "no_match":
            no_match_dirs.append(r["dir"])
            continue
        if kind == "phantom_parent_fallback":
            phantom_fallback_dirs.append((r["dir"], len(targets)))
        for e in targets:
            prev_fidelity = e.get("provenance_fidelity")
            prev_ratio = e.get("word_ratio")
            new_fidelity = r["provenance_fidelity"]
            new_ratio = r["word_ratio"]
            if prev_fidelity == new_fidelity and prev_ratio == new_ratio:
                unchanged += 1
            else:
                changed += 1
            e["provenance_fidelity"] = new_fidelity
            e["word_ratio"] = new_ratio
            stamped += 1

    tmp_path = INDEX_FILE + ".tmp"
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(idx, f, indent=2, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp_path, INDEX_FILE)

    print("\n--- Write summary ---", file=sys.stderr)
    print(f"Entries stamped (total writes): {stamped}", file=sys.stderr)
    print(f"  changed:   {changed}", file=sys.stderr)
    print(f"  unchanged: {unchanged}", file=sys.stderr)
    print(f"Directories with no matching index entry (skipped, nothing to stamp): {len(no_match_dirs)}", file=sys.stderr)
    for d in no_match_dirs:
        print(f"  {d}", file=sys.stderr)
    print(f"Directories using phantom-parent fallback (stamped onto child entries directly): {len(phantom_fallback_dirs)}", file=sys.stderr)
    for d, n in phantom_fallback_dirs:
        print(f"  {d} ({n} entries)", file=sys.stderr)


def main_legacy():
    """--legacy-schema mode: doc_id/chunks_dir entries only, routed through
    resolve_legacy_targets(). Never touches a sources/-schema entry -- see
    enumerate_legacy_entries()'s gate."""
    idx = load_index_entries()

    entries = enumerate_legacy_entries(idx)
    results = [classify_legacy(e) for e in entries]
    print_report(results)

    if MODE != "write":
        return

    stamped = 0
    changed = 0
    unchanged = 0
    no_match_doc_ids = []
    skipped = []  # (doc_id, fidelity) deliberately left unstamped
    already_honest = []  # (doc_id, existing_value) -- pre-existing out-of-band value, never clobbered

    for r in results:
        doc_id = r["doc_id"]
        fidelity = r["provenance_fidelity"]
        # no_source_pdf (no recovered source at all) and the djvu-blocked
        # unadjudicated case (a baseline exists but the extractor does not) are
        # deliberately left unstamped -- reported explicitly below, not silently
        # skipped. Their disposition is out of this script's scope.
        if fidelity == "no_source_pdf" or r.get("djvu_blocked"):
            skipped.append((doc_id, fidelity))
            continue

        target = resolve_legacy_targets(idx, doc_id)
        if target is None:
            no_match_doc_ids.append(doc_id)
            continue

        prev_fidelity = target.get("provenance_fidelity")
        # An entry already carrying a value OUTSIDE this script's own six-value enum
        # (e.g. the Group A pair's out-of-band "ocr_rescanned_reflowed_partial_
        # symbol_loss", a more specific manual/OCR-provenance assessment made
        # elsewhere) is already-honestly-stamped and must never be clobbered by this
        # detector's coarser classification. Re-running this script's own six-value
        # classifications (Group B, once stamped) remains fully idempotent since
        # those values ARE in SIX_VALUE_ENUM.
        if prev_fidelity is not None and prev_fidelity not in SIX_VALUE_ENUM:
            already_honest.append((doc_id, prev_fidelity))
            continue

        prev_ratio = target.get("word_ratio")
        new_ratio = r["word_ratio"]
        if prev_fidelity == fidelity and prev_ratio == new_ratio:
            unchanged += 1
        else:
            changed += 1
        target["provenance_fidelity"] = fidelity
        target["word_ratio"] = new_ratio
        stamped += 1

    tmp_path = INDEX_FILE + ".tmp"
    with open(tmp_path, "w", encoding="utf-8") as f:
        json.dump(idx, f, indent=2, ensure_ascii=False)
        f.write("\n")
    os.replace(tmp_path, INDEX_FILE)

    print("\n--- Legacy write summary ---", file=sys.stderr)
    print(f"Entries stamped (total writes): {stamped}", file=sys.stderr)
    print(f"  changed:   {changed}", file=sys.stderr)
    print(f"  unchanged: {unchanged}", file=sys.stderr)
    print(f"doc_ids with no matching legacy entry (skipped, nothing to stamp): {len(no_match_doc_ids)}", file=sys.stderr)
    for d in no_match_doc_ids:
        print(f"  {d}", file=sys.stderr)
    print(f"doc_ids deliberately left unstamped (no_source_pdf or djvu-blocked): {len(skipped)}", file=sys.stderr)
    for d, fidelity in skipped:
        print(f"  {d}\t{fidelity}", file=sys.stderr)
    print(f"doc_ids already honestly stamped (pre-existing out-of-band value, never clobbered): {len(already_honest)}", file=sys.stderr)
    for d, fidelity in already_honest:
        print(f"  {d}\t{fidelity}", file=sys.stderr)


def main():
    if LEGACY_SCHEMA:
        main_legacy()
    else:
        main_default()


if __name__ == "__main__":
    main()
PYEOF
