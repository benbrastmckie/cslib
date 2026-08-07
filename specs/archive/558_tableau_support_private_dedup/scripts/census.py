#!/usr/bin/env python3
"""
Declaration-level duplicate census for Cslib/Logics/Modal/Tableau.

Reused identically across every deletion phase per the plan's Research Integration
section: "Drive off signatures, not comments." Never grep the `Local re-derivation`
comment string alone -- 17 of 72 duplicates carry no such comment, and the comments
falsely flag some byte-identical copies (e.g. mem_modalUniverse_of) as deviant.

Two independent duplicate signals, unioned into one census:

  (A) EXACT-NAME duplicates: the identical top-level lemma/theorem identifier is
      declared (private or public) in 2+ files within the subsystem. This is the
      dominant pattern (e.g. `hasEdge_addEdge_cases`, `mem_modalKnownWorlds`).

  (B) SUFFIX-FAMILY duplicates: a declaration's name ends in one of the known
      per-driver suffixes (_B _C _S4 _S5 _S5w _Five _FS _anc _local _origin
      _S4Keyed) and the base name (suffix stripped) is ALSO declared somewhere
      in the subsystem (with or without a suffix of its own). Captures cases
      like `hasEdge_addEdge_cases_anc` duplicating `hasEdge_addEdge_cases`.

Usage:
    python3 census.py                    # full report, both signals, union count
    python3 census.py --family NAME      # restrict to declarations whose exact
                                          # name equals NAME, or whose base
                                          # (per signal B) equals NAME
    python3 census.py --files F1 F2 ...  # restrict scanned files to this filename
                                          # subset (e.g. two-file phase scoping)

Output: prints per-family listing (file:line, private/public) then a summary line
"TOTAL_DUPLICATE_DECLARATIONS=<n> TOTAL_FAMILIES=<m>" for scripted comparison
against the plan's stated estimates. A "duplicate declaration" here means every
occurrence in a family beyond the first is counted (family of 7 = 6 duplicates),
matching the plan's "72 duplicates across 41 families" framing (72 = sum over
families of (count-1); 41 = number of families with count >= 2).
"""
import argparse
import re
import sys
from pathlib import Path
from collections import defaultdict

SUBSYS = Path(__file__).resolve().parents[3] / "Cslib" / "Logics" / "Modal" / "Tableau"
# Fallback: resolve relative to repo root if the above guess is wrong.
if not SUBSYS.exists():
    SUBSYS = Path("Cslib/Logics/Modal/Tableau")

# Do-not-edit files are still SCANNED (they may be the origin of a duplicate
# elsewhere) but never a deletion target -- callers must respect the do-not-edit
# list independently of this script.
DECL_RE = re.compile(r"^(?P<priv>private\s+)?(?P<kind>lemma|theorem)\s+(?P<name>[A-Za-z_][A-Za-z0-9_'?!]*)")

SUFFIXES = ["_S5w", "_S4Keyed", "_origin", "_local", "_anc", "_S4", "_S5", "_Five", "_FS", "_B", "_C"]
# NOTE on trailing-prime variants (e.g. `mem_successorsOf_hasEdge'`): a prime-stripping pass
# was trialled and reverted. It correctly caught genuine cross-file duplicates (e.g.
# FrameSoundness.lean's `mem_successorsOf_hasEdge'` vs FmpMeasure.lean's
# `mem_successorsOf_hasEdge`; FrameCompleteness.lean's `modalApplyOneT_boxPos_fst'` /
# `modalApplyOneT_diamondNeg_fst'` vs TDriver.lean's now-public unprimed originals) but ALSO
# pulled unrelated same-base declarations into a shared family purely because they stripped to
# the same base string, even when the primed member itself has no cross-file duplicate at all
# (e.g. FmpMeasure.lean's `mem_modalUniverse_of'` has no copy anywhere, but got merged into the
# unrelated `mem_modalUniverse_of` family because both share the stripped base
# "mem_modalUniverse_of"). Fixing this properly needs per-suffix-flavor grouping (not just a
# cross-file guard), which was judged not worth the complexity here. Primed duplicates are
# instead caught by manual, phase-scoped grep (see phase handoffs) and reported as an explicit
# known gap of this script -- do not assume `census.py`'s count includes prime-named
# duplicates. Cross-check `grep -rn "NAME'" *.lean` for any family with published/reachable
# consequences (Accessibility, KnownWorlds) before declaring a phase's family count final.


def strip_suffix(name: str):
    for suf in SUFFIXES:
        if name.endswith(suf) and len(name) > len(suf):
            return name[: -len(suf)], suf
    return None, None


def strip_comment_state(text_lines):
    """Yields (line_no, code_only_line) with block-comment (/- ... -/, nesting-aware)
    content blanked out, so declaration matching never fires on docstring prose (e.g.
    a doc comment sentence "... lemma is `private` ..." at column 0 must NOT be
    mistaken for a real `lemma is` declaration -- this was an observed false positive
    before this guard was added). Line comments (`--`) are also blanked from their
    `--` marker onward. Does not attempt to special-case string literals; adequate
    for this subsystem's actual content (no `/-`, `-/`, or `--` appears inside a
    Lean string literal here)."""
    depth = 0
    for i, line in enumerate(text_lines, start=1):
        out = []
        j = 0
        n = len(line)
        while j < n:
            if depth == 0 and line[j:j + 2] == "--":
                break  # rest of line is a line comment
            if line[j:j + 2] == "/-":
                depth += 1
                j += 2
                continue
            if depth > 0 and line[j:j + 2] == "-/":
                depth = max(0, depth - 1)
                j += 2
                continue
            if depth == 0:
                out.append(line[j])
            j += 1
        yield i, "".join(out)


def scan_published_names():
    """Names published under Support/*.lean. Used ONLY to keep signal B's "does the base exist
    somewhere" check accurate after an origin has been deleted from the flat driver-file surface
    and relocated to Support/ (e.g. modalKnownWorlds_mono_append's FmpMeasure.lean origin was
    deleted in Phase 5's forced-collision cleanup; the 5 remaining suffixed copies elsewhere are
    STILL a real pending-migration family, but without this check the family would silently
    disappear from the census the moment the origin moved to Support/, since Support/ is not on
    the flat glob(...) driver-file surface scan() reads from -- discovered when Phase 5's
    post-phase census showed an implausibly large drop and cross-checking against a manual grep
    of the known Phase 6 target families revealed the gap.
    Support/ names are NEVER added to `decls` / never appear as family members themselves --
    only used to seed the base-existence check.
    """
    published = set()
    support_dir = SUBSYS / "Support"
    if not support_dir.exists():
        return published
    for f in sorted(support_dir.glob("*.lean")):
        text = f.read_text(encoding="utf-8", errors="replace").splitlines()
        for _, code_line in strip_comment_state(text):
            m = DECL_RE.match(code_line)
            if m:
                published.add(m.group("name"))
    return published


def scan(files=None):
    """Returns list of (file, line, private:bool, kind, name)."""
    decls = []
    lean_files = sorted(SUBSYS.glob("*.lean"))
    if files:
        wanted = set(files)
        lean_files = [f for f in lean_files if f.name in wanted]
    for f in lean_files:
        text = f.read_text(encoding="utf-8", errors="replace").splitlines()
        for i, code_line in strip_comment_state(text):
            m = DECL_RE.match(code_line)
            if m:
                decls.append((f.name, i, bool(m.group("priv")), m.group("kind"), m.group("name")))
    return decls


def census(files=None, family_filter=None):
    decls = scan(files)

    # Signal A: exact-name duplicates across files
    by_name = defaultdict(list)
    for (fname, line, priv, kind, name) in decls:
        by_name[name].append((fname, line, priv, kind))

    # Signal B: suffix-family duplicates (base name declared anywhere, incl. same name w/o suffix)
    all_names = set(by_name.keys())
    # Published Support/ names count as "the base exists" too -- see scan_published_names()'s
    # docstring for why this is load-bearing once an origin has been relocated to Support/.
    published_names = scan_published_names()
    lookup_names = all_names | published_names
    by_base = defaultdict(set)  # base -> set of names (base itself + suffixed variants) present
    base_is_support_only = set()  # bases whose ONLY existence is in Support/, not in all_names
    for name in all_names:
        base, suf = strip_suffix(name)
        if base and base in lookup_names:
            by_base[base].add(name)
            by_base[base].add(base)
            if base in published_names and base not in all_names:
                base_is_support_only.add(base)

    # Union: family key -> set of (fname, line, priv, kind, name)
    families = defaultdict(list)

    # from signal A: any name with >=2 declared occurrences forms its own family
    for name, occs in by_name.items():
        if len(occs) >= 2:
            for (fname, line, priv, kind) in occs:
                families[name].append((fname, line, priv, kind, name))

    # from signal B: suffix families get merged under the base key -- but ONLY when the
    # family spans 2+ DISTINCT FILES. Re-derivation-across-a-privacy-boundary is inherently
    # a cross-file phenomenon (you re-derive BECAUSE you cannot reach the original file); a
    # same-file pair sharing a stripped base (observed for e.g. `mem_modalUniverse_of` /
    # `mem_modalUniverse_of'` both in FmpMeasure.lean, or `mem_modalUniverseS4_of` /
    # `mem_modalUniverseS4_of'` both in LoopChecking.lean) is reliably a legitimate same-file
    # sibling pair (an anonymous-constructor form vs. a generic form, observed by manual
    # audit), not a re-derivation duplicate. Requiring cross-file spread eliminates this
    # false-positive class without losing any genuine cross-file suffix/prime family.
    for base, names in by_base.items():
        if len(names) < 2:
            continue
        candidate_entries = []
        files_seen = set()
        for name in names:
            for (fname, line, priv, kind) in by_name.get(name, []):
                candidate_entries.append((fname, line, priv, kind, name))
                files_seen.add(fname)
        # The cross-file requirement guards against same-file prime-sibling false positives
        # (two DIFFERENT facts sharing a stripped base in one file -- see the module docstring
        # note above). That risk does not apply when the base's ONLY existence is the published
        # Support/ module: Support/ is a distinct file by construction, so even a single
        # remaining driver-file copy is a genuine, real duplicate needing consolidation, not a
        # same-file sibling ambiguity. Require >=2 files only when the base is NOT Support-only.
        needs_two_files = base not in base_is_support_only
        if not needs_two_files or len(files_seen) >= 2:
            for entry in candidate_entries:
                if entry not in families[base]:
                    families[base].append(entry)

    # De-duplicate: an exact-name family that is ALSO absorbed by a suffix-family
    # (shouldn't normally happen since suffix families use the stripped base as key,
    # and exact-name families use the declared name as key) -- but guard anyway by
    # collapsing on the multiset of (fname, line) pairs.
    seen_lines = set()
    final_families = {}
    for key, entries in families.items():
        entries = sorted(set(entries))
        line_ids = tuple(sorted((e[0], e[1]) for e in entries))
        if line_ids in seen_lines:
            continue
        seen_lines.add(line_ids)
        final_families[key] = entries

    if family_filter:
        final_families = {
            k: v for k, v in final_families.items()
            if family_filter in k or any(family_filter in e[4] for e in v)
        }

    return final_families


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--family", default=None, help="restrict to a family/base/name substring")
    ap.add_argument("--files", nargs="*", default=None, help="restrict to these filenames")
    ap.add_argument("--quiet", action="store_true", help="only print the summary line")
    args = ap.parse_args()

    fam = census(files=args.files, family_filter=args.family)

    total_dup_decls = 0
    for key in sorted(fam.keys()):
        entries = sorted(fam[key])
        if not args.quiet:
            print(f"== family: {key} ({len(entries)} declarations) ==")
            for (fname, line, priv, kind, name) in entries:
                vis = "private" if priv else "public "
                print(f"  {fname}:{line}  {vis}  {kind} {name}")
        total_dup_decls += max(0, len(entries) - 1)

    print(f"TOTAL_DUPLICATE_DECLARATIONS={total_dup_decls} TOTAL_FAMILIES={len(fam)}")


if __name__ == "__main__":
    main()
