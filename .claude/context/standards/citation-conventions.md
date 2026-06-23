# Citation Conventions

Standards for bibliographic references in Lean source files. These
conventions follow Mathlib's documentation system with CSLib-specific
naming.

## Canonical Format

External literature citations use the Mathlib BibKey format:

```lean
## References

* [Author Initials. Surname, *Title*][BibKey], location info
```

Every BibKey resolves to an `@book` or `@article` entry in the root
`references.bib` file.

### Examples

Single-author:
```
* [D. Prawitz, *Natural Deduction: A Proof-Theoretical Study*][Prawitz1965]
```

Multi-author with location:
```
* [A. Chagrov, M. Zakharyaschev,
  *Modal Logic*][ChagrovZakharyaschev1997],
  Section 2.2, Proposition 2.1
```

Multi-author, single line:
```
* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
```

### Format Rules

| Element | Convention |
|---------|------------|
| Bullet | `*` (not `-`) |
| Author names | Initials then surname: `A. Chagrov` |
| Title | Italicized with `*...*` |
| Display text | In first square brackets: `[Author, *Title*]` |
| BibKey | In second square brackets: `[BibKey]` |
| Location | After closing bracket, comma-separated |
| Line wrapping | Indent continuation lines by 2 spaces |
| Line length | 100-character limit per line |

### BibKey Naming

CSLib uses CamelCase BibKeys: `Blackburn2001`,
`ChagrovZakharyaschev1997`, `KatzLindell2020`.

Mathlib uses lowercase: `bourbaki1966`, `schaefer1966`. The CamelCase
convention is a deliberate CSLib project choice and is used
consistently.

Format: `{Surname(s)}{Year}` — concatenate author surnames without
separators, append the publication year.

| Authors | BibKey |
|---------|--------|
| Blackburn, de Rijke, Venema (2001) | `Blackburn2001` |
| Chagrov, Zakharyaschev (1997) | `ChagrovZakharyaschev1997` |
| Katz, Lindell (2020) | `KatzLindell2020` |
| Prawitz (1965) | `Prawitz1965` |

## Internal Cross-References

Files may also reference other CSLib source files as implementation
notes. These use a different format:

```
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- description
```

Internal cross-references do not use BibKey format. They point to
files that served as templates, patterns, or related implementations.

## References Section Structure

The `## References` section appears inside the module docstring
(`/-! ... -/`), after other standard sections (`## Main definitions`,
`## Main results`, `## Notation`, `## Implementation notes`).

A file may contain both external citations and internal
cross-references in the same section. External citations come first:

```lean
/-!
## References

* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001]
* Cslib/Logics/Modal/Metalogic/Soundness.lean -- parameterized soundness
-/
```

## Adding New Bibliography Entries

New entries go in the root `references.bib` in alphabetical order by
BibKey. Use `@book` or `@article` with standard BibTeX fields:

```bibtex
@book{AuthorSurname2024,
  author       = {Surname, Given Name},
  title        = {Full Title},
  publisher    = {Publisher Name},
  address      = {City},
  year         = {2024},
  isbn         = {978-...}
}
```

Before adding an entry, verify no duplicate key exists. After adding,
ensure every file that cites the BibKey uses the canonical display
format.

## Current State

The canonical BibKey format is consistently used across Languages,
Foundations, Computability, Crypto, LinearLogic, and HML modules. The
Modal, Bimodal, and Temporal modules contain legacy informal
citations (e.g., `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4,
...)`) that predate the adoption of the Mathlib convention. New files
and citation updates use the canonical format.

### Informal Patterns to Convert

When updating references in existing files, replace these legacy
patterns with the canonical format:

| Legacy pattern | Replacement |
|----------------|-------------|
| `* CZ Section 1.2` | `* [A. Chagrov, M. Zakharyaschev, *Modal Logic*][ChagrovZakharyaschev1997], Section 1.2` |
| `* Blackburn, de Rijke, Venema - Modal Logic (Ch. 4)` | `* [P. Blackburn, M. de Rijke, Y. Venema, *Modal Logic*][Blackburn2001], Chapter 4` |
| `- Burgess 1982: "Axioms for tense logic II"` | `* [J. P. Burgess, *Axioms for Tense Logic II*][Burgess1982]` (add bib entry) |
| `- GHR94, Chapter 10.2` | `* [D. M. Gabbay, I. Hodkinson, M. Reynolds, *Temporal Logic*][GabbayHodkinsonReynolds1994], Chapter 10.2` (add bib entry) |

Also convert dash bullets (`-`) to star bullets (`*`) in reference
sections.
