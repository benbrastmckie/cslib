/-
Copyright (c) 2026 Benjamin Brast-McKie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Brast-McKie
-/

module

public import Cslib.Logics.LTL.Semantics.GNBA.Closure
public import Cslib.Logics.LTL.Semantics.GNBA.Atoms
public import Cslib.Logics.LTL.Semantics.GNBA.Construction
public import Cslib.Logics.LTL.Semantics.GNBA.Correctness

/-! # GNBA Tableau Construction for LTL Omega-Regularity

Barrel module re-exporting the GNBA tableau construction split across four submodules.

The construction proceeds in four phases:

1. **Closure** (`GNBA.Closure`): Fischer-Ladner closure `Formula.closure` and
   the subformula membership lemmas.

2. **Atoms** (`GNBA.Atoms`): The atom predicate `Formula.IsAtom` (maximally consistent
   subsets of the closure), finiteness, and canonical atoms from semantic valuations.

3. **Construction** (`GNBA.Construction`): GNBA state type, transition relation, initial
   states, acceptance sets, and GNBA-to-NBA conversion via cycling counter.

4. **Correctness** (`GNBA.Correctness`): Language equality
   `language (gnbaNBA φ) = φ.gnbaOmegaLanguage`.

## References

* [C. Baier, J.-P. Katoen, *Principles of Model Checking*][BaierKatoen2008]
* [M. Y. Vardi, P. Wolper,
  *An automata-theoretic approach to automatic program verification*][VardiWolper1986]
-/
