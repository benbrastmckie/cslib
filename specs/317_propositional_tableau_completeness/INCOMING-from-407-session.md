# Incoming partial fix for phase-6 blocker B2 (from the 407 session)

While implementing task 407's HasInitialBot witness, the agent also partially
resolved a sorry in `Cslib/Logics/Propositional/Tableau/Intuitionistic/Scheme.lean`:
it proved the `notApplicable` case of `intExpandBranches_openBranch_sat` is
unreachable via a new private lemma `intStepBranch_result_not_notApplicable`.

This is OUT OF SCOPE for 407 and IN 317's territory, so it was NOT committed by the
407 session (to avoid a concurrent-edit conflict with this live 317 session). It is
saved as a patch instead:

  git apply specs/317_*/scheme-b2-partial-fix-from-407-session.patch

Review it (git diff after applying), verify it builds, and fold it into 317's
phase-6 work if correct. Discard the patch if 317 has a different/better approach.
