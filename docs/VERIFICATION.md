# Verification record

Updated 3 November 2026. All local development, candidate, Linux, schema, and
selected-result comparison checks listed here passed.

## Builds and axiom audit

| Check | Evidence | Result |
| --- | --- | --- |
| Integrated development build | [`full-build.log`](../verification/2026-11-02-full-build.log) | 4,328 jobs; exit 0; no warnings. |
| Curated candidate build | [`candidate-build.log`](../verification/candidate-build.log) | 4,328 jobs; passed. |
| Challenge/Solution interface build | [`candidate-interface-build.log`](../verification/candidate-interface-build.log) | 4,332 jobs; passed with exactly five authorized Challenge theorem-placeholder warnings. |
| Global development axiom audit | [`full-axioms.log`](../verification/2026-11-02-full-axioms.log) | 4,978 declarations; only `propext`, `Classical.choice`, and `Quot.sound`. |
| Candidate axiom audit | [`candidate-axioms.log`](../verification/candidate-axioms.log) | 4,978 declarations; only the three permitted axioms. |
| Fresh Linux build and axiom audit | [`linux-build.log`](../verification/linux-build.log), [`linux-axioms.log`](../verification/linux-axioms.log) | Build passed with 4,328 jobs; audit passed for 4,978 declarations. |

## Comparator and input identity

The official command `lake comparator --config comparator.json` passed in the
Linux Bubblewrap namespace sandbox with `enable_nanoda=true`. NanoDa accepted
the Solution, Lean's default kernel accepted it, and Comparator reported
“Your solution is okay!”. See [`linux-comparator.log`](../verification/linux-comparator.log)
and the machine-readable [`linux-summary.json`](../verification/linux-summary.json).
The comparison covers the five selected Introduction theorem exports, including
combined conclusions. It does not claim Comparator results for every library theorem.

Host and staged Linux source matched exactly for all 365 mathematical inputs.
The identity records are [`mathematical-inputs.json`](../verification/mathematical-inputs.json)
and [`linux-input-identity.json`](../verification/linux-input-identity.json).
They also record source, toolchain, dependency-manifest, Lake-target, and
Comparator-configuration identity. Publication documentation and metadata were
updated after the Linux source archive was staged; these 365 mathematical inputs
were rechecked unchanged after verification and before the final local commit.

## Metadata and review

The current official metadata schema check passed; see
[`metadata-schema.json`](../verification/2026-11-03-metadata-schema.json).
The Citation File Format schema check also passed; see
[`citation-schema.json`](../verification/2026-11-03-citation-schema.json).
The Palomar policy and protocol versions used for local preparation are
recorded in [`publication-policy.json`](../verification/2026-11-02-publication-policy.json).

Native source/prose reviews passed. This is not independent human mathematical
review. Source corrections and proof departures SF1–SF6 remain documented in
[`FORMALIZATION_REPORT.md`](../FORMALIZATION_REPORT.md) and
[`MANUSCRIPT_RECOMMENDATIONS.md`](../MANUSCRIPT_RECOMMENDATIONS.md).

## Scope and limits

The source inventory has 85 IDs: 82 completed claims and three open research
questions. The selected five-result Comparator interface verifies the
Introduction statements; the broader library claims are covered by the builds
and axiom audits, not by that Comparator selection.

These records establish local builds, transitive axiom checks, schema
validation, exact input identity, and acceptance of the selected Challenge
Solution by the official Comparator with both kernels. They do not establish a
full Palomar submission pipeline, a public upload or registration, independent
human review, or editorial endorsement. Those external actions are deferred;
they are not outstanding mathematical proof obligations.
