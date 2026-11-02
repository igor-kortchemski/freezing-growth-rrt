# Freezing growth for random recursive trees (Lean 4 formalization)

Lean 4 / Mathlib formalization of **Does freezing impede the growth of random
recursive trees?** by A. Brandenberger, S. Briend, H. Cairns, R. Khanfir and
I. Kortchemski, [arXiv:2505.16571v2](https://arxiv.org/abs/2505.16571v2).

> **Local verification status (3 November 2026).** The source inventory contains
> 82 completed claims and three open research questions. Development and
> curated-candidate builds passed (4,328 library jobs); the authorized
> Challenge/Solution interface build passed with exactly five expected
> Challenge placeholder warnings. The global axiom audit passed for 4,978
> declarations. A fresh Linux build and audit passed, and the official
> five-result Comparator run passed under Bubblewrap namespaces; both NanoDa
> and Lean accepted the Solution. Metadata and citation schema checks passed.
> No public upload, Palomar submission, or full Palomar pipeline is claimed.

The paper source is not redistributed here. Obtain `main.tex` from arXiv (v2);
the version formalized has SHA-256
`7b7d6ef6e2200b3129cbd4a74ef45c09fbf758643ce63489bf67f2aef93301f3`.
Line numbers in the coverage record refer to that file.

## Formalized results

The model uses the actual forward random tree: each step attaches to or freezes
a uniformly chosen active vertex. `true` denotes attachment and `false`
denotes freezing; the population starts at one and reaches zero only on the
last step. Height is maximum root distance, including frozen vertices. Precise
signatures are in [`FreezingGrowth/MainStatements.lean`](FreezingGrowth/MainStatements.lean)
and [`FreezingGrowth/PaperResults.lean`](FreezingGrowth/PaperResults.lean).

All 82 non-question claims in the curated source inventory are proved; its
three research questions remain open. This includes the Introduction results,
I2, II1, III1, E4, the Section 2.5 claims, and the cited-results formalizations
listed in the coverage report. The integrated development build and complete
axiom audit passed. The direct E4 characteristic-function proof establishes
the limit without verifying the cited Lodewijks argument. Source corrections
and proof departures SF1–SF6 are recorded in
[`FORMALIZATION_REPORT.md`](FORMALIZATION_REPORT.md) and
[`MANUSCRIPT_RECOMMENDATIONS.md`](MANUSCRIPT_RECOMMENDATIONS.md).

The Introduction comparison selects five theorem exports: Proposition 1.1(i),
(ii), and (iii), combined Theorem 1.2, and Theorem 1.3. This comparison scope is narrower
than the 82 completed claims in the library. See the [Introduction results](docs/MAIN_RESULTS.md)
for the source statements.

## Verification status

The project pins Lean `4.35.0`, Mathlib `v4.35.0`, and the dependency revisions
in `lake-manifest.json`. Development, candidate, Linux, axiom-audit, and
Comparator records are listed in [`docs/VERIFICATION.md`](docs/VERIFICATION.md).
Linux verification confirmed exact identity for all 365 mathematical inputs
between the host and staged Linux source. The final metadata and citation
schema records are linked there as well.

No full Palomar preflight, public upload, or submission is claimed. These are
deferred publication actions, not outstanding mathematical claims. No
independent human mathematical review or editorial endorsement is claimed. See
[`docs/PALOMAR_STATUS.md`](docs/PALOMAR_STATUS.md) for publication status and
[`docs/COMPARATOR_DRAFT.md`](docs/COMPARATOR_DRAFT.md) for the five-result
comparison scope and outcome.

## Local development commands

From the development project root:

```sh
lake exe cache get
lake build
lake env lean scripts/AxiomAudit.lean
```

The axiom audit checks public `FreezingGrowth` declarations transitively and
allows only `propext`, `Classical.choice`, and `Quot.sound`. It does not
establish source fidelity or replace Comparator or independent kernel checks.

## Where to start

| Entry | Purpose |
| --- | --- |
| `FreezingGrowth/MainStatements.lean` | Precise Lean forms of the Introduction claims |
| `FreezingGrowth/PaperResults.lean` | Numbered exports with their source hypotheses |
| `Path`, `Extinction`, `ChoiceSequence`, `ForwardTree`, `ForwardLaw`, `FiniteLaw`, `Height` | Model, admissibility, tree law, and height law |
| `Reverse*` | Reverse forest construction, forward-law equivalence, and deletion comparisons |
| `RRTSplit*` | First-edge split of the recursive tree |
| `Profile*`, `RemoveAttachWitness` | Exact height-profile enumeration and supporting arithmetic |
| `LowPopulationAsymptotic`, `BinomialLowerBound`, `ActiveHeightBernoulli` | Low-population branch of Theorem 1.2 |
| `Scaling*` | Polynomial height-scaling limit under reciprocal-profile hypotheses |

## Licence, provenance, and citation

New Lean code is licensed under [Apache-2.0](LICENSE). [`NOTICE`](NOTICE)
and [`SCALING_PROVENANCE.md`](SCALING_PROVENANCE.md) record adapted
companion code and source hashes. The paper and its sources retain their own
licence and are not included. See [`CITATION.cff`](CITATION.cff) to cite the
formalization and paper separately.

Igor Kortchemski is identified as formalization author and responsible
maintainer. The intended personal repository is
[`igor-kortchemski/freezing-growth-rrt`](https://github.com/igor-kortchemski/freezing-growth-rrt);
it has not been uploaded. AI agents developed proofs and read-only AI reviews
checked selected statements and proof routes. No independent human review or
editorial endorsement is claimed.
