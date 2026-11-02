# Introduction Comparator interface and result

The user authorized exactly five theorem placeholders in the Challenge. The
active `Challenge.lean`, `Solution.lean`, and `comparator.json` select these
exports from `FreezingGrowth.Paper`:

| Paper result | Selected declaration |
| --- | --- |
| Proposition 1.1(i) | `proposition_1_1_i` |
| Proposition 1.1(ii) | `proposition_1_1_ii` |
| Proposition 1.1(iii) | `proposition_1_1_iii` |
| Theorem 1.2 | `theorem_1_2` |
| Theorem 1.3 | `theorem_1_3` |

Theorem 1.2 is one selected theorem export containing its probability and
expectation conclusions. The selected statements preserve their source quantifiers,
same-witness conditions, finite-word model, and terminal-extinction boundary.
`Solution.lean` uses the proved library exports and has no proof holes; the
five authorized placeholders are Challenge-only. The configuration selects no
definitions and permits only `propext`, `Quot.sound`, and `Classical.choice`.
The [Introduction statements](MAIN_RESULTS.md) give the informal result text.

## Result

The official `lake comparator --config comparator.json` run passed on Linux in
Bubblewrap namespaces with `enable_nanoda=true`. NanoDa accepted the Solution,
Lean's default kernel accepted it, and Comparator reported “Your solution is
okay!”. See [`linux-comparator.log`](../verification/linux-comparator.log)
and [`linux-summary.json`](../verification/linux-summary.json). The complete
build and axiom-audit records are in [`VERIFICATION.md`](VERIFICATION.md).

This configuration checks the five Introduction exports. The source inventory
contains 82 completed claims and three open research questions; this selected
Comparator run does not claim to compare every library result. The full
Palomar submission pipeline, upload, and submission remain external actions
and have not been performed.
