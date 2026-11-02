# Formalization report

Work was paused at the user's request on 29 October 2026 and resumed on
31 October 2026 after the user lifted that pause. A further handover pause was
lifted on 1 November 2026. The 31 October evidence is
recorded in the section "Resumed development" below; earlier sections describe
the 29 October checkpoints and are kept for provenance. The development-time restart notes are not part of this repository.

## Scope and current evidence

The requested scope is every theorem, proposition, lemma, corollary, and
substantive rendered mathematical claim in `main.tex`, prioritizing all
Introduction results and their dependencies. Open questions are classified as
questions. No claim is dropped because it depends on a cited result.

- Paper: **Does freezing impede the growth of random recursive trees?**,
  arXiv:2505.16571v2.
- Source SHA-256: `7b7d6ef6e2200b3129cbd4a74ef45c09fbf758643ce63489bf67f2aef93301f3`.
- Lean 4.35.0; Mathlib v4.35.0, exact revisions in `lake-manifest.json`.
- Intended repository name: `freezing-growth-rrt`; new Lean code: Apache-2.0.
- Destinations: GitHub and Palomar. The user will handle upload once the
  deliverable is ready. Nothing has been published or submitted.
- Current state: **all 82 non-question inventory obligations complete, with documented source corrections SF1–SF6**.
  All three assertions of Proposition 1.1, including the same-witness freezing-only
  consequence, and Theorems 1.2 and 1.3 are proved. The analytic proofs avoid the
  numerical witness computation. Proposition 1.1(iii)'s eventual strengthening
  and accompanying non-domination are also proved. The other retained source
  obligations are now covered: 82 of the 85 inventory items are complete, 0 partial, 0 pending, 3 are
  open questions (counted from the tables below by their coverage cell).

The source-first inventory below was independently prepared by the
`paper_inventory` reviewer on 29 October 2026, reading all of `main.tex` and its
macros. It includes the unnumbered displays, footnote, and quantitative claims
inside the open-question section. Its coverage column records current status;
initial review alone is not proof evidence.

## Verified completion milestone — 2 November 2026

All 82 non-question inventory obligations are complete in the explicitly
recorded source-faithful or corrected forms; Q1–Q3 remain open research questions.
The source SHA-256 is unchanged. Independent source-first reconciliation found
all 85 unique IDs and no omitted rendered mathematical claim. Printed errors
SF1–SF6 retain their qualifications: this is not certification of false literal
printed formulas. Earlier dated sections below are historical evidence.

- Full integrated `lake build`: **4,328 jobs**, no warnings, exit zero.
- Global axiom audit: **4,978 declarations**, only `propext`, `Classical.choice`,
  and `Quot.sound`, exit zero.
- Evidence: `verification/2026-11-02-full-build.log` and
  `verification/2026-11-02-full-axioms.log`; focused E4 and graft logs are retained.
- Independent native final source/body reviews PASS for I2, II1, III1 and E4;
  the unchanged earlier 78 inventory reviews are reused. Claude Sonnet 5.5 High
  additionally reviewed III1's design after explicit user authorization.
- I2/II1 now include exact entire word histories and their literal shared prefix;
  III1 has the actual nested master trees and birth-ordered full grafts.
- E4 uses a direct recurrence/characteristic-function argument; the cited proof
  by Lodewijks is not claimed checked.

Local publication preparation continues. Candidate-only verification,
Comparator, independent kernel replay and full Palomar verification must be
reported separately; none follows merely from these build and axiom results.
No upload, submission or registration has occurred.

## Curated publication candidate — 2 November 2026

The local `freezing-growth-rrt` candidate exports the entire verified import
closure, including the nested `PWIT` modules. Its fresh library build passed
with **4,328 jobs**, followed by a successful **4,332-job** library/interface
build and a **4,978-declaration** global axiom audit. The only interface warnings
are the five explicitly authorized theorem placeholders in `Challenge.lean`.
All actual proofs remain hole-free and permit only the three standard axioms.

The independently reviewed Comparator interface selects the Introduction's
Proposition 1.1(i), (ii), (iii), combined Theorem 1.2 and Theorem 1.3. Five
exports are not five inventory rows: some conclusions are combined. The full
82-claim library remains built and audited. Independent source-fidelity and
informal-account reviews passed for this selected interface. On 3 November (local time), the fresh Linux build passed with 4,328 jobs
and its global axiom audit passed for 4,978 declarations. Official sandboxed
`lake comparator --config comparator.json` accepted all five selected results;
both NanoDa and Lean's kernel accepted the exported Solution. All 365
mathematical input files match the macOS-tested candidate and staged Linux
source exactly. The raw logs and input identity record are retained under
`verification/`; final publication documentation was then updated without
changing those mathematical inputs. No full Palomar verification, human review
or public submission is implied.

## Historical development and checks (through 1 November 2026)

`Path.lean`, `Extinction.lean`, `ForwardTree.lean`, and `ForwardLaw.lean` under
`FreezingGrowth/` are self-contained adaptations of the local `freezing1`
companion's Apache-2.0 forward model. Source hashes and adaptation details are in
`NOTICE`. The copied models use persistent birth-time vertex identifiers and
retain freezing times; the paper's binary labels are recovered by whether a
vertex remains active. The induced finite graph is proved to be a tree, and
stored heights are proved equal to root distances. The transition measure is
uniform on active vertices conditional on the current state; it is not uniform
on depth levels or unlabeled tree shapes.

Last integrated checkpoint (29 October 2026; before the follow-up below):

- `lake build` passed with **3,733 jobs**, without warnings. The root module
  imports all **30 mathematical modules**; no mathematical source is orphaned.
- `lake env lean scripts/AxiomAudit.lean` passed for **434 project declarations**.
  Every transitive axiom belongs to `propext`, `Classical.choice`, or `Quot.sound`.
  The probe also prints the axiom closures of the principal numbered, low-branch,
  representation, endpoint, profile, and normalized-depth exports explicitly.
  Its final `#check` queries confirm the elaborated corrected E5 and surviving-
  prefix representation statements, with no additional asymptotic premise.
- A source scan found no proof holes, custom axioms, `native_decide`,
  `bv_decide`, or unsafe declarations in the mathematical library. This scan
  complements the actual transitive axiom check; it is not its substitute.
- Independent `paper_inventory` reviews passed the implemented statements and
  their proof routes, including exact minima, extinction endpoints, first-peak
  counts, active-depth representation, low-branch limits, height-profile law
  projection, and corrected uniform-depth convergence. The six Introduction
  target definitions also passed statement review; they remain unproved.
- The source inventory was reconciled after the milestone: all **85 IDs** remain,
  including the three explicitly open questions. `main.tex` retains the source
  hash recorded above.

Scoped kernel replay also passed (exit 0) for `PaperResults`,
`LowPopulationAsymptotic`, `ActiveHeightBernoulli`, `RRTUniformDepth`,
`HeightProfile`, and `FiniteActiveHeight`, using the sequential command
`lake env leanchecker --verbose FreezingGrowth.<module>` for each named module.
This replays each module against its imported environment with the same Lean
kernel; it is distinct from a fresh independent kernel, Comparator, or Palomar's
full mechanical report. All nine dependency checkout revisions match the locked
manifest, and their tracked source files are unchanged.

The infinite schedule's extinction time is used only through comparisons at a
finite horizon. Its raw value is not identified with the paper's truncated
stopping time; the distinction is documented in `Extinction.lean`.

## Follow-up development after the integrated checkpoint

Work continues toward the complete inventory. The preceding full-build and
434-declaration audit describe the earlier integrated snapshot, not every new
working module. The full build and axiom audit were rerun on 31 October 2026 and now cover these additions (see Resumed development below).

- `AlternatingHeight` and `AlternatingHeightBounds` passed the focused build
  `lake build FreezingGrowth.AlternatingHeight` (3,717 jobs, no warnings).
  `alternating_height_tendsto_half` states the actual finite-word height law,
  normalized by its attachment/edge count, with no extra asymptotic premise.
  Root independently reviewed the statement and finite-tail proof route.
- All 33 adapted reverse-equivalence modules and `ReverseHeightBridge` compiled,
  including `CanonicalTree.reverseStateLaw_eq_forward_treeLaw` and actual
  maximum-height transport at the weak horizon $m\leq\tau$. The ordered-list
  process, its uniform position-pair kernel, and its actual terminal-height
  bridge also compiled. The singleton-insertion comparison is under development.
  The repair to
  reachable-history support concerns the cited/companion equivalence argument,
  not a proof printed in this manuscript.
- `ProfileCode` and `ProfileCompute` compiled cleanly. A structural merge/sort
  implementation preserves every weighted observable and passes kernel-only
  `decide +kernel` examples at sizes 1, 2, and 3; their axiom closures contain
  only `propext`. The original core merge reduction got stuck on its accessibility
  recursor already at size 2. The large $n=13$ certificate remains pending.
- `ProfileEnumeration` and `RemoveAttachWitness` compiled cleanly: the integer
  table now has a proved normalization and expected-height identity for every
  word, including extinction. The latter module's strict comparison explicitly
  assumes the two still-pending numerical certificates; it is not M1iii.
- `BernoulliOrder`, `BinomialSum`, `ActiveHeightOrder`, and `BinomialLowerBound`
  compiled cleanly. The actual independent product sum is identified with
  Mathlib's binomial law, giving D2 with terminal extinction included. Independent
  source and proof-route review passed; covered by the 31 October 2026 integrated build and audit.
- All 20 scaling modules compiled cleanly. Both operation-index and actual
  vertex-count versions of E9 have passed exact-type and transitive-axiom probes,
  using only the permitted axioms. The vertex normalization includes the factor
  $2^{1-\alpha}$. The user authorized Apache-2.0 for the local reused proof code;
  exact provenance is in `SCALING_PROVENANCE.md`.
- `HeightMonotonicity` and `HighPopulationReduction` compiled. The latter proves
  the corrected $r-1$ comparison conditional on `FirstPairDeletionClaim`; that
  hypothesis is explicit and still unresolved. `HighPopulationCentering`'s
  explicit logarithmic margin and its divergence also passed a focused build;
  no RRT height estimate is assumed by those analytic lemmas.
- `RRTStarProbability` proves the actual height-one probability $1/n!$ for
  every $n\geq1$. Its focused build and independent statement/route review
  passed. The alternating star formula and Observation 2.1 are being added.

## Resumed development (31 October 2026)

The saved focused batch was run first. Its failures were repaired in place
(implicit and shadowed names, `rw` hitting the wrong sum, a keyword used as a variable
name, deprecated lemma names, a kernel timeout from `rfl`-style unfolding in
`map_runBackward_replicate_true`), and then the whole batch compiled:
`ReverseHeightDynamics`, `ReverseHeightRecursion`, `ReverseSingletonInsertion`,
`ReverseFirstPairDeletion`, the eight `RRTSplit*` modules ending in `RRTSplitLaw`,
`RRTStarProbability`, `AlternatingStarProbability`, `HeightExpectationOrder`,
`HighPopulationCentering`, `ProfileEnumeration`, `ProfileTailStatistics`.

Verified results (statement, semantic bridge and proof checked; see the coverage rows):

- **Theorem 1.3 (M3)**, `FreezingGrowth.firstPairDeletionClaim` / `Paper.theorem_1_3`.
- **Observation 2.1 and the star probabilities** (O1–O4).
- **First-edge split of the recursive tree** (E3), and E6 as a law identity.
- **Unconditional corrected high-population reduction** (H2):
  `Word.high_population_domination` no longer takes the M3 premise.
- `Word.HeightLE.expectedHeight_le`: upper-tail domination implies mean comparison.
- **Q3a**, the lower bound $\liminf N_n/(n\log_2 n)\geq1$ asserted in open question (3):
  `question3_lowerBound` / `Paper.question_3_lower_bound`. Q2a (that the thresholds $h_n\to\infty$)
  needs genuinely new probability estimates for small heights and remains pending.

Current mechanical evidence, all on the tree as of 31 October 2026 (macOS, Lean 4.35.0,
Mathlib v4.35.0, nine locked packages):

- `lake build`: **3,958 jobs, no warnings**, exit 0. The root imports the new
  modules, so the build covers them.
- `lake env lean scripts/AxiomAudit.lean`: **2,083 `FreezingGrowth` declarations checked;
  every transitive axiom is `propext`, `Classical.choice` or `Quot.sound`.** The
  script also prints the closures and elaborated types of the new exports.
- `lake env leanchecker --verbose FreezingGrowth.<module>`, run one module at a time,
  passed (exit 0) for `ReverseHeightDynamics`, `ReverseSingletonInsertion`,
  `ReverseFirstPairDeletion`, `HighPopulationDomination`,
  `AlternatingStarProbability`, `RRTSplitLaw`, `Question3Bound`, `ProfileChunk` and `PaperResults`. This replays each
  module against its imported environment with Lean's own kernel; it is not an
  independent verifier, not Comparator, and not Palomar's report.
- The curated publication candidate (`scripts/export_candidate.sh`, 128 modules, excluding the unfinished
  certificate) was built from its own files: `lake build` 3,958 jobs, exit 0, no warnings, and the same
  audit (2,083 declarations, permitted axioms only). Dependencies were copied copy-on-write from this
  tree at the locked revisions, so this is not a clone of a public snapshot, not Comparator, and not
  Palomar's preflight.
- Independent read-only statement and proof-route review of M3, E3, O1–O3, the expected-height
  comparison and H2, by a separate AI agent that did not write the declarations and ran
  no compiler (it read the source before the Lean). Verdicts: M3 statement PASS and
  proof route PASS-WITH-NOTES; E3 statement PASS-WITH-NOTES (law identity only,
  exchangeability not separately exported) and proof PASS; Observation 2.1 and the star
  probabilities PASS; the expected-height comparison and H2 PASS. It found no
  mathematical error. The review preceded the compile evidence above; the two are
  complementary, neither replaces the other. These are AI reviews, not human review.

**Proposition 1.1(iii), existential form.** `RemoveAttachWitness` reduces the claim to two
exact integer statistics at `n = 13`, with the long word `[true,true,false] ++ replicate 13 true`
(mass 523069747200, height weight 2493235880606) and the short word
`[true,false] ++ replicate 13 true` (mass 12454041600, height weight 59460503672). The
exact integer enumeration is tied to the actual forward law by `ProfileEnumeration`. An
exact Python enumeration (a development-time script `exploration/prop_1_1_iii.py` that is not included here) reproduces these numbers
and shows that the reversal first occurs at `n = 13` (it fails for `n = 11, 12`); this
is not proof evidence. `ProfileWitnessCertificate.lean` (generated, 217 lines) states the two kernel certificates
and the final `removeAttachClaim`, but it has **never completed a kernel check**: the run was
stopped at the user's request on 31 October 2026 after about 63 CPU-minutes, and the
user will return to Proposition 1.1(iii) later. Earlier attempts hit the machine's memory
limits (one declaration holding both enumerations used over 12 GB within 5 minutes, and swap
was about 17 of 18 GB full). The present file therefore cuts each enumeration into blocks
of 32 prefix rows using the compiled generic lemmas of `ProfileChunk`
(`runFrom`, `weightedSum_runFrom`, `statistics_run_two_attach_split`, `weightedSum_chunks`;
built cleanly), and its block values come from a compiled `#eval` that reproduces both
target pairs exactly (exploration only, not proof evidence). Calibration at `n = 9, 10`
took about 5 s and 13 s. This describes the historical computational attempt.
The paper's original route uses E1 (still open) and corrected E5 (already proved).
Neither the existential statement nor III10 intrinsically requires E1: the
strategy review below gives alternative routes. The chunked profile file is no
longer the recommended restart point. The
certificate module is deliberately **not** imported by the root and is not exported;
`M1iii` stays Pending and nothing in this report counts it as proved.

Module-system note: `List.orderedInsert` has no exposed body in `module` files, so kernel
computation on profile codes got stuck there. `ProfileCode.attach` now uses the exposed,
provably equal `ProfileCode.insertSorted` (`insertSorted_eq`); all dependent proofs were
adapted and re-verified by the full build and audit above.

## Strategy review after Claude (31 October 2026)

At the user's request, this milestone audits the resumed work and prepares
bounded tasks for a later run at lower reasoning effort. It does not claim a
new completed main result. The detailed execution plan is `ROADMAP.md` in the
development tree; the independent mathematical review is
`verification/III_ROUTES_REVIEW.md`. These working notes and probes are not part
of the curated publication export.

Fresh checks on the current integrated tree passed: `lake build` (3,958 jobs)
and `lake env lean scripts/AxiomAudit.lean` (2,083 declarations, permitted axioms
only). `main.tex` retains the recorded SHA-256. The earlier scoped kernel
replays were not rerun here. No fresh candidate export, Comparator or Palomar
verification is claimed. No mathematical library proof body changed during
this strategy milestone.

The recommended alternative for **M1iii** is analytic. Write $a_n=\mathbb E H(R_n)$.
The already proved maximum-height MGF bound and Jensen give
$a_n\leq\log(n+1)+1+(e-1)\operatorname{heightScale}(\mathrm{allAttach},n)$,
so $a_n=o(n)$. Telescoping then yields arbitrarily large $n$ with
$a_{n+1}-a_n<1/24$. Once the actual seeded-growth/mixture expectation bridge
and exchangeability are proved, III7 gives strict reversal for such an $n\geq2$.
This avoids a finite witness and the sharp height estimates. The generic
telescoping helper in `exploration/SublinearIncrement.lean` compiles with only
permitted axioms; the actual RRT mean upper bound and mixture bridge are still
unproved. This route does **not** prove the eventual comparison III10.

For III9/III10, an independently reviewed but unformalized alternative uses
$u_n=\mathbb E[(2/5)^{H(R_n)}]$ and the larger first-edge component to prove
$u_n=O(1/n)$. This gives a height lower tail above $(21/20)\log n$; corrected E5
then proves the vanishing expected increment. Thus E1 is not a necessary
dependency of III10, although the source uses it. E1/E2/E4 remain in scope in
their own right and for other results.

A finite fallback is also feasible: `exploration/rrt_height_dp.py` constructs
only the height CDF counts, using 225 table entries and 1,470 recurrence
summands. `exploration/RRTHeightTableCertificate.lean` verifies the table
recurrences, the two mean numerators, the split-height tie numerator and the
positive common-denominator gap 4105273618 by `decide +kernel`. Command:
`/usr/bin/time -p lake env lean exploration/RRTHeightTableCertificate.lean`;
exit 0, 14.29 seconds elapsed, 4.29 user, 8.05 system, with existing caches and
default proof budgets. The five inspected numeric exports use only `propext`.
After writing its object file under `.lake/build/lib/lean/exploration/`, the
scoped replay `lake env leanchecker --verbose exploration.RRTHeightTableCertificate`
also passed (exit 0; 30.88 seconds elapsed, 5.57 user, 22.18 system). This uses
Lean's own kernel against the imported environment, not an independent verifier.
This is a kernel-checked arithmetic artifact, **not** a proof of M1iii: its
connection to the actual RRT CDF and frozen-word expectations is missing.
It does not discharge the old `ProfileCompute.statistics` premises merely by
producing the same numbers. The probes remain outside the root import closure.

Independent read-only mathematical review by `review_iii_routes` passed the
three proof plans with these limitations; no compiler was run by that reviewer.
It also confirmed two inventory corrections: III2 is already covered by
`RRTSplit.treeLaw_height_split` and `Describes.height_eq`; E3 remains partial
because its listed exchangeability corollary has not been exported, despite
the complete joint-law identity. All 85 IDs are retained. Source and scope are
unchanged; the earlier source-wide inventory is reused, with this targeted
review of the changed routes and affected dependencies. This is an AI review,
not a human review or a review of future Lean statements not yet written.

## Roadmap implementation (31 October 2026)

**P1–P5 are implemented and integrated. Proposition 1.1(iii) is proved.**
The numbered export is `Paper.proposition_1_1_iii : RemoveAttachClaim`.
`removal_reversal_arbitrarily_late` additionally gives witnesses beyond every
index; it does not assert reversal at every sufficiently large index.

The new proof chain is explicit:

- `RRTMeanUpper` proves the logarithmic mean upper bound by Jensen and the
  existing forward MGF, its sublinear limit, affine upper bounds, and arbitrarily
  late small increments using `SublinearIncrement`.
- `RRTSplitSymmetry` proves exchangeability of the actual full component pair
  after forgetting the tag, and the height-tie mass bound $1/2$.
- `SeededHeightGrowth` proves the occurrence-weighted transition identities.
  `SeededHeightLaw` identifies one/two-seed growth with actual RRT laws.
  Cardinalities and validity for the two-component kernel are discharged using
  the actual first-edge split support, rather than assumed for an arbitrary
  tagged state. The initial frozen maximum is retained.
- `SeededWordLaw` proves suffix continuation for the actual finite word law,
  and the small prefixes' profile mixtures using kernel-checked tables of two
  or three steps. `RRTSplitIntegrals` and `SeededHeightExpectation` supply the
  finite-support integrability and genuine expectation bridges.
- `RemoveAttachMixture` proves both exact word means and III7 with the corrected
  scalar identity. `RemoveAttachAnalytic` proves admissibility for variable $n$,
  chooses $n\geq2$ with mean increment $<1/24$, bounds the factorial correction
  by $1/36$, and obtains strict reversal. No $n=13$ certificate is used.

Current mechanical evidence:

- `lake build`: **3,968 jobs**, exit 0, no warnings. All 138 mathematical
  modules in the root import closure are covered. The only mathematical source
  outside that closure is the historical `ProfileWitnessCertificate.lean`.
- `lake env lean scripts/AxiomAudit.lean`: **2,169 declarations**, exit 0;
  every transitive axiom belongs to `propext`, `Classical.choice`, `Quot.sound`.
  The exact type of the numbered export and the stronger late-witness theorem
  are printed, together with the axiom closures of the new semantic bridges.
- Scoped replay with `lake env leanchecker --verbose`, explicitly targeting
  `FreezingGrowth.SeededHeightGrowth`, `SeededHeightLaw`, `SeededWordLaw`,
  `RemoveAttachMixture`, `RemoveAttachAnalytic`, `RRTMeanUpper`,
  `RRTSplitSymmetry` and `PaperResults`, passed (exit 0). These are same-kernel
  replays against each module's imported environment, not an independent
  verifier or a complete replay of all 138 modules.
- The source remains unchanged at the recorded SHA-256. No source or scope
  change occurred; all 85 inventory IDs are retained. The current count is
  **36 complete, 13 partial, 33 pending, 3 open questions**.
- Independent read-only review by `review_iii_routes` passed the P1/P2 statements
  before dependent work, the P3 seed interfaces, and the final P3–P5 source and
  proof route. The reviewer read the actual code, checked the genuine-law
  identifications, multiplicities, frozen maxima, integrability, indexing and
  absence of additional premises. The record is
  `verification/ROADMAP_IMPLEMENTATION_REVIEW.md` (development file). This is
  an AI review, not a human review; it does not replace the mechanical checks.

**Proof departure and retained scope.** The proof checks the source's finite
height algebra, actual mixture, exchangeability and expectation comparison, with
SF1 corrected. For the existential conclusion it replaces the source's sharp
height/depth argument and vanishing-increment limit by sublinear mean growth
and telescoping. III9 and III10 remain open, as does III11. The height/profile
greffe laws do not supply the complete labelled-tree coupling construction of
III1; that row is partial. E1/E2/E4 and the original M3 pathwise coupling remain
retained obligations. The current curated export has not been regenerated or
reverified at this milestone; previous export evidence is historical. No new
Comparator or Palomar evidence, publication or upload is claimed.

## Eventual comparison and non-domination: A1–A3 (31 October 2026)

**The remaining analytic claims III9–III11 are now proved.**
`Paper.proposition_1_1_iii_eventually` states reversal for every sufficiently
large index, and `Paper.removal_not_stochastic_domination` states the source's
non-domination for every $n\geq1$.

The negative-moment route uses $q=3/7$, refining the roadmap's initial $2/5$
choice so that it covers the **exact** threshold $1.1\log n$ printed in the
source. `LargerComponentSum` groups the two uniform split orientations by their
larger component (choosing the root side in a tie). `RRTNegativeMoment` proves
the actual moment recursion, using the genuine first-edge split law and product
marginals. `HalfHarmonic` proves the harmonic-window limit and eventual
contraction with coefficient $(10/7)\log2<1$; strong induction in
`RRTNegativeMomentBound` gives a single positive $C$ with

$$
\mathbb E[(3/7)^{H_n}]\leq\frac{C}{n+1}\qquad(n\geq0).
$$

`RRTWeakLowerTail.height_lower_tail_tendsto_zero` applies Chernoff to obtain
$\mathbb P(H_n\leq(11/10)\log n)\to0$. The exponent inequality
$(11/10)\log(7/3)<1$ is proved. `RRTHeightIncrement` proves the actual transition
mean identity and bounds the deepest-parent fraction by this height lower tail
plus the existing E5 upper tail. It proves convergence of **all** mean
increments, rather than only a subsequence.

`RRTDeepestParent.depthHeightLaw` samples the depth of a conditionally uniform
parent together with the height of the **same** sampled tree. Its first marginal
is the actual uniform-vertex depth law. The exact identity
`meanHeight_increment_eq_deepest_probability` expresses the mean increment as
the mass of the diagonal. No independence between the two coordinates is
asserted or used. `RemovalEventually` combines the limit with III7 and the
factorial correction to prove III10.

`RemovalStarProbability` proves both height-one masses and the failure of
domination at upper-tail threshold two. The proof uses the genuine small-prefix
laws and seeded continuation; it explicitly excludes height zero and excludes
two zero-height components when their total edge count is positive. The masses
are $1/(2n!)$ and $1/(3(n+1)!)$ for $n\geq1$; their false $n=0$ extensions are
not claimed.

Fresh integrated evidence:

- `lake build`: **3,977 jobs**, exit 0, no warnings.
- `lake env lean scripts/AxiomAudit.lean`: **2,230 declarations**, exit 0; only
  `propext`, `Classical.choice`, `Quot.sound`. Exact types and transitive axiom
  closures of the new source-facing exports and semantic bridges are printed.
- A scan of all nine new mathematical modules found no holes, custom axioms,
  unsafe declarations, native evaluation tactics or debugging traces.
- Sequential scoped replay with
  `lake env leanchecker --verbose FreezingGrowth.<module>` passed (exit 0)
  for `RemovalStarProbability`, `HalfHarmonic`, `LargerComponentSum`,
  `RRTNegativeMoment`, `RRTNegativeMomentBound`, `RRTWeakLowerTail`,
  `RRTHeightIncrement`, `RRTDeepestParent` and `RemovalEventually`, one module
  at a time. These use Lean's own kernel and each imported environment; they
  are not an independent verifier or a full replay of all 147 modules.
- All 85 source inventory IDs are retained: **39 complete, 12 partial,
  31 pending, 3 questions**. The manuscript SHA-256 is unchanged.

Independent read-only source/statement/proof-route review by `review_iii_routes`
passed A3, the revised $q=3/7$ interfaces, and the final A1–A2 implementation.
It checked the tie orientation, uniform constant, induction domain, actual
conditional laws, same-tree coupling and exact eventual conclusion. This is
an AI review, not human review; no Lean/Lake was run by the reviewer. The record
is `verification/EVENTUAL_REMOVAL_REVIEW.md`.
This milestone checks the source's weak lower-height step at $1.1\log n$, the
same-tree parent identity and subsequent limit/comparison. It supplies a
different proof of that weak step, **not** the source's cited sharp height
theorems E1/E2. The full labelled-tree grafting couplings III1/I2, E1/E2/E4 and
the other pending obligations remain in scope. The curated export has not been
regenerated at this milestone; no Comparator, Palomar or upload result is claimed.

## Proof departures and candidate repairs

- Bennett concentration is proved by a direct exponential-moment/Chernoff
  argument. The paper states the result and cites Boucheron–Lugosi–Massart; that
  book's argument has not been checked here.
- The finite scalar identity behind the incorrect `C`-case term is proved
  in corrected form, along with a counterexample to the printed term. The
  probability/profile law feeding the integrated identity is now proved by
  `SeededHeightLaw`, `SeededWordLaw` and `RemoveAttachMixture`. The full labelled-
  tree coupling surplus remains in III1.
- Exact integer-history exploration suggests a finite witness `n = 13` for
  Proposition 1.1(iii). It is not a Lean proof and is not counted as coverage.
  The historical full-profile certificate remains unverified and unused.
  Both the existential and stronger eventual conclusions are now proved
  analytically; this numerical experiment is not required for their coverage.
- Terminal freezing preserves the full height law. The endpoint wrapper now
  combines this with an independently proved forward Bernoulli-sum identity;
  no active vertex is sampled after extinction.
- The low-population branch is proved directly through the forward mean and
  MGF recursion, using the real cap $n/(3\log n)$. The exact-floor bridge is
  also proved. The paper's separate binomial stochastic-domination claim D2 is
  now also proved by coordinatewise monotonicity of independent Bernoulli sums.
  This verifies that step without changing the existing direct proof.
- The active-depth Bernoulli identity is proved by matching the actual forward
  recursion to finite independent product sums. It does not rely on the cited
  reverse construction.
- Corrected E5 is proved from actual uniform-vertex MGF concentration and the
  harmonic-number asymptotic in Mathlib. The paper's missing normalization is
  repaired, and the last-inserted/uniform-vertex citation gap is avoided. This
  does not formalize Devroye's record-count or central-limit arguments.
- `HeightProfile` proves a genuine projection of the forward law to active-depth
  multiplicities and the maximum over all vertices. The exploratory integer
  enumeration has a verified evaluator-to-law bridge. Its large historical
  computational certificate remains unfinished and is not used by the proved
  analytic counterexample or eventual comparison.
- E9 is adapted from the local `freezing2` proof and selected `freezing1`
  analytic lemmas. It uses actual forward maximum-height MGF estimates and
  reciprocal-profile integration. It verifies the cited height conclusion
  under its global reciprocal $L^1$ hypothesis, without needing the stronger
  local $L^2$ hypothesis. It does not check the cited paper's reverse-process
  proof. The new actual-vertex normalization wrapper is proved here.
- **Theorem 1.3 (M3) is proved by a different route from the paper's.** The proof is a
  recursion on the number of reverse-forest components: adding an isolated zero-height
  component can only increase every upper tail of the final maximum height
  (`finishLaw_tail_le_prepend_zero`). The first uniform ordered pair is split into
  avoiding the added singleton (exact mass $(r-1)/(r+1)$, zero when $r=1$) and hitting it;
  the hit case is a componentwise comparison, the receiver orientation up to a proved
  permutation invariance, and the avoidance case is the induction hypothesis. Three
  departures: (1) it replaces Algorithm 3's pathwise coupling (the stored delayed pair
  and the invariants M_i, E_i) by a law-level argument, which is all the stochastic
  domination needs, so the paper's pathwise assertions C2–C7 and the SF6 delayed-pair
  filtration are bypassed, not verified; (2) the paper's ordering bookkeeping is replaced by
  permutation invariance of the coalescence law; (3) the cited reverse/forward
  equivalence (BBKK23+ Theorem 8) is proved here (`reverseStateLaw_eq_forward_treeLaw`)
  instead of being cited.

## Verification and publication obligations

The mathematical inventory remains open as indicated below. In particular,
the delayed-pair coupling, sharp RRT maximum-height asymptotic, and joint-depth
CLT remain open. Forward/reverse equivalence has passed focused builds; the normalized
uniform-depth law of large numbers is proved separately. These are not axioms or
hypotheses smuggled into a claimed main theorem.

The next main-result dependencies are explicit:

1. M1i/M1ii need the grafting/split couplings, exponential RRT height estimates,
   the two-vertex depth limit, and the divergent-gap argument.
2. M1iii and its eventual strengthening III10 are proved, as are III9 and III11.
   The existence proof uses sublinear mean growth and telescoping; the eventual
   proof uses a proved negative-moment bound, the weak lower tail at $1.1\log n$
   and the actual deepest-parent identity. None supplies the sharp E1/E2 input
   needed by the other main results. The complete tree-level coupling in III1
   remains partial.
3. M3 is proved (Resumed development). The paper's delayed-pair construction with the
   correct filtration (C2–C7, SF6) is bypassed by the law-level route and remains a
   separate retained obligation.
4. M2p/M2e now have the stochastic deletion theorem and the corrected high-population
   reduction. The high-effort plan below identifies a weaker sufficient input:
   constant positive success near the regularized $e\log n-2\log\log n$ center,
   amplified through E3 to a bounded expected lower deficit. This input is still
   unproved. The low-population conclusions are already proved uniformly;
   full E1/E2 remain separate retained obligations.

All remaining non-main claims, including the cited joint depth limit and Q2a, remain
in the inventory with their exact status. Q3a is proved.

Publication still requires, beyond the mathematics above, a small independent
Challenge/Solution interface, Comparator, clean-checkout verification, and Palomar's
full mechanical report. The default Comparator sandbox requires Linux; this macOS
build cannot establish that check. The Challenge needs an authorization for
deliberate placeholder proofs that this project has not been given, or a hole-free
Challenge whose proofs fit its size limits (see `docs/PALOMAR_STATUS.md` in the
publication candidate). The repository owner and final human-maintainer metadata are
unspecified. The local candidate is not ready for upload.

## M2 proof design (31 October 2026; planning only)

M2_ROADMAP.md (development record, not included in this export) records a new route for the high-population
branch. A constant positive success probability around
$b_c(n)=e\log(n+1)-c\log(1+\log(n+1))$, for $0\leq c<5-e$, suffices.
The planned discrete amplification uses the actual E3 independent component
laws: at least half the split indices leave both component vertex counts at
least a quarter of the total. It gives a geometric lower tail on a fixed grid,
then a uniformly bounded expected positive deficit. The corrected cutoff
$r_n-1$ leaves a divergent gap with coefficient $5-e-c$; choose $c=2$.
This supplies both main conclusions once the new seed bound is proved.

The chosen seed route is a specialized exponential-clock branching model,
identified with a geometric mixture of the existing RRT height laws through
a first-birth renewal equation. The substantial missing estimate is a
barrier-constrained second moment, with a fixed source version and separate
implementation lots. Neither a first-moment count nor the current weak tail
at $1.1\log n$ supplies it. No new probabilistic premise has been added to
`MainStatements` or `PaperResults`.

Independent mathematical design review is recorded in
[verification/M2_ROADMAP_REVIEW.md](verification/M2_ROADMAP_REVIEW.md).
`lake env lean exploration/HighPopulationInterfaces.lean` exited 0 and checked
the candidate proposition definitions. It proves **none** of those estimates.
The probe is outside the library import closure; production Lean sources,
toolchain, dependencies, and `main.tex` were not changed in this milestone.
No new full build, axiom audit, kernel replay, Comparator or Palomar result
is claimed. The prior integrated evidence remains the A1–A3 milestone above.

Coverage remains **85 IDs: 39 complete, 12 partial, 31 pending, 3 open
questions**. In particular, M2p/M2e remain partial, E1/E2 remain pending,
and H3's sharp asymptotic subclaim remains unresolved. The plan's weaker
inputs must not erase those obligations. The source/scope are unchanged;
the review is local to M2 and its affected dependencies. Finding SF7 records
a citation mismatch in PS22; AF13 remains a valid source for the stated sharp
result. GitHub and Palomar upload remain deferred.

## M2 lot B1 implemented (31 October 2026)

`RRTLowerCenter` defines the accepted regularized center and the expected
positive deficit under the actual RRT height law. It proves the logarithmic
center loss under restriction to a smaller component, the quarter-size bound
$e\log4$, deficit integrability and nonnegativity for every real coefficient
and every size. No probabilistic lower bound is assumed or proved here.

`HighPopulationWeakCentering` proves the quantitative corrected-index gap
for every $c\geq0$, and its divergence when $c<5-e$. The coefficient-two
specialization retains the strict margin $3-e>0$. The previously private
ratio lemma in `HighPopulationCentering` is now publicly available as
`eventually_populationRatio_ge_four`; its proof is unchanged. The original
sharp center remains unchanged. Both new modules are in the root closure.

Validation: `lake build` passed, **3,979 jobs**, no warnings.
`lake env lean scripts/AxiomAudit.lean` passed, **2,242 declarations**, only
`propext`, `Classical.choice`, `Quot.sound`; the five new representative
exports are explicitly queried. Independent read-only B1 statement and
proof review: **PASS**, appended to
[verification/M2_ROADMAP_REVIEW.md](verification/M2_ROADMAP_REVIEW.md).
The actual audit output is `/private/tmp/freezing-growth-b1-axioms.log`.
Sequential `leanchecker --verbose` replay of `HighPopulationCentering`,
`RRTLowerCenter`, and `HighPopulationWeakCentering` passed (exit 0 for all
three; log `/private/tmp/freezing-growth-b1-replay.log`). This uses the same
Lean kernel, not an independent verifier or the full Palomar check.

There are now 149 mathematical modules in the root closure. The inventory
remains 85 IDs (39 complete, 12 partial, 31 pending, 3 open questions).
Theorem 1.2 remains partial and E1/E2 remain pending. Next lot: **B2a**,
projection of the actual first-edge split law to CDFs and real thresholds.
No manuscript change, upload, or new Comparator/Palomar verification.

## M2 lot B2a implemented (31 October 2026)

`RRTSplitCDF` projects the actual E3 component law onto arbitrary height
events and rectangular events of the component heights. It proves the exact
CDF recurrence for a tree with $n+1$ edges, natural thresholds $h+1$ and $h$,
and both strict and non-strict arbitrary real thresholds $t$ and $t-1$.
The child edge offset is retained, including negative real thresholds.
The initial and height-zero boundary values are proved on the actual law.

`RRTCentralSplits` counts central indices for a tree with $n$ edges. The set
is exactly the integer interval $[\lfloor n/4\rfloor,n-\lfloor n/4\rfloor)$,
with cardinality $n-2\lfloor n/4\rfloor$. Consequently at least half of all
split choices leave both components with at least a quarter of the vertices.
Every split has a component containing at least half the vertices. The empty
case $n=0$ is retained. When using the recurrence at argument $n$, the
amplifier must therefore use `centralSplits (n+1)`.

Both modules are integrated into the root closure. `lake build` passed with
**3,981 jobs**, no warnings. The current axiom audit passed for **2,257
project declarations**, permitting only `propext`, `Classical.choice`, and
`Quot.sound`; seven B2a exports are explicitly queried. Audit log:
`/private/tmp/freezing-growth-b2a-axioms.log`. Sequential same-kernel
`leanchecker --verbose` replay of `RRTSplitCDF` and `RRTCentralSplits`
passed (exit 0), recorded in `/private/tmp/freezing-growth-b2a-replay.log`.
This is not an independent verifier or full Palomar verification.
There are 151 mathematical
modules in the root closure. Independent read-only statement/proof-route review
passed, including the non-strict recurrence and boundary additions; see the
B2a entries in [verification/M2_ROADMAP_REVIEW.md](verification/M2_ROADMAP_REVIEW.md).

The scope is unchanged: 85 IDs, with 39 complete, 12 partial, 31 pending,
and 3 open questions. These are exact-law helpers, not a new asymptotic
height lower bound. M2p/M2e remain partial; E1/E2 remain pending.
Next lot: **B2b**, conditional amplification on the fixed lower-tail grid.
No manuscript change or publication action.

## M2 lot B2b implemented (31 October 2026)

`RRTSplit.split_average_contraction` in module `SplitContraction` proves
the finite averaging inequality: terms bounded by $a\geq0$, improved to
$a(1-p)$ on the central indices, have average at most $a(1-p/2)$ for
$p\geq0$. The proof uses the actual central-index cardinal bound.

`RRTLowerTailAmplification` defines `RRT.lowerTail`, `SeedAt`, and
`ConstantSuccessSeed` on the actual RRT height laws. Its main export
`RRT.lowerTail_geometric_of_seed` proves, for $c,A\geq0$, $0<p\leq1$, and
explicit hypothesis `SeedAt c A p`,

$$
\mathbb P(H_n<b_c(n)-A-j e\log4)
\leq(1-p)(1-p/2)^j\qquad(j,n\geq0).
$$

The induction is on the grid index with every tree size in the induction
hypothesis. The real-threshold split recurrence retains the child's offset,
which is discarded only in the favorable direction when bounding a factor.
The central set is `centralSplits (n+1)` for a root with $n+1$ edges.
The empty-tree and $p=1$ boundaries are included. Independent mathematical
statement/proof-route review passed, appended to
[verification/M2_ROADMAP_REVIEW.md](verification/M2_ROADMAP_REVIEW.md).

Validation: `lake build` passed with **3,983 jobs**, no warnings.
The axiom audit passed for **2,266 project declarations**, allowing only
`propext`, `Classical.choice`, `Quot.sound`. Both new main helper exports
are explicitly queried. The audit log is
`/private/tmp/freezing-growth-b2b-axioms.log`. There are now 153 mathematical
modules in the root closure. Sequential `leanchecker --verbose` replay of
`SplitContraction` and `RRTLowerTailAmplification` passed (exit 0); log
`/private/tmp/freezing-growth-b2b-replay.log`. This is a same-kernel check,
not an independent verifier or the full Palomar verification.

The implication is proved; the constant-success seed has **not** been
constructed. Neither M2 nor E1/E2 becomes complete on this basis.
The coverage remains 85 IDs: 39 complete, 12 partial, 31 pending, 3 open
questions. Next lot: **B3a**, integrate the geometric grid bound to a
uniformly bounded expected positive deficit. The manuscript is unchanged.

## Continuous M2 implementation: B3 and C constructions (31 October 2026)

The user superseded the one-lot-per-resume cadence and requested the entire
remaining roadmap continuously. B3a and B3b now compile cleanly.
`DeficitGrid` proves the finite indicator-grid and geometric-sum bounds.
`RRTLowerDeficit` integrates the actual lower tail to the explicit uniform
positive-deficit bound, proves its mean and Markov consequences, and absorbs
an eventual seed's finite prefix without computing any finite RRT laws.
`HighPopulationAssembly` proves `uniformHeightClaims_of_seed`: the exact
original probability/expectation conjunction follows from the single visible
premise `RRT.ConstantSuccessSeed 2`. The corrected cutoff index, uniform
choice of validity threshold before the word, and terminal extinction in the
low branch are retained. Independent mathematical review passed, including
finite-prefix absorption; see the B3 entries in the existing review file.

C1/C2 implementation is underway. `PWIT.Basic` and `RRTGeometricMixture`
have passed focused Lake builds with no warnings. The former constructs actual
independent exponential clocks, measurable finite-path times, simultaneous
almost-sure positivity and measurable generation events. The latter constructs
the actual geometrically mixed RRT law, its CDF series, normalization, index
integrability/mean/tail and fixed-size transfer bounds. First-birth, renewal
and finite-rank path modules are being implemented and checked separately.
No unproved draft is imported by the root library.

The seed, barrier estimates, full PWIT/RRT height bridge and unconditional M2
exports remain unproved. Existing coverage counts do not advance: 85 IDs,
39 complete, 12 partial, 31 pending, 3 open questions. This milestone records
focused compilation and mathematical reviews. The first integrated group
passed `lake build` (**4,004 jobs**, no warnings) and the axiom audit
(**2,421 declarations**, only `propext`, `Classical.choice`, `Quot.sound`).
The audit log is `/private/tmp/freezing-growth-b3-c1-axioms.log`.
Further C2/C3 additions are being checked in subsequent compiler phases;
this evidence does not claim those pending estimates or independent replay. No publication
or manuscript modification was performed in this milestone.

### C2/C4 and C3a verified during continuous execution

The next integrated group passed `lake build` (**4,018 jobs**, no warnings)
and the axiom audit (**2,498 declarations**, permitted axioms only), log
`/private/tmp/freezing-growth-c2-c3a-axioms.log`.
C1's actual clock decomposition and C2's full height-law bridge are now proved:
`PWIT.heightCDF_eq_geometricCdf` and
`PWIT.reaches_probability_eq_geometric_tail` identify the actual birth-event
probability with the actual geometric mixture of RRT heights. The proof uses
first-birth integrals and bounded-measurable scalar renewal uniqueness,
not an assumed chronological enumeration of an infinite tree.

C4 is proved as the explicit implication
`RRT.constantSuccessSeed_of_clockLowerSeed`. It uses the verified deterministic
`seedIndex` and its divergent time margin; the clock-success input is still
unproved. C3a now has actual finite path Gamma laws, exact finite rank counts
and density factors, and `PWIT.hasSum_integral_rankBirthCount`, which sums
all actual rank-slice means to the generation first-moment value. The explicit
whole-generation counting variable and its almost-sure finiteness are being
checked separately, as are the sampled cyclic path laws and normalized bridges.

Independent review is recorded in the existing M2 review file. The C3 barrier
bounds, positive good-count first moment, overlap second moment and resulting
`PWIT.ClockLowerSeed` remain unproved. No unconditional M2 export or E1/E2
completion is claimed. The user instruction remains to continue through all
remaining lots, rather than stop at this milestone.

### User-requested stop and handover

The user explicitly stopped continuous execution for a handover. All workers
acknowledged the stop; no owned Lean/Lake process remains. The exact compiled,
uncompiled and nonimported file inventory, focused Simplex build/axiom evidence,
source-proof findings and next steps are preserved in
HANDOVER_2026-10-31_M2.md (development record, not included in this export).
The all-rank Poisson route is a reviewed proposed proof departure; its actual
many-to-two and quantitative barrier estimates remain unproved. No seed, M2,
E1/E2 or publication completion is claimed at this pause.

### Resumed C3 development (1 November 2026)

The user lifted the handover pause and asked to continue. The previously
uncompiled `GenerationCount`, `TimeCenterEstimates`, `Leading` and
`RankDensity` now compile without warnings. The actual generation count is
measurable, has the exact finite first moment and is finite almost surely;
its real projection is integrable. The weighted cyclic identity is applied
only after summing a whole finite rank class. Its actual mixture has the
orthant radial density previously described, without a probability divisor.

All six `Simplex*` foundations and the new `SimplexMixture` are integrated.
The latter proves the common normalized bridge for **every** excess rank,
with its actual Gamma endpoint and correct class mass. `GammaWindows` proves
explicit uniform lower bounds on standardized integer-Gamma windows and the
global density bound $1/\sqrt n$ (shape $n+1$, mode $n$). Independent actual-body
reviews passed these modules, including the previously unread grouping laws.

`AllRankCount` supplies measurable extended counts, exact Tonelli identities,
the actual path-existence bridge and finite-mean domination. `CriticalWindow`
and `AllRankLeading` now prove the exact expected count of exactly-leading
paths with endpoints in $(m_d-1,m_d]$, and a strictly positive lower bound
for all sufficiently large $d$. This is an actual count with no excess-rank
cutoff. Its window formula explicitly requires a nonnegative lower endpoint;
the eventual application proves $m_d\geq1$. This first moment is not a
success probability. `AllRankMoment` proves a generic global second-moment
implication with first and square integrability visible as premises.
`OverlapEstimates` proves the uniform suffix factor and stretched-exponential
summability helpers; it does not assert a stochastic pair bound.

Current integrated evidence: `lake build` passed **4,055 jobs**, no warnings.
`lake env lean scripts/AxiomAudit.lean` passed **2,762 declarations**, using
only `propext`, `Classical.choice`, and `Quot.sound`. The actual audit output is
`/private/tmp/freezing-growth-c3-2026-11-01-axioms.log`. Independent mathematical
and proof-correspondence reviews are in `verification/M2_ROADMAP_REVIEW.md`.
This is ordinary Lean/axiom evidence; no new kernel replay, Comparator, or
Palomar verification is claimed for this checkpoint.

The preferred remaining seed argument has been simplified further after an
independent mathematical assessment: for exact Poisson offspring, use the
global pair intensity and apply the near-leading bound to the common prefix
and to **both** suffixes. Three factors give a uniformly summable overlap,
so neither $B_a$ nor $D_a$ is needed for this alternative seed proof. Details
are in the updated `M2_ROADMAP.md` and the review. This does not verify the
bypassed cited barrier arguments. The actual ordered-sibling and path-pair
laws, near-leading bound, and quantitative second moment are still being
formalized; new files outside the root closure are not covered by the above
build. `PWIT.ClockLowerSeed`, unconditional M2, E1/E2 and publication remain
open. The inventory remains **85 IDs: 39 complete, 12 partial, 31 pending,
3 questions**. The manuscript and destination instructions are unchanged.

### Universal ballot and actual pair laws verified

The next integrated group passed `lake build` (**4,076 jobs**, no warnings)
and the full axiom audit (**3,055 declarations**, the same three permitted
axioms only). Output:
`/private/tmp/freezing-growth-c3-ballot-2026-11-01-axioms.log`.
The new root closure includes the following proved ingredients:

- `SimplexNearLeading`: a single explicit positive constant bounds the
  near-leading probability for every positive dimension, nonnegative allowance
  and positive prescribed endpoint. The proof uses actual three-block
  simplex/Gamma joint laws, controlled integer padding, and exact cyclic
  probabilities; it does not multiply probabilities conditioned on a fixed
  total without a joint-law justification.
- `OffspringIntensity`, `ManyToTwo`: actual ordered distinct-sibling factorial
  intensity is the product of positive Lebesgue measures. Actual root-row and
  two-subtree joint laws justify a full common-ancestor expansion, with the
  diagonal separate and coefficient one for every ordered overlap. A common
  carrier of zero-extended increment sequences avoids dependent length casts;
  exact restriction recovers the original finite-dimensional pair law.
- `GenerationBridge`: the actual unnormalized positive-orthant intensity
  disintegrates into the canonical simplex law and endpoint density
  $s^{d-1}/(d-1)!$ for $s\geq0$, with positive dimension explicit. Reconstruction
  from that product is proved, including the null zero-total exception.
- `PairCount`, `PairDecomposition`: the square of the actual extended count
  integrates to the actual ordered-pair intensity. The exact decomposition is
  diagonal mean, independent-root mean squared, and the interior-depth sum.
  Real-square integrability follows only after the actual pair measure is
  proved finite.
- `BallotIntensity`, `BallotIntensityUniform`, `ThreeFactorOverlap`: multiplying
  the actual simplex probability by its endpoint density gives a uniform
  exponential bound in every positive dimension and for all real endpoints.
  Negative endpoints have zero density. Arbitrary real endpoint windows of
  width at most one are covered with genuine integrability. The three-factor
  depth weight has a uniform finite sum controlled by the convergent
  $3/2$-power series; the excess polynomial times exponential is integrable.

Independent actual-body and statement reviews passed these ingredients.
The source hash is unchanged. No new kernel replay, Comparator or Palomar
verification has yet been claimed for this group. The actual overlap-to-density
transport and the exponential product-integration assembly are written and
reviewed, but are being compiled separately outside the current root closure.
The final global square-moment bound, the clock seed, unconditional M2 and the
other retained inventory obligations remain open. `ClockSeedMoment`, also
written and reviewed but not yet compiled, is only an implication from an
explicit uniform square-moment bound; it does not close that bound.

### Theorem 1.2 completed (1 November 2026)

The full M2 roadmap is now implemented without an unresolved probability or
moment premise. `PWIT.uniform_exactLeadingWindow_secondMoment`
proves genuine square integrability and a bound uniform in the generation for
the actual exactly-leading endpoint-window count. The actual ordered pair law
splits its second moment into the diagonal, independent-root mean squared,
and the interior-depth sum. `OverlapIntegral` transports each true overlap
to three ballot factors; `OverlapProduct` and `OverlapBound` integrate their
actual density bound. The closed boundary is handled by its zero Lebesgue
mass. No finite depth enumeration, excess-rank window, bad-rank estimate or
interior-barrier estimate is needed for this alternative proof.

`PWIT.clockLowerSeed` now proves `ClockLowerSeed` without an estimate premise.
`uniformHeightClaims` in `UniformHeightBounds` applies the actual geometric RRT
transfer, split amplification and bounded-deficit assembly to obtain both
original conclusions, with the corrected cutoff $r_n-1$ and terminal
extinction retained. `Paper.theorem_1_2`, `theorem_1_2_probability` and
`theorem_1_2_expectation` export the exact independently reviewed targets.

Current evidence: full `lake build` passed **4,082 jobs**, no warnings;
`scripts/AxiomAudit.lean` passed **3,123 declarations**, and the actual new
clock seed, global moment, conjunction and numbered projections use only
`propext`, `Classical.choice`, `Quot.sound`. The audit output is
`/private/tmp/freezing-growth-m2-final-2026-11-01-axioms.log`.
Independent final source, statement and proof-route review passed. A sequential
same-kernel replay passed **18 explicit module targets**, from
`PWIT.AllRankCount` through `PWIT.GenerationCount` in alphabetical order;
the summary and per-module logs are in
`/private/tmp/freezing-growth-m2-kernel-replay/`. The coordinator interrupted
the run during `PWIT.GenerationFirstMoment` (exit 130) to release the compiler
for subsequent proof work. Thus 49 targets are unfinished: one interrupted and
48 not started. These are deferred, not reported as passed or failed.
No Comparator, independent verifier, remote CI,
GitHub upload or Palomar verification is claimed.

The affected inventory was independently reconciled: M2p, M2e and D5 are now
complete; H4 is complete in corrected form by the alternative deficit proof.
H3 remains partial because its literal fine mean expansion is not proved,
although its final uniform mean bound is. This gives **85 IDs: 43 complete,
9 partial, 30 pending, 3 open questions**. E1/E2, Proposition 1.1(i)–(ii),
full labelled-tree couplings and the other retained obligations remain open.
The manuscript is unchanged. New follow-up work on coarse RRT upper tails
was subsequently integrated at the following helper milestone; it does not
certify the sharp E1/E2 assertions.

### Same-tree depth gap and survivor profiles (1 November 2026)

`RRTDepthMoments` derives the actual marginal centered moments from the
one-step uniform-vertex law: $\mu_m/2\leq V_m\leq\mu_m$ and
$K_m\leq3\mu_m^2+\mu_m$. `RRTMeanDepthVariance` proves that the actual random
tree mean has variance at most one. `AbsoluteMomentBounds` and `RRTDepthGap`
then give an actual ordered-distinct same-tree absolute gap at least
$\sqrt{\mu_m}/16-1$ eventually. This replaces the paper's joint-CLT argument;
the joint CLT E4 and its cited proof are not verified by this alternative.

`ForwardFiniteSupport` supplies genuine finite-horizon integrability for
every real state observable. `FinitePairAveraging`, `ForwardPairAveraging`
and `ForwardPairMaximum` establish the exact uniform-freeze identities with
at least three vertices before deletion. `TwoSurvivorGap` identifies all
depth-pair/full-maximum profile expectations for the actual source prefix
and transfers the gap divergence to its two survivors. Vertex identity,
rather than equal depth, determines the removed diagonal. The full underlying
labelled-tree survivor law remains open.

`RRTUpperTail`, `RRTRoughAbsoluteDeviation` and `RRTSplitRoughGap` give actual
coarse height tails, uniform positive excess and a component-height imbalance
bounded by $C+4\log(1+\log(n+1))$. `RRTDepthGapAsymptotics` shows that the
proved gap dominates this error for polynomial continuation sizes, including
$n=m^9$. `SeedComparison` retains the old-tree residual in its pointwise
comparison. These do not certify the sharper E1/E2, bounded-imbalance I6 or
the full floor-indexed expected-height limit I9.

Evidence: full `lake build` passed **4,097 jobs**, without warnings.
`scripts/AxiomAudit.lean` passed **3,283 declarations**, permitting only
`propext`, `Classical.choice`, `Quot.sound`; log
`/private/tmp/freezing-growth-m1-helper-2026-11-01-axioms.log`.
Independent statement and actual-body reviews passed the new chains.
`main.tex` retains its recorded SHA-256; no new kernel replay, Comparator,
independent verifier, remote CI or Palomar result is claimed.

Only I8 becomes complete and I1 becomes partial at this milestone:
**85 IDs: 44 complete, 10 partial, 28 pending, 3 open questions**.
Proposition 1.1(i)–(ii) remain open. Actual seeded-word comparisons and the
old-tree residual estimate are the next integration obligations. A uniformly
bounded residual suffices for the existential main claims; the manuscript's
stronger zero-limit assertion I5 remains separately required. New working
files outside the integrated closure carry no additional coverage credit.

### All Introduction main results completed (1 November 2026)

`MainDeletionClaims` proves `RemoveFreezeAttachClaim` and
`RemoveAttachFreezeClaim` without unresolved mathematical premises.
`Paper.proposition_1_1_i`, `proposition_1_1_ii`, and the combined
`proposition_1_1` export the exact original targets alongside the earlier
part (iii). The first assertion retains the same witnesses for deleting the
pair and deleting only the freezing step.

The actual local profile laws, including all six attachment/freezing choices,
are integrated through the genuine two-survivor prefix. Their old maximum
stays coupled to both depths, and a newly attached child still contributes
when frozen. The local comparison yields a global gain of at least half the
actual distinct depth gap minus the component-height imbalance, one edge and
the old-tree residual. For $n=m^9$, the residual is uniformly bounded and the
depth gap dominates the $O(\log\log n)$ imbalance. The attachment/freezing
gain is at least one third of this gain minus $2/3$.

This is a substantive alternative to the paper's sharp-height/CLT route.
The actual six-branch and seeded-height calculations were checked. The sharp
E1/E2/E4 inputs, the stronger floor-indexed I9 assertion, source-specific
vanishing remainders, sharper conditional cases and full labelled grafting
couplings are not certified by this milestone and remain in the inventory.

Current milestone evidence: full `lake build` passed **4,110 jobs**, with no
warnings. The full axiom audit passed **3,381 declarations**, with only
`propext`, `Classical.choice`, `Quot.sound`; log
`/private/tmp/freezing-growth-introduction-2026-11-01-axioms.log` includes
the exact two claims and all numbered Proposition 1.1 exports. Independent
source, statement and actual-body review passed the global chains and final
wrappers. The unchanged source hash and a clean forbidden-proof scan were
checked. No new independent kernel, Comparator, remote CI or Palomar result
is claimed; publication remains unfinished.

M1i, M1f and M1ii now become complete, yielding **85 IDs: 47 complete,
10 partial, 25 pending, 3 open questions**. All Introduction main results are
proved; the full requested paper scope remains partial.

### Full floor-indexed deletion limits (1 November 2026)

`FloorDeletionGaps` now proves both expected-height limits for every natural
continuation index with the exact prefix $m=\lfloor n^{1/9}\rfloor$, not merely
the ninth-power subsequence. `PaperPrefixSize` gives the all-index power
inequalities, divergence of $m$, and eventual $n\leq m^{18}$.
`RRTSplitResidualPolynomial` bounds the genuine residual uniformly for all
$n\geq m^9$. The depth-gap estimate at exponent eighteen absorbs the actual
component-height imbalance. The final attachment/freezing difference is
exported with the manuscript's sign and limit at minus infinity.

Full `lake build` passed **4,113 jobs**, without warnings; the full axiom
audit passed **3,395 declarations**, with only the permitted three axioms.
Log: `/private/tmp/freezing-growth-floor-gaps-2026-11-01-axioms.log`.
Independent actual-body review passed the new floor, residual-range and limit
proofs. Sequential same-kernel `leanchecker --verbose` replay of
`FreezingGrowth.MainDeletionClaims` and `FreezingGrowth.PaperResults` passed
(exit zero for both); logs are in
`/private/tmp/freezing-growth-introduction-replay/`. This is a scoped replay
against imports using the same Lean kernel, not an independent verifier or a
replay of every source module. The earlier M2 replay remains at eighteen
successful targets, one interrupted and forty-eight not started.

I9 is now complete. II5 is partial: its final full-sequence limit is proved,
but its explicit conditional case-(c) statement remains. This gives **85 IDs:
48 complete, 11 partial, 23 pending, 3 open questions**. The common-residual
zero-limit helper and actual tagged-case kernels are new working files
outside this checked closure; no further coverage is credited yet.

### Labelled survivors, conditional cases and exact comparison rate (1 November 2026)

The complete original labelled tree and its two survivor IDs now have the
actual RRT/conditional-uniform-pair bind law (`TwoSurvivorTreeLaw`), closing I1.
The tagged global height model makes all three freezing cases uniform and
independent of the remaining model data. Its actual word-height marginal and
normalized branch restrictions justify the precise errors $1/(n+1)$ and one,
and the conditional third-case divergence. Thus II2–II5 are complete;
the full labelled graft constructions I2, II1 and III1 remain separate.

`RRTFirstOrder` closes the RRT half of O5 in normalized absolute mean and in
probability. `RRTLowerTailPaperRate` shifts the actual seed finitely to success
$3/4$; its resulting rate is at least $1/(3e)$. With the exact floor sizes,
`PaperHeightComparison` proves L1's $n^{-1/8}$ bound. `PaperMeanThresholds`
proves the source's two centered event inclusions using the same height on
both sides, correcting SF5. This closes LP1 by an alternative route to the
sharp E1/E2 argument. The common constants of L1 and the pending L2 remain
to be chosen together by enlargement.

`RRTCriticalLowerSeed` also transfers the actual clock seed at coefficient
$3/2$ with a fixed offset, and proves its bounded expected lower deficit.
This is one-sided progress on E1, which is now partial. Its upper critical
tail, tightness and bounded mean error remain unresolved, as does E2.
`E1_ROADMAP.md` records the reviewed logarithmic-barrier route. The compiled
`PWIT.CyclicBarrier` proves only the generic rotation/near-minimum occupancy
reduction under explicit symmetry, measure-preservation and no-tie hypotheses.
`PWIT.GammaBridgeBounds` supplies uniform actual Gamma density and positive
unit-band estimates. Neither helper assumes a fixed labelled path is an
exchangeable simplex bridge; neither is counted as E1 or E2.

Current evidence: full `lake build` passed **4,135 jobs**, without warnings.
`lake env lean scripts/AxiomAudit.lean` passed **3,690 declarations**, permitting
only `propext`, `Classical.choice`, `Quot.sound`. The audit log is
`/private/tmp/freezing-growth-cases-comparison-2026-11-01-axioms.log`.
The independent reviewer read the exact new statements and actual bodies;
all passed, with route limits retained in `verification/M2_ROADMAP_REVIEW.md`.
The unchanged source hash and a forbidden-proof scan were checked. There is
no new independent kernel replay, Comparator, clean public checkout, remote
CI or Palomar pass. The earlier curated export is still historical.

All **85 IDs** remain: **60 complete, 8 partial, 14 pending, 3 open questions**.
The full requested paper scope and the publication candidate are unfinished.
New two-block simplex work outside the integrated closure is not credited.

### Actual logarithmic ballot and reverse dynamics (1 November 2026)

`PWIT.SoftBallotSummation.simplex_log_ballot_bound` now proves the actual
uniform canonical-simplex estimate with one fixed positive constant:

$$
\mathbb P\!\left(Y_j\geq-A-c\log(\min(j,d-j)+1)\text{ for all }j\right)
 \leq C\frac{(1+A+c)^{14}}d,
\qquad d\geq1,\quad A,c\geq0.
$$

The proof retains the genuine rotation law, almost-sure no ties and the
minimum-at-zero indicator. Actual independent block angles and a positive
Gamma total band give the near-minimum occupation bound. The exceptional
suffix is polynomially short, and its first-angle estimate supplies the
remaining terms. The shifted logarithmic series is summable; the zero-position
term is exactly $1/d$. No fixed labelled PWIT path is assumed exchangeable.
The theorem is unconditional, but does not itself prove E1/E2: the actual
first-crossing clock upper bound remains to be established.

The critical upper transfer and critical absolute/mean deviation helpers are
also integrated with their clock upper estimate retained as an explicit premise.
`CriticalBarrierGeometry` excludes all prefix dimensions below thirty by a
negative barrier, without enumerating trees. The endpoint/count intensity and
conditional sharp-height adapters are newer working files and not credited
as completed source results here.

The full labelled forest-order theorem closes F2. Actual source-tail
initialization and finite delayed dynamics close C2 and C3. The unused-state
matching invariant and local adjoin/join commutation give partial C6 progress.
The terminal used flag proves the $M_0=1$ subclaim of C7, which becomes partial.
C1's common-tail relabelling, C4/C5's whole-process laws and the first-use graft
relation remain explicit obligations. No conclusion about entire histories is
drawn merely from equality of separate phase marginals.

Full `lake build` passed **4,155 jobs**, with no warnings.
`scripts/AxiomAudit.lean` passed **4,055 declarations**, permitting only
`propext`, `Classical.choice`, `Quot.sound`. Log:
`/private/tmp/freezing-growth-ballot-dynamics-2026-11-01-axioms.log`.
Independent statement and actual-body reviews passed the new chains and
coverage changes. The source and scope are unchanged. All **85 IDs** remain:
**63 complete, 9 partial, 10 pending, 3 open questions**.
No independent kernel replay, Comparator, clean public checkout, remote CI or
Palomar verification is newly claimed. The curated export remains historical.


## Critical height and complete first-process history (1 November 2026)

The actual critical upper clock estimate is now proved in
`PWIT/CriticalClockUpper.lean`. The finite first-crossing reduction uses one
witnessing actual PWIT path and nonnegative clocks; it does not assume an
attained minimum over the infinite generation. Prefix dimensions below thirty
are excluded by a fixed negative barrier. The all-rank logarithmic-barrier
intensity, the degree-fourteen actual simplex bound, and a uniformly summable
minimum-window depth bound give $C(1+x)^{14}e^{-x}$ under the actual clock law.
The terminal crossing dimension is included using a shifted logarithmic series.

`RRTSharpHeight` discharges E1/E2, including the exact source center and
numerical centered exponential rate. `RRTSharpSplitMean` proves LP2 and I6;
I6 uses actual critical absolute deviation and uniform split averaging rather
than deducing it from L2. `TwoSeedSharpGap` proves both source I7 equalities,
with a bounded absolute error at the full floor index. `HighPopulationSharp`
finishes the fine mean expansion and its logarithmic-ratio form at the corrected
edge count. The Introduction proofs remain valid by their earlier alternative
routes and do not need to be rewritten to depend on the new sharp estimates.

The entire first-process labelled-graph history is now identified with
Algorithm 2, retaining its actual ordered common tail and both initialization
states. The neighbouring-phase pending match is explicit. Thus C4/C6 are
complete; the shorter-process conditional history law C5 and first-hit history
in C7 remain separate. Local first-use graft and terminal pathwise domination
working files are outside this checkpoint's import closure.

Current full `lake build`: **4,172 jobs**, no warnings, recorded in
`/private/tmp/freezing-sharp-full-build.log`. Current full axiom audit:
**4,260 declarations**, only `propext`, `Classical.choice`, `Quot.sound`, in
`/private/tmp/freezing-growth-critical-2026-11-01-axioms.log`. Independent
statement and complete-body reviews passed for all changed source-facing
exports. The source hash and the independently checked 85-item inventory are
unchanged. Current coverage: **71 complete, 5 partial, 6 pending, 3 open
questions**. No independent whole-library kernel replay, Comparator pass,
remote CI, Palomar verification or publication readiness is claimed.


## Full split tails and first-use history (1 November 2026)

Lemma 2.2 is complete with one shared pair of positive constants. The actual
first-edge split sampling retains the uniform size tag and zero-size endpoints;
its four-term decomposition, exact conditioning, finite maximum, shifted ratio
count and two-exponential bound now verify LP3/LP4 as well as L2. These prove
the displayed source arguments, rather than replacing them by the earlier
coarse mean bound.

C7 is complete on the actual finite delayed histories. The first chronological
true flag exists by terminal use; reversing its index gives the printed maximum
$j_1=k-1-r$. At the initial index the proved initializer graft applies, and at
later indices the preceding flag is false and the exact consumed-pair transition
graft applies. The incoming forest and full history remain on the same sample.
The component slot, original stored pair and complete root-order/forest equality
are retained. The source terminal marginal is explicitly identified.

The corresponding used-state height invariant and terminal pathwise maximum
comparison are proved. C8 remains partial solely because C5's identification
of the shorter process is still missing. A previously sampled delayed pair is
not asserted independent of all joint-process history.

Full `lake build`: **4,178 jobs**, no warnings, in
`/private/tmp/freezing-split-first-hit-full-build.log`. Full permitted-axiom
audit: **4,355 declarations**, only `propext`, `Classical.choice`, `Quot.sound`,
in `/private/tmp/freezing-growth-split-first-hit-2026-11-01-axioms.log`.
Independent statement and actual-body review passed for the changed exports.
The source and inventory are unchanged. Coverage is **75 complete, 4 partial,
3 pending, 3 open questions**. Pending: I2, C5, E4. Partial: II1, III1, C1, C8.
Publication, Comparator and independent full-library kernel replay remain
unverified.


## Source delayed coupling completed (1 November 2026)

The original reverse deletion-coupling argument is now checked in full.
The exact frozen-label permutation identifies the whole common-tail ordered
history. The actual shorter-history/pending-tag product law is then proved at
every phase, including that original tail past. It gives the corrected SF6
conditional independence: the pending stored pair is independent of the
comparison process's complete past, not of the joint-process past.

The full shortened-word history and terminal ordered forest law are identified,
with the precise two-step label shift. Both actual terminal height marginals
are now proved on the same delayed construction. `sourceCoupling_heightLE`
uses its genuine terminal pathwise inequality and the verified forward/reverse
law bridge to obtain the original stochastic comparison. This closes C1, C5
and C8, and verifies the source proof of M3 in addition to the earlier alternate
law-level proof. The original manuscript remains unchanged; SF6 records the
required filtration clarification.

Current full `lake build`: **4,187 jobs**, no warnings, in
`/private/tmp/freezing-source-coupling-full-build.log`. Current full axiom audit:
**4,511 declarations**, only `propext`, `Classical.choice`, `Quot.sound`, in
`/private/tmp/freezing-growth-source-coupling-2026-11-01-axioms.log`.
Independent source and complete-body reviews passed. Source and inventory
unchanged. Coverage: **78 complete, 2 partial, 2 pending, 3 open questions**.
The remaining mathematical obligations are I2, II1, III1 (full graft couplings)
and E4 (joint depth-difference Gaussian limit). New master-graft and depth-limit
working modules have no completion credit until integrated and audited.
Publication, Comparator and independent full-library kernel replay remain
unverified.

## User-requested stop (1 November 2026)

Development was stopped at the user's explicit request because their token
allowance was exhausted. No compiler remains active. The current verified
checkpoint is unchanged: 4,187 build jobs, 4,511 permitted-axiom declarations,
78 complete, 2 partial, 2 pending and 3 open questions. Frozen candidate files,
their actual compiler status, last diagnostics and precise restart tasks are
recorded in HANDOVER_2026-11-01.md (development record, not included in this export). The E4 final
adapter's last two repairs and the tagged-graft branch repairs have not been
recompiled. No further mathematical or publication completion is claimed.

## Main results

| ID | Source | Exact obligation | Main proof dependencies | Current coverage |
| --- | --- | --- | --- | --- |
| M1i | 209–217, `prop:increaseheight` (Proposition 1.1(i)) | For every real $A>0$, some natural $m,n$ make deleting the specified consecutive freezing/attachment pair raise expected height by at least $A$. | Paper route: I1–I9, L1–L2, E1–E4. Alternative route: actual survivor profiles, depth moments, coarse height imbalance, bounded residual. | **Complete by an alternative proof.** `removeFreezeAttachClaim`, exported as `Paper.proposition_1_1_i`, supplies $n=m^9$ and the original actual-word inequalities without an unproved estimate. `freezeAttachExpectedGap_lower` and its polynomial divergence use the actual same-tree pair law. This main proof bypasses E1/E2/E4 and the stronger intermediates; those obligations are now separately certified below. Full 4,110-job build, 3,381-declaration axiom audit and independent source/body review passed. |
| M1f | 219, unnumbered consequence inside Proposition 1.1(i) | For the same witness parameters, deleting only the freezing step gives the stated gap at least $A$. | M1i and monotonicity under one final attachment. | **Complete.** The same `RemoveFreezeAttachClaim` proof provides both inequalities for the same $(m,m^9)$, using `Word.expectedHeight_le_append` for one further attachment. No independent witnesses are substituted. |
| M1ii | 220–224, Proposition 1.1(ii) | For every $A>0$, some $m,n$ make deleting the specified attachment/freezing pair raise expected height by at least $A$. | Paper route: II1–II5 and I9. Alternative route: actual six-branch profile law and the affine comparison with the proved freezing/attachment gap. | **Complete by an alternative proof.** `removeAttachFreezeClaim`, exported as `Paper.proposition_1_1_ii`, requests a freezing/attachment gap at least $3A+2$ and applies `attachFreeze_expected_gap_ge`. The actual six occurrence-weighted cases retain the new child's maximum. The sharper conditional case assertions and full labelled-tree couplings remain separate. Full build, axiom audit and independent source/body review passed. |
| M1iii | 225–229, Proposition 1.1(iii) | Some $n$ makes expected height of $(+1,-1)(+1)^n$ strictly exceed that of $(+1,+1,-1)(+1)^n$. | Source route: III1–III10, E1, E5. Alternative existence route: seeded means, exchangeability, sublinear RRT mean and telescoping. | **Complete.** `removeAttachClaim`, exported as `Paper.proposition_1_1_iii`, proves the exact existential target. `removal_reversal_arbitrarily_late` additionally supplies witnesses after every index. Analytic route: actual seeded-growth laws and mixture means, exchangeability, sublinear RRT mean, and telescoping. No numerical witness or sharp RRT estimate is assumed. III9/III10 are now also complete, via the subsequent negative-moment proof; see the A1–A3 milestone. |
| M2p | 245–249, `thm:main` (Theorem 1.2) | The minimum over all admissible $n$-attachment sequences of the probability of height at least $e\log n-5\log\log n$ tends to one. Uniformity in the sequence is essential. | M3, H1–H4, B1–B2, D1–D4, E1, E7. | **Complete.** `Paper.theorem_1_2_probability : UniformHeightProbabilityClaim` is unconditional; `FamilyMinima` proves the exact minimum/epsilon equivalence. Actual clock success, geometric RRT transfer, lower-tail amplification and both population branches give the original uniform claim, including terminal extinction. Full build and 3,123-declaration axiom audit passed on 1 November; independent final source/route review PASS. This proof bypasses E1; the sharp estimate is separately certified under E1. |
| M2e | 250–253, Theorem 1.2 | For all sufficiently large $n$, the minimum expected height over the same class is at least $e\log n-5\log\log n$. The threshold in $n$ is uniform. | M3, H1–H3, D1–D3, E1. | **Complete.** `Paper.theorem_1_2_expectation : UniformHeightExpectationClaim` is unconditional, with the exact family-minimum equivalence already proved. The same clock/RRT seed supplies a bounded positive deficit and the corrected-index high branch, combined with the full low branch. Full build/axiom audit passed; independent final source/route review PASS. No sharp mean expansion is assumed here; it is separately certified under E1. |
| M3 | 261–265, `prop:decreaseheight` (Theorem 1.3) | For a valid sequence with initial run of $k\geq1$ attachments followed by a freezing, remove its $k$th and $(k+1)$st steps; the new height is stochastically dominated by the old height. Terminal extinction is allowed. | F1–F3, C1–C8, E6. | **Complete.** `FreezingGrowth.firstPairDeletionClaim` (numbered export `Paper.theorem_1_3`) proves `FirstPairDeletionClaim` with its exact source-facing signature: $k\geq1$, arbitrary tail, validity of the shortened word and `Word.HeightLE` both conclusions, including $k=1$ and terminal extinction; no coupling or survival premise. Route: `ReverseHeightDynamics`, `ReverseHeightRecursion`, `ReverseSingletonInsertion`, `ReverseFirstPairDeletion` (a law-level recursion; see departures). Full `lake build` (3,954 jobs, no warnings) and the axiom audit (only `propext`, `Classical.choice`, `Quot.sound`) passed on 31 October 2026. Independent read-only review: statement PASS, proof route PASS-WITH-NOTES. The later C1–C8 milestone also certifies the source delayed coupling. |

## Other numbered results

| ID | Source | Obligation | Current coverage |
| --- | --- | --- | --- |
| O1 | 321–326, Observation 2.1 (no label) | For every $n\geq3$, alternating-tree height does not stochastically dominate $n$-edge RRT height. | **Complete.** `Alternating.not_heightLE_rrt` (export `Paper.observation_2_1`): for every $n\geq3$, `¬ Word.HeightLE (replicate n true) (alternatingWord n)`. Built and audited 31 October 2026; independent read-only review PASS. |
| L1 | 361–366, `lem:estimates` (Lemma 2.2(i)) | Some common $c_1,c_2>0$ give the stated bound $2c_1 n^{-1/8}$ for comparison of independent RRT heights at sizes $\lfloor n^{1/9}\rfloor$ and $\lfloor n/2\rfloor$, eventually in $n$. | **Complete for part (i).** `paper_height_comparison_polynomial` gives the exact eventual $2c_1n^{-1/8}$ bound on the actual independent product at the two exact floor sizes. The finite seed boost gives the numerical rate $1/(3e)$ at the regularized lower center, and the coarse error is enough at the separating threshold. No sharp E1/E2 premise remains. `paper_height_comparison_and_split_tails` now supplies the common positive constants with part (ii). Built, axiom-audited and independently reviewed. |
| L2 | 364, 367–368, Lemma 2.2(ii) | With the same constants, for every natural $n,k\geq1$, the independent uniformly split RRT-height difference has tail at most $4c_1e^{-c_2k/4}$. | **Complete.** `paper_height_comparison_and_split_tails` gives one common positive pair $c_1,c_2$ for both Lemma 2.2 assertions, including the eventual exact-floor comparison in (i) and the actual uniformly split independent RRT-height difference in (ii). The tail bound holds for every $n\geq0$ and every nonnegative real threshold, hence for all source natural $n,k\geq1$. Full 4,178-job build, 4,355-declaration permitted-axiom audit and independent actual-body review passed. |
| B1 | 931–935, `prop:bennett` (Proposition 3.1, upper tail) | For independent Bernoulli variables with positive total mean $m_n$ and every real $t>0$, strict upper-tail probability is at most $\exp(-m_ng(t/m_n))$, where $g(u)=(1+u)\log(1+u)-u$. | Complete: `FreezingGrowth.bernoulli_sum_upper_tail`; source review, build, axiom check passed. |
| B2 | 931–935, Proposition 3.1, lower tail | The same bound for the strict lower tail, including $t\geq m_n$ where the event is empty. This is a cited theorem but is explicitly restated as an in-scope proposition. | Complete: `FreezingGrowth.bernoulli_sum_lower_tail`; source review, build, axiom check passed. |

There are exactly six numbered result environments: two `thm`, two `prop`, one
`lem`, and one `obs`. No numbered corollary, claim, or remark environments occur.
The numerous substantive prose claims below must not be lost merely because
there is no theorem environment around them.

## Definitions, well-posedness, and finite examples

| ID | Source | Obligation or meaning required | Current coverage |
| --- | --- | --- | --- |
| A1 | 190–202, `eq:Sj` | Choice sequence, prefix active counts starting at one, extinction time, validity and the class $\mathbb X_n$. A prefix may reach zero at the final step but not earlier. | **Complete.** Implemented: finite `Word` admissibility, active counts, and finite-horizon extinction equivalence. The infinite stopping time is not identified with the truncated paper value.|
| A2 | 196, 299–310, Algorithm 1 | The conditional uniform transition law for a rooted tree with active/frozen vertex labels; well-defined active choice before every step. Independent auxiliary draws, not unconditional independence of the history-dependent selected vertices, formalize the wording at line 304. | Complete: `Forward.transitionLaw_apply`, `treeLaw_valid`, `treeLaw_isTree`, and the graph-distance height bridge. |
| A3 | 202, 310 | Number of active vertices after step $j$ equals $S_j$; an admissible sequence with $n$ attachments has exactly $n$ edges. Include height bounds and attachment/freezing invariants used later. | Complete: active/edge counts through extinction and height at most attachment count, exported in `TreeCounts`. |
| A4 | 198–202, 248–253 | The class in each minimum is nonempty and finite (valid sequences have $n\leq m\leq2n+1$); hence the displayed minima are meaningful. This is implicit but necessary for faithful main statements. | Complete: finite, nonempty families; attained minima and exact uniform/minimum equivalences in `FamilyMinima`. |
| A5 | 256, 319 | No-freezing construction agrees with the RRT law; define the alternating tree with $n$ attachment/freezing pairs. | Complete definitions and law bridges: `RRT.allAttach`, `uniformVertexDepthLaw_eq_bind_vertices`, `alternatingWord`, and `alternatingWord_heightLaw`. Separate distributional obligations are tracked below. |
| O2 | 325–326 | For $n\geq1$, RRT height-one probability is $1/n!$. | **Complete.** Proved by `RRT.height_one_mass` and its real-probability version, using actual uniform attachment. Focused build and independent target/route review passed; covered by the 31 October 2026 integrated build and audit.|
| O3 | 325–326 | For $n\geq1$, alternating-tree height-one probability is $2^{-(n-1)}$. | **Complete.** `Alternating.height_one_mass` and `height_one_real_mass` (export `Paper.alternating_height_one_probability`): the actual alternating tree with $n\geq1$ edges is a star with probability $2^{-(n-1)}$. Built and audited 31 October 2026; independent read-only review PASS. |
| O4 | 325–326 | For $n\geq3$, the two height-one probabilities have the strict inequality that disproves domination. | **Complete.** The exact inequality in `StarComparison` is combined with the actual identifications $1/n!$ and $2^{-(n-1)}$ to prove the stochastic non-domination `Alternating.not_heightLE_rrt` for $n\geq3$ (see O1). |
| O5 | 330–339 | Alternating height divided by $n$ tends to $1/2$ in probability; RRT height divided by $\log n$ tends to $e$ (cited/derived external results E8 and E1). | **Complete.** `alternating_height_tendsto_half` proves the alternating limit; `RRT.heightLaw_firstOrder_in_probability` proves the actual RRT height divided by $\log n$ tends to $e$. `tendsto_firstOrderAbsoluteDeviation` additionally gives normalized absolute-mean convergence. This uses the proved rough error, without asserting E1. Full build/axiom audit and independent actual-body review passed on 1 November. |

## Proof of Proposition 1.1(i) and Lemma 2.2

| ID | Source | Obligation | Current coverage |
| --- | --- | --- | --- |
| I1 | 375–378 | With $m=\lfloor n^{1/9}\rfloor$, the common prefix tree is an $m$-edge RRT whose two remaining active vertices form a uniform distinct pair. | **Complete.** `twoActivePrefix_active_card` gives exactly two active vertices. `twoActivePrefix_treePairLaw_eq_bind_vertices` identifies the full persistent labelled tree and its ordered survivor IDs with the actual $m$-edge RRT followed by a uniform ordered distinct pair of all its vertices. The bind retains dependence on the tree; graph, parents, heights and labels are retained, while freezing timestamps are forgotten. Full build/axiom audit and independent actual-body review passed. |
| I2 | 380–385 | Joint grafting coupling using an independent uniform split $I_n\in\{0,\ldots,n\}$ and independent RRTs. Include the RRT first-edge split law and conditional component independence, not just the uniform split size. | **Complete.** `TwoSeedGraft.source_freezeAttach_history_coupling`, `source_history_treePair_split`, `source_history_both_graft_graphs` and `historySample_entire_common_prefix` realize both complete original-word trajectories on one probability space, retain the literal shared prefix, identify the original full RRT and ordered uniform pair, and prove joint independence from the actual uniform-size split with conditionally independent complete RRT components. The two full graft graphs preserve frozen data and source orientation. Independent final source/body review PASS; current full build and permitted-axiom audit passed. |
| I3 | 397–405, `eq:HeightCoupled` | Both displayed height maxima hold jointly under that coupling. | **Complete at the actual joint-height level.** `TwoSeedCoupling.source_height_coupling` proves both word-height marginals on the same genuine old-depth/maximum and fresh-split probability space. `longHeight` is child-first, exactly as in the source; the actual ordered-pair swap law identifies the uniformly surviving root. The stronger complete-tree and history coupling is now certified under I2. Full build, axiom audit and independent source/body review passed. |
| I4 | 407–417, `eq:couplingmadeeasy` | The two maximum decompositions and definitions of $\Delta_n,Z_{m,n},\hat Z_{m,n}$. | **Complete.** `componentImbalance`, `sourceZ`, `sourceHatZ` and `source_decompositions_joint` give the exact two identities on the same verified height model, pointwise and with both actual word marginals. Positive-part order is equivalent by commutativity of maximum. |
| I5 | 419–425 | Both remainder positive-part expectations tend to zero. Includes the displayed stochastic bounds, $H(R_m)\leq m$, and domination by the height of an RRT of size $\lfloor n/2\rfloor$. | **Complete by an alternative decay proof.** `tendsto_meanZPositive_paperPrefix` and `tendsto_meanHatZPositive_paperPrefix` prove both exact full-floor limits. The two `source…Positive_strict_tail_le_comparison` exports prove the displayed stochastic bounds for every real threshold against the actual independent product heights with event $H_{\lfloor n/2\rfloor}\leq H_m$. `RRTSplit.residual_uniform_tendsto_zero` supplies decay without requiring the sharp L1 rate. Actual support and larger-component comparisons are proved. |
| I6 | 427 | Uniform bound $\mathbb E\lvert\Delta_n\rvert=O(1)$ from L2. | **Complete.** `RRTSplit.uniformHeightGap` bounds the first absolute moment of the actual uniformly split independent component heights uniformly in $n$. The proof averages the critical-center absolute-deviation bound and the exact uniform-size logarithmic defect, giving $2(B+e)$. This is an alternative proof of I6 using E1; the separate tail statement L2 is not inferred from it. Full build, axiom audit and independent review passed. |
| I7 | 428–435 | The two deterministic positive-part inequalities; expected gap equals $\mathbb E[(h(V_m)-h(U_m))_+]+O(1)$, and this is half the expected absolute difference plus $O(1)$ by exchangeability. | **Complete.** `TwoSeedCoupling.integral_depthMaximum_positive_gap` proves the exact exchangeability identity for distinct vertices in the same original RRT. `freezeAttachExpectedGap_absolute_error` bounds the difference from half the expected absolute depth gap by $1+2\mathbb E\lvert\Delta\rvert+\mathbb E Z_++\mathbb E\hat Z_+$. `freezeAttachExpectedGap_floor_bounded_error` gives the source bounded error along the full floor index, using the actual joint height laws and proved remainder limits. Built, axiom-audited and independently reviewed. |
| I8 | 437 | The expected absolute depth difference diverges, deduced from the nondegenerate normal limit E4. Uniform integrability is unnecessary for this lower-bound divergence, but the implication needs proof. | **Complete by an alternative proof.** `RRT.tendsto_expectedDistinctDepthGap_atTop` and `tendsto_expectedTwoSurvivorGap_atTop` prove the actual same-tree and source-prefix divergences. The quantitative lower bound is $\sqrt{\mu_m}/16-1$, where $\mu_m=H_{m+1}-1$. Actual marginal moments and bounded tree-mean fluctuation replace the CLT; E4 and the paper's CLT implication are not checked by this route. Full build and axiom audit passed on 1 November; independent actual-body review PASS. |
| I9 | 440–443, `eq:cvinfinity` | Expected deletion gap tends to positive infinity along $m=\lfloor n^{1/9}\rfloor$. Stronger than the existential main statement and used again in item (ii). | **Complete by an alternative proof.** `freezeAttachExpectedGap_floor_tendsto` proves the actual-word gap diverges along the full natural continuation index, with the exact `paperPrefixSize` floor of the real ninth root. `PaperPrefixSize` proves $m^9\leq n<(m+1)^9$ and eventual $n\leq m^{18}$. The actual depth-gap bound absorbs the coarse split error; the genuine residual is uniformly bounded over $n\geq m^9$. Full build and axiom audit passed; independent actual-body review PASS. |
| LP1 | 454–462 | Union bound at $(e/2)\log n$, eventually centered deviations of at least $(3e/8)\log n$, and the resulting $n^{-1/8}$ estimate. Correct the independent-copy typo at line 461 (finding SF5). | **Complete in the corrected SF5 form.** `comparisonLaw_threshold_union_bound` proves the actual product union bound. `eventually_paper_mean_thresholds` and `eventually_paper_centered_event_inclusions` prove both exact mean margins and same-copy event inclusions. `paper_height_comparison_polynomial` supplies the exact rate. The alternative proof uses the coarse absolute-mean error and boosted seed rather than sharp E1/E2. Strict-tail bridges use $T-1$ and $T+1$ explicitly. Built, axiom-audited and independently reviewed. |
| LP2 | 465–470, `bound:esp_In-n` | A constant $C>0$ bounds $\lvert\mathbb E H(R_n)-\mathbb E H(R_i)\rvert$ by $-C\log((1+i)/(1+n))+C$ uniformly for $n\geq1$, $0\leq i\leq n$. | **Complete.** `RRT.meanHeight_logarithmic_increment_ratio` proves the exact logarithmic-ratio bound with one positive constant, including all $0\leq i\leq n$ and also $n=0$. The actual uniform critical mean error and the center increment bounded by $e(\log(n+1)-\log(i+1))$ discharge the source argument. Built, axiom-audited and independently reviewed. |
| LP3 | 471–479 | Four-term decomposition of the split-height difference, symmetry of the uniform split, union bound, and conditioning arguments. | **Complete.** `RRTSplit.heightPair_tail_le_sampled_deviations` proves the four-term union bound and exact conditioning reduction under the actual first-edge split law. `heightPair_tail_le_maximum_and_ratio` gives the displayed finite-maximum/ratio-event bound. The sampled component law retains the true uniform size tag; reflection on its exact support justifies both factors of two, including zero-sized components. Built, axiom-audited and independently reviewed. |
| LP4 | 480–482 | Explicit two-exponential tail bound $2c e^{-k/(12e)}+2e^{1-k/(4C)}$, including the discrete-uniform tail bound; choose common positive constants for L1/L2. | **Complete.** `RRTSplit.uniformIndexLaw_ratio_le` proves the exact shifted discrete-uniform ratio count. `heightPair_two_exponential_tail` gives the source two-exponential formula; `paper_height_comparison_and_split_tails` explicitly chooses the same positive constants for L1/L2. Built, axiom-audited and independently reviewed. |

## Proof of Proposition 1.1(ii)

| ID | Source | Obligation | Current coverage |
| --- | --- | --- | --- |
| II1 | 491–507 | Joint prefix/grafting coupling for all three possible frozen vertices and the comparison tree, with the frozen extra child retained in case (a). | **Complete.** `TaggedGraftProcessSource` supplies both full original-word histories, literal shared-prefix recovery, an independent uniform case tag against the entire old history/pair/master, the actual source joint component law, and all three full graft graphs. The frozen extra child remains in case (a); equal heights do not merge vertex-ID cases. Independent final source/body review PASS; current full build and permitted-axiom audit passed. |
| II2 | 517–525 | Each freezing case has probability $1/3$, with the needed independence from the other coupling variables. | **Complete at the actual height-coupling level.** `taggedHeightModelLaw_joint`, `caseTag_independent_data` and `taggedHeightModelLaw_restrict_case` give a uniform `Fin 3` tag independent of all old data and fresh split, and branch restrictions of mass $1/3$. `actual_tagged_profile_kernel` identifies the tag with the actual frozen vertex; `taggedHeight_marginal` supplies the true full-word height law. The stronger full-tree/history assertion is now certified under II1. |
| II3 | 529–532, `eq:case1Pr1/3` | In case (a), heights agree when $I_n\ne0$, otherwise differ by at most one; conditional expected height bound with error $1/(n+1)$. | **Complete.** `caseHeight_zero_eq_of_size_ne_zero` retains the genuine split-size tag and proves equality in case (a) when it is nonzero; `firstEdgeSplit_first_height_pos` transports the positivity implication to the actual RRT split. The pointwise error is at most one, the exact first-component zero-height mass is $1/(n+1)$, and `caseHeightLaw_zero_mean_le` gives the precise conditional-mean bound for every $n\geq0$. Built, axiom-audited and independently reviewed. |
| II4 | 534–537, `eq:case2` | Case (b) height difference at most one and its conditional expected bound. | **Complete.** `caseHeight_one_abs_sub_baseline_le` proves the pointwise absolute height difference at most one, and `caseHeightLaw_one_mean_le` gives the conditional-mean bound on the same genuine height model. Built, axiom-audited and independently reviewed. |
| II5 | 539–551, `eq:case3` | Case (c) reverses the divergent gap of item (i); averaging yields divergence to minus infinity and M1ii. The self-reference to item (ii) at line 539 should refer to item (i). | **Complete.** `case_two_expected_difference` identifies the normalized case-(c) mean difference with the negative freezing/attachment gap; `case_two_expected_difference_floor_tendsto` proves its full floor-indexed limit at minus infinity. The actual branch has mass $1/3$ by II2. The final averaged limit `attachFreezeExpectedDifference_floor_tendsto` and M1ii were already proved. The line 539 self-reference is read as item (i). Built, axiom-audited and independently reviewed. |

## Proof of Proposition 1.1(iii)

| ID | Source | Obligation | Current coverage |
| --- | --- | --- | --- |
| III1 | 564–569 | First-edge component coupling and correct $n$ versus $n+1$ indexing. The smaller sequence has only $n-1$ remaining attachments after the shared three-vertex setup, so this description is for $n\geq1$. | **Complete for the source range $n\geq1$.** `RemoveAttachTreeCoupling.source_full_tree_coupling` with `sampleLaw_graphs`, `sampleLaw_orderedSeeds`, the prefix/master joint-product laws and `sampleLaw_ae_prefix_components` realizes the exact two words using one actual master and its actual same-parent prefix. Parametrization $n=k+1$ gives continuation lengths $k+1$ and $k$. Seeds are ordered by birth; all old and new parent/freezing data are retained. The otherwise unspecified joint law of the two prefixes is chosen independently. Independent final source/body review PASS; full build and permitted-axiom audit passed. |
| III2 | 587–590, `eq:HRn` | RRT height is $\max(H(T_n^1),1+H(T_n^2))$. | **Complete.** `RRTSplit.treeLaw_height_split` and `Describes.height_eq` identify the actual tree height with the maximum of the heights of its actual, canonically relabelled first-edge components, including the offset one. Reindex $n+1$ to the source $n\geq1$. Present in the current build and axiom audit; independent source/code review confirmed this previously unrecorded coverage on 31 October. |
| III3 | 592–596, `eq:ht-Tx-hat-iii` | Expected smaller-tree height is $\mathbb E H(R_n)+1/2$. | **Complete.** `removalShort_expectedHeight` proves the exact actual-word mean identity for every $n\geq1$, using the one-seed law and the two equally likely prefix states. |
| III4 | 598–608 | Five-term mixture for expected larger-tree height and its maximum simplification, including the height-one correction term. | **Complete.** `HeightProfile.long_word_law` proves the five-configuration profile mixture; `removalLong_expectedHeight_mixture` identifies its actual mean with the already proved `heightMixture`. The maximum of all vertices, including the frozen height-two vertex, is retained. |
| III5 | 609–621 | Partition into events $A_n,B_n,C_n$, the expectation decompositions, and final identity with $\mathbb E H(R_{n+1})+1/3$ plus the two $1/6$ correction probabilities. The intermediate line 617 needs SF1's correction. | **Complete in corrected form.** The scalar cases/partition identities in `HeightAlgebra`, together with the actual seeded mixture, give `removalLong_expectedHeight`: mean $\mathbb E H(R_{n+1})+1/3$ plus the tie probability divided by six and $1/(6(n+1)!)$. SF1 remains a correction to the printed intermediate C-case. The full labelled-tree coupling is now certified under III1. |
| III6 | 622–627 | Exchangeability of the first-edge components and bound $\mathbb P(H(T^1)=H(T^2)+1)\leq1/2$. | **Complete.** `RRTSplit.pairLaw_swap` proves exchangeability of the true full component pair after forgetting its size tag; `heightPairLaw_swap` projects it to heights, and `heightPairLaw_tie_le_half` gives the mass bound $1/2$, including the zero-sized endpoints. |
| III7 | 628–634, `eq:HeightComparison` | Expected height comparison with $-1/12$, RRT expected increment, and the factorial correction. | **Complete.** `removal_expectedHeight_comparison` proves the actual mean difference bound with $-1/12$, the RRT mean increment and the factorial correction, for every $n\geq1$. |
| III8 | 635 | Height-one probability $1/(n+1)!$ tends to zero. | **Complete.** The actual RRT height-one probability is now proved in `RRT.height_one_mass`; `inverse_factorial_tendsto_zero` supplies its zero limit. Focused build passed; covered by the 31 October 2026 integrated build and audit. |
| III9 | 637–649, `eq:dif`, `eq:HeightIncrease` | RRT height increment is zero or one, its expectation equals the probability a uniform vertex is deepest, and this expectation tends to zero. Uses E1 and corrected E5. | **Complete.** `RRT.meanHeight_increment_eq_integral` identifies the true mean increment with the conditional deepest-parent fraction. `depthHeightLaw` samples the parent depth and the height of the same tree; its first marginal is the actual uniform-vertex depth law, and `meanHeight_increment_eq_deepest_probability` gives the exact probability identity. `meanHeight_increment_tendsto_zero` proves the limit using the new weak height lower tail at $(11/10)\log n$ and proved E5. The deterministic zero/one increment and deepest-parent criterion were already proved in `Height`. This proof bypasses E1; the sharp estimate is separately certified under E1. |
| III10 | 561, 627–649 | Strict expected-height reversal for all sufficiently large $n$, stronger than M1iii's existence claim. | **Complete.** `removal_reversal_eventually`, exported as `Paper.proposition_1_1_iii_eventually`, proves strict reversal for every sufficiently large $n$ from III7, the vanishing actual mean increment and the factorial correction. No numerical witness or sharp RRT height estimate is assumed. |
| III11 | 661–662 | Despite the expectation reversal, the smaller-tree height fails to stochastically dominate the larger-tree height; for $n\geq1$ the two height-one probabilities are $1/(2n!)$ and $1/(3(n+1)!)$. | **Complete.** `removalShort_height_one` and `removalLong_height_one` prove the exact real masses $1/(2n!)$ and $1/(3(n+1)!)$ for $n\geq1$. `removal_not_heightLE`, exported as `Paper.removal_not_stochastic_domination`, disproves `Word.HeightLE (removalLong n) (removalShort n)` at upper-tail threshold two. The zero-height event is explicitly excluded for the actual admissible words; the $n=0$ formulas are not claimed. |

## Reverse forest construction and coupling

| ID | Source | Obligation | Current coverage |
| --- | --- | --- | --- |
| F1 | 676–702, Algorithm 2 | Well-defined reversed forest process, uniform ordered distinct pair selection for every attachment, singleton addition for a freeze, and unique terminal tree. Includes case $S_m=0$. | **Complete** (well-posedness of the reverse construction): actual graph-forest and ordered-list processes, legal uniform distinct pair selection, singleton addition, root counts, and unique terminal component, including terminal extinction. The Algorithm 3 comparison is replaced by the law-level M3 proof; see M3 and the proof departures. Covered by the 31 October 2026 integrated build and audit. |
| F2 | 684 footnote | The final-tree law is invariant under the order of ancestral blocks and the position of added singleton blocks. Essential because Algorithm 3 changes the order. | **Complete.** `ReverseOrdered.map_lawAfterWithOrdering` and `treeLaw_order_independent` identify the full rooted labelled-forest law at every phase under arbitrary initial, state/time-dependent and freshly sampled-pair-dependent ordering policies certified to preserve the underlying forest. The actual uniform pair kernel, fallback below two roots and horizon hold are retained. Arbitrary permutations, front singleton insertion and distinguished receiver relocation are explicit instances. Full build/axiom audit and independent actual-body review passed; this does not identify the delayed comparison process in C4/C5. |
| F3 | 684, 706 | Every reversed forest has exactly $S_i$ components. | **Complete.** Root-count invariants and legal pair cardinalities for actual graph and ordered forest laws compiled. Covered by the 31 October 2026 integrated build and audit. |
| C1 | 720–730 | Deletion sequence remains valid; active profiles line up; the post-deletion tails can be coupled identically. | **Complete.** Validity, attachment counts and active-profile alignment are proved by `FirstPeakDeletion`. `orderedHistoryLaw_deletion_tail` transports the complete actual common-tail ordered history by the explicit frozen-label permutation, including the actual root order and all inter-stage dependence. Active labels are fixed and frozen insertion labels are shifted by two exactly on the source tail. Full 4,187-job build, 4,511-declaration permitted-axiom audit and independent final-body review passed. |
| C2 | 732–755 | Initialization cases have valid indices, forest sizes and update laws; the distinguished singleton is removed in the use-zero case. | **Complete.** `ReverseDistinguishedInitialization` proves all three actual join/order cases, singleton-component survival exactly when the distinguished vertex is avoided, and original sampled-position storage. `ReverseInitializationValidity` supplies freshness and exactly $k$ incoming roots from the actual admissible long-word tail, then proves the genuine initialization bind is a probability law for $k\geq1$, with source indices, sizes and flags valid almost surely. The $k=1$ flag is necessarily used. C1's shortened-label common-tail identification remains separate. Built, axiom-audited and independently reviewed. |
| C3 | 757–795 | Inductive updates preserve index validity and the invariant that the isolated distinguished singleton is present exactly when $M_j=0$. | **Complete.** `ReverseDelayedDynamics` constructs the actual fresh-pair transition and finite iteration. `sourceDelayedLaw_ae_valid` preserves the full forest, cardinality, position-index, singleton-use and unused matching invariant at every source phase; `sourceDelayedLaw_probability` proves these are actual probability laws. The pending branch is identified with the actual source join kernel after consuming the stored pair, and joins cannot create a new distinguished singleton. C4/C5 retain the separate original-process history-law obligations. Built, axiom-audited and independently reviewed. |
| C4 | 798 | The first forest process has Algorithm 2's law, despite changed list order. | **Complete.** `ReverseOrdered.sourceLongerHistoryLaw_eq` identifies the entire labelled-graph history of the first process with Algorithm 2: the actual incoming ordered common-tail history, the insertion, the first join, and every remaining join, including $k=1$. The proof uses exact projected kernels and finite-history concatenation, preserving dependence between phases rather than only their marginals. Full build, axiom audit and independent complete-body review passed. |
| C5 | 798 | The delayed pair in case (B), conditional on that case and appropriate comparison-process past, is uniform over distinct nonzero indices; the second forest process has Algorithm 2's law. Do not assert independence from all past *joint-process* choices: the pair is explicitly a previously sampled pair. | **Complete in the corrected SF6 form.** `delayedHistoryLaw_shorter_pendingTag` proves the actual full comparison-history/pending-pair product invariant. `sourceShorterTaggedHistoryLaw_eq` includes the entire original common-tail past at every phase; conditional on being pending, the original stored pair is uniform over distinct positive positions and independent of that comparison history. Its irrelevant old indices are discarded after use. `sourceShorterHistoryLaw_eq` and `sourceDelayedLaw_shorter_treeLaw` identify the full correctly relabelled shortened-word history and terminal forest law. No independence from the full joint-process past is asserted. Full build, axiom audit and independent final-body review passed. |
| C6 | 800 | Delayed forest matching invariant when $M_j=0$. | **Complete.** `prependLabel_joinChoice_commute` and `initializationChoice_pending_matching` prove exact labelled forest/list matching. The actual finite dynamics preserve the unused-state invariant; `sourceDelayedLaw_pending_shorter` additionally identifies the adjacent-phase shorter forest by its deterministic consumed-pair construction at every nonterminal pending phase. Terminal pending states are impossible. Full build, axiom audit and independent review passed. |
| C7 | 879–884 | $M_0=1$, the first distinguished-vertex-use index $j_1$ exists, and at that index the lists agree except for one tree with a singleton grafted above/below it. | **Complete.** `sourceDelayedLaw_terminal_used` proves $M_0=1$. `sourceFirstUseHistoryLaw_firstUse` constructs the first true flag on the actual complete finite history, retaining the incoming forest. `FirstUseAt.reverse_max` converts it to the source maximum index $j_1=k-1-r$. `FirstUseGraft` and its initializer/transition theorems give the exact original sampled positions, selected component slot, complete rooted-forest graft and root order, including the initial-use and $k=1$ cases. The source-history current marginal is explicitly identified with the actual delayed law. Full build, axiom audit and independent final-body review passed. |
| C8 | 886 | Componentwise height domination at $j_1$ is preserved under synchronized grafting, and yields terminal domination M3 after E6. | **Complete by the source delayed coupling.** The exact first-use graft supplies componentwise height domination, and `delayedLawAfter_ae_usedHeightDomination` preserves it through actual synchronized joins. `sourceDelayedLaw_terminal_maxDepth_le` proves the terminal pathwise comparison. `sourceCoupling_heightLE` identifies both actual word-height marginals on that same joint law and derives the required stochastic domination using the verified forward/reverse law bridge. Thus this source argument is now checked in addition to the earlier independent law-level proof of M3. Full build, axiom audit and independent final-body review passed. |

## Proof of Theorem 1.2

| ID | Source | Obligation | Current coverage |
| --- | --- | --- | --- |
| H1 | 896–900 | Define $r_n=\lfloor n/(3\log n)\rfloor$ eventually positive; split all admissible sequences by their maximum active count. | Complete: `eventually_populationCutoff_pos`, exact source-range `Word.population_dichotomy`, and the low-cap bridge. |
| H2 | 902–906, `eq:case1` | Repeated first-peak deletion and domination by a pure RRT prefix. The stated prefix of $r_n$ attachments has an off-by-one; a justified index is $r_n-1$ (SF2 below). The literal printed proof step remains unresolved until corrected. | **Complete in corrected form.** `Word.high_population_domination` (unconditional) derives $\operatorname{HeightLE}(R_{r-1},\mathbf x)$ for every admissible word reaching $r$ active vertices, using the proved Theorem 1.3; `Word.high_population_expectedHeight_ge` gives the mean comparison. The printed index $r_n$ remains uncertified (SF2). Built and audited 31 October 2026; independent read-only review PASS. |
| H3 | 907–909 | Uniform high-profile expected-height lower bound using the RRT mean expansion. The corrected index $r_n-1$ has the same needed asymptotic expansion. | **Complete in the corrected SF2 form.** `highPopulation_mean_bounded_error` proves the sharp mean expansion at the actual comparison edge count $r_n-1$. `highPopulation_mean_log_ratio_expansion` gives the displayed logarithmic-ratio expansion explicitly, and `tendsto_highPopulation_mean_gap` proves its divergent margin above the target threshold. Existing corrected stochastic reduction then supplies the uniform high-profile expectation bound. The literal printed $r_n$ domination is not asserted. Full build, audit and independent review passed. |
| H4 | 910–915 | The centered threshold tends to minus infinity and tightness gives a uniform high-profile probability lower bound tending to one. | **Complete in corrected form, by an alternative proof.** `tendsto_highPopulation_center_gap` proves the corrected threshold limit; `highPopulation_uniform_probability_of_deficit`, instantiated by the actual bounded deficit in `uniformHeightClaims`, proves the uniform high-branch conclusion. The printed $r_n$ domination remains uncertified under SF2/H2; sharp centered tightness is retained under E1. Full build/axiom audit and independent milestone review passed. |
| D1 | 917–919 | Terminal active-vertex depth law is a sum of independent Bernoulli variables on attachment indices; handle terminal extinction by deleting its final freezing step, preserving the height law and attachment count (SF3 below). | Complete in corrected endpoint form: `Forward.uniformActiveHeightLaw_eq_bernoulliSum` and `Word.exists_surviving_bernoulli_representation`, with explicit independent coordinate laws. |
| D2 | 920–923 | Uniform low-profile stochastic lower bound by $\operatorname{Bin}(n,1/r_n)$. | **Complete.** Proved: `Word.binomial_tail_lower_bound` for the actual maximum-height law, including terminal extinction. Mathlib binomial identification, focused build, and independent source review passed; covered by the 31 October 2026 integrated build and audit.|
| D3 | 924–925 | Low-profile expected-height lower bound $n/r_n\geq3\log n$ and resulting main bound. | Complete: low-branch expectation bound, uniform version, and exact-floor inequality `log_scale_le_div_populationCutoff`. |
| D4 | 941–945 | Bennett tail bound, comparison $s_n\geq3\log n$, monotonicity/positivity properties of $g$, and uniform failure bound $\exp(-3\log n\,g(1-e/3))\to0$. | Complete: final uniform failure bound, positive rate, and zero limit proved in `LowPopulationAsymptotic`; `Scaling.strictMonoOn_bennettRate` now also proves auxiliary rate monotonicity. D2 supplies the binomial comparison. Covered by the 31 October 2026 integrated build and audit. |
| D5 | 895–946 | Assemble the two cases into the single uniform probability and expectation statements, with minima justified by A4. | **Complete.** `uniformHeightClaims` and `Paper.theorem_1_2` prove both exact claims without an extra estimate premise; the finite-family minima equivalences in `FamilyMinima` justify their minimum formulations. Full build/axiom audit and independent source/route review passed on 1 November. |

## External results explicitly asserted or essential

These are retained as unresolved dependencies or directly asserted cited claims,
not silently assumed axioms. A verified library theorem, a faithful proof, or an
explicitly documented change of proof route is needed. Reading the cited paper
is still needed before approving precise hypotheses not reproduced here.

| ID | Source | Cited assertion and use | Current coverage |
| --- | --- | --- | --- |
| E1 | 237–242, `eq:H` | RRT height equals $e\log n-(3/2)\log\log n+O_{\mathbb P}(1)$ and its mean has the same expansion with $O(1)$; cites AF13 Corollary 1.3 and PS22 (1.3). Needed for M2 and all counterexample asymptotics. | **Complete.** `RRT.sourceMeanHeightExpansion` gives a uniform bounded error at the exact source center for every $n\geq2$; `RRT.sourceHeight_tight` gives uniform tightness there. `PWIT.criticalClockUpperBound_actual` discharges the upper estimate under the actual PWIT law. The lower seed/deficit, logarithmic-ballot first crossing, and actual clock-to-RRT transfer supply both sides without an unproved estimate premise. Full 4,172-job build and 4,260-declaration permitted-axiom audit passed; independent statement and actual-body review PASS. This verifies the required estimates by the documented route, not every argument in AF13 or PS22. |
| E2 | 449–452, `eq:AF` | Uniform centered RRT exponential tail at rate $1/(3e)$ for all $n,k\geq0$, citing AF13 Corollary 1.3. | **Complete.** `RRT.meanCenteredHeightConcentration` proves the exact rate $1/(3e)$, with one positive uniform constant, for every $n\geq0$ and every nonnegative real threshold. The critical upper tail, finite lower-seed boost and bounded critical mean error are all proved. Full build, axiom audit and independent actual-body review passed at the critical-height milestone. |
| E3 | 385, 564–569, 622 | First-edge split of an RRT: uniform component edge count; conditional independent RRT components; exchangeability. Called well known but must be proved or found in a verified library. | **Complete.** `RRTSplit.first_edge_split_joint_law` proves the actual full-state joint law: uniform size tag, then conditionally independent RRT components. `pairLaw_swap` now supplies the previously missing exchangeability after forgetting the tag; `heightPairLaw_swap` gives its height projection. Zero-edge component endpoints are included. The root import closure builds and the independent roadmap implementation review passes. |
| E4 | 437 | For two distinct uniform vertices of the same RRT, depth difference divided by $\sqrt{\log m}$ converges in law to $N(0,2)$; cites Lodewijks Theorem 2.4 with $k=2$, $a_1=a_2=0$. | **Complete.** `RRT.depthDifference_central_limit` and `RRT.depthDifference_tendstoInDistribution` prove the exact distinct-uniform-vertex difference limit for the same actual RRT, including the root, divided by $\sqrt{\log n}$, with limit $N(0,2)$. Direct recurrence and characteristic-function proof, followed by Mathlib Lévy convergence; the cited Lodewijks proof is not claimed checked. Independent source/body review PASS, focused twelve-export axiom probe, current full build and global permitted-axiom audit passed. |
| E5 | 648 | Uniform RRT vertex depth is asymptotic to $\log n$ in probability (ratio form); cites Devroye Theorem O1. Literal source wording lacks normalization; see SF4. | Complete for the corrected normalized uniform-vertex statement: `RRT.uniformVertexDepthLaw_deviation_tendsto_zero`; required upper tail also proved. Direct forward-MGF/harmonic proof; see SF4 and cited-source checks. |
| E6 | 676, 706 | Forward frozen tree and reverse forest final tree agree in law as rooted active/frozen-labelled trees; cites BBKK23+ Theorem 8. | **Complete as a law identity.** Canonical full-state equality (`CanonicalTree.reverseStateLaw_eq_forward_treeLaw`), binary-label projection, and actual ordered-list terminal-height transport (`Word.heightLaw_eq_orderedReverseHeightLaw`, `Word.heightLaw_eq_runBackward`), including extinction. The theorem cited from BBKK23+ is thus proved here by a point-mass computation rather than assumed. Built and audited 31 October 2026; independent source reviews passed (29 and 31 October). The deletion coupling itself is M3/C-rows. |
| E7 | 917–919 | Uniform active terminal vertex depth has the Bernoulli-sum law; cites BBKK23+ (5), with nonempty active set required. | Complete before extinction: actual active law equals the explicit independent Bernoulli sum. The finite endpoint wrapper supplies the corrected application after terminal freezing. |
| E8 | 330–339 | Alternating-tree height divided by $n$ converges to $1/2$ in probability; cites BBKK23+ Theorem 3(3). | **Complete.** Proved by `alternating_height_tendsto_half`; focused build and independent source review passed. Covered by the 31 October 2026 integrated build and audit. Direct forward upper/lower-tail proof, not a verification of the cited paper’s argument.|
| E9 | 207 | Under unspecified technical assumptions, active population of order $n^\alpha$ gives height of order $n^{1-\alpha}$ for $\alpha\in(0,1)$, citing BBKK25+. This contextual claim is retained with the reciprocal-profile hypotheses identified in the cited-source checks below. | **Complete.** Proved under the cited reciprocal-profile hypotheses by `Scaling.height_scaling_limit_positive_horizons` and its actual-vertex-count version. All 20 modules compiled; exact-type and permitted-axiom probes passed. Independent source/route review passed; integrated in the root and covered by the 31 October 2026 build and audit.|
| E10 | 928–935 | Bennett concentration statement (B1–B2), citing Boucheron–Lugosi–Massart Theorem 2.9. | Complete for the stated inequality: `Paper.bennett`, duplicating B1/B2. The cited book proof was not reviewed. |

The historical/model-motivation summaries at 182–186 and 676 contain no precise
additional theorem statement in this source. The abstract's two mathematical
claims duplicate M1iii and M2; lines 205, 207, 235, 267–271, and 280–281 summarize
other inventoried results and routes rather than adding separate targets.

## Cited-source checks

The independent reviewer read the following source statements on 29 October
2026. These checks refine the obligations; they do not supply Lean proofs.

- **E1/E2:** [Addario-Berry–Ford, Corollary 1.3](https://arxiv.org/pdf/1012.2544v3)
  uses a tree with $m$ vertices. It gives the mean expansion and a centered
  exponential tail at every fixed rate below $1/(2e)$. Set $m=n+1$ for this
  paper's edge count and enlarge constants for small thresholds. The relevant
  [Pain–Sénizergues preprint](https://arxiv.org/pdf/2101.01156v2) was also read;
  its equation numbering does not directly match the manuscript's citation.
  AF13 supplies the needed assertion. Only the indicated source statements and
  surrounding proof excerpts were checked, not their complete proofs.
- **E4:** [Lodewijks, Theorem 2.4](https://arxiv.org/pdf/2204.09032v4) requires
  two distinct uniformly sampled vertices. Choose the degree thresholds
  identically zero to remove conditioning, then subtract the joint independent
  normal limits. Merely setting their limiting ratios to zero is insufficient.
  Convert $m$ edges to $m+1$ vertices. The extra diverging-degree hypothesis
  concerns the later label assertion, which is not needed here. The theorem's
  proof was not checked.
- **E5:** [Devroye, Theorem O1](https://luc.devroye.org/devroye_recordsBST_1988.pdf)
  concerns the last-inserted vertex. Its record-count law and harmonic moments
  imply normalized concentration. A uniformly sampled vertex needs an
  insertion-index mixture argument or a separate direct proof. The record-law
  proof and moment/limit discussion were read; they are not formal proof
  evidence. SF4's missing normalization remains a separate issue.
- **E6:** [Bellin–Blanc-Renaudie–Kammerer–Kortchemski, Theorem 8](https://arxiv.org/html/2308.00493v2)
  includes the weak horizon $m\leq\tau$, hence terminal extinction. It identifies
  labelled-tree laws after merging the distinct reverse active labels into one
  active label. Freezing-time vertex and birth-time edge labels survive. The
  current forward identifiers require a faithful common projection or
  isomorphism. Algorithms 1–2, the theorem, and the start of the counting proof
  were read; the full cited proof was not reviewed. The adapted local canonical
  equivalence and its ordered-list height projection have now compiled.
- **E9:** [Scaling Limits, Theorem 2.1](https://arxiv.org/html/2308.00484v3)
  uses triangular schedules surviving beyond the operation horizon $m$ and
  $0<\alpha<1$. Its assumptions include convergence of
  $m^\alpha/S^m_{\lfloor mt\rfloor}$ to $1/f(t)$ in $L^1([0,1])$, together with
  convergence of squared integrals on every compact subinterval of $(0,1)$.
  The reciprocal profile belongs to $L^1\cap L^2_{\mathrm{loc}}$.
  The height divided by $m^{1-\alpha}$ converges in every $L^p$, $p\geq1$, to
  $\int_0^1(2f(t))^{-1}\,dt$. Lemma 4.2 gives vertex count asymptotic to $m/2$;
  conversion preserves the exponent and changes the constant. The statements
  were checked, not their proofs. This specifies the retained contextual
  obligation without treating population-order language as sufficient.

## Open questions and proved assertions in that section

| ID | Source | Classification | Current coverage |
| --- | --- | --- | --- |
| Q1 | 954–956 | Open question: uniform expected-height domination by the RRT for every $n\geq3$. Do not claim as proved. | Open question; no proof claimed |
| Q2 | 957–960 | Open optimization question about the least height truncation $h_n$ giving stochastic domination for every sequence. Do not claim the optimal function is known. | Open question; no proof claimed |
| Q2a | 960 | Substantive asserted result: any such thresholds satisfy $h_n\to\infty$. A proof is only described as an extension of the earlier argument; retain as an obligation. | **Complete.** `question2_threshold_divergence`, exported as `Paper.question_2_threshold_divergence`, proves the faithful `Question2ThresholdDivergenceClaim` for arbitrary real thresholds under the actual all-real-tail uniform clipped domination property. `RRTBoundedHeight` proves each fixed-height CDF decays faster than every geometric sequence; the alternating star mass contradicts any bounded threshold subsequence. No extra lower-bound hypothesis or existence/optimality claim is introduced; Q2 remains open. |
| Q3 | 961–963 | Open optimization question about the least attachment count $N_n$ giving domination of the $n$-edge RRT for every choice sequence. | Open question; no proof claimed |
| Q3a | 964 | Substantive asserted lower bound $\liminf N_n/(n\log_2n)\geq1$, derived from $1/n!\geq2^{-(N_n-1)}$; includes the logarithmic-factorial asymptotic needed for this implication. | **Complete.** `question3_lowerBound` (export `Paper.question_3_lower_bound`): for every sequence $N$ such that each tree with $N(n)$ attachments stochastically dominates the $n$-edge recursive tree, and every $\varepsilon>0$, eventually $N(n)\geq(1-\varepsilon)\,n\log_2 n$, i.e. $\liminf N_n/(n\log_2 n)\geq1$. Proof: dominating the alternating tree's height-one probability gives $n!\leq 2^{N-1}$ (`Alternating.factorial_le_two_pow_of_heightLE`, including $N=0$), then $n!\geq (n/e)^n$ from Mathlib's `Real.pow_div_factorial_le_exp`. The question itself (the least $N_n$) stays open. |

Commented-out source material, including 652–656 and the duplicate commented
lower bound at 963, is not a rendered claim and is not an extra obligation.
Questions Q1–Q3 are inventoried as questions, not proof obligations.

## Source findings and necessary proof repairs

### SF1 — Incorrect term in an intermediate expectation identity

At line 617, the summand on $C_{n+1}=\{H(T^1)>H(T^2)+1\}$ is written with
$H(T^2)$. The preceding maximum expression and the following consequence at 621
require $H(T^1)$. This is not merely a change of proof route: the literal displayed
identity is wrong. For deterministic heights $a=3,b=0$, the variable part of the
preceding maximum combination is $3$, while the displayed $C$ term gives $0$.
Record a correction and prove the corrected identity; do not mark the literal
source line as verified.

### SF2 — Off-by-one in the high-active-count reduction

At 902, maximum active count at least $r_n$ is claimed to permit a reduced
sequence starting with $r_n$ attachments. Since the count starts at one, reaching
$r_n$ gives a pure prefix with $r_n-1$ attachments. Removing a consecutive peak
cannot increase the maximum active count, so a sequence with maximum exactly
$r_n$ cannot be transformed by those removals into one starting with $r_n$
attachments. Such paths exist with arbitrarily many attachments (reach $r_n$,
then repeat freezing/attachment pairs). This diagnoses the combinatorial proof
step, not a counterexample to the main theorem. Using $R_{r_n-1}$ repairs the
asymptotic argument without changing either main statement.

### SF3 — Terminal extinction in the low-active-count argument

The admissible class allows $S_m=0$, but 917 chooses a uniform active vertex at
time $m$ and 919 assigns Bernoulli parameter $1/S_m$. When the terminal count is
zero, remove its final freezing step. The preceding count is exactly one, and
the height law and attachment count are unchanged. When the terminal count is
positive, use the entire word. On the surviving prefix, assign reciprocal
post-step population parameters to all coordinates and sum only the attachment
coordinates. The endpoint reduction and this representation are now proved by
`Word.exists_surviving_bernoulli_representation`.

### SF4 — Missing normalization in a cited depth limit

Line 648 literally says $h(U_n)$ converges in probability to $\log n$. The
required and standard assertion is $h(U_n)/\log n\to1$ in probability. The
unscaled difference does not tend to zero; depths have growing fluctuations.
Use the normalized statement or the sufficient upper-tail estimate, and record
the correction. This is a cited prerequisite, not evidence that Devroye's
published theorem itself is wrong.

### SF5 — Independent-copy typo in a displayed event inclusion

At 461, the left event contains $R^1_{\lfloor n/2\rfloor}$ but the right event
contains $R_{\lfloor n/2\rfloor}$. Those trees were defined to be independent;
the literal event inclusion does not follow. Keep the same copy on both sides,
or phrase the step as a probability inequality using equality of laws.

### SF6 — Coupling conditional independence needs the correct filtration

Line 798 calls the delayed pair independent of “all the previous choices.” It
is explicitly the already sampled pair $(A_{j+1},B_{j+1})$, so the mathematically
needed independence is from the past of the comparison forest process under the
relevant conditioning, not the full past of the joint construction. A formal
coupling proof must establish this precise marginal property. Ordering-invariance
F2 from the reverse-forest inventory also must be proved rather than assumed.

Minor exposition findings: line 539 should cite item (i), not itself; line 763
should refer to $\mathcal F^j$ rather than a free $\mathcal F^i$; line 235 writes
$\mathbb X^n$ rather than $\mathbb X_n$. The explicit star formulas in O2/O3 and
III11 should carry $n\geq1$, since they are false at $n=0$.

## Inventory reconciliation

The full rendered source was independently rescanned on 2 November 2026,
including its open-question section, footnote, and unnumbered displays. All
85 unique inventory IDs remain present: **82 completed non-question claims
and three open research questions**, with no omitted claim found. All four
final source/body reviews passed and are supported by the current 4,328-job
integrated build and 4,978-declaration permitted-axiom audit. The machine-readable
coverage summary is `verification/2026-11-02-coverage.json`.

Completion retains the explicit corrections and qualifications SF1–SF6 and the
documented proof departures. It does not certify erroneous printed formulas
literally, claim a proof of Q1–Q3, or certify cited arguments that were bypassed.
Publication-candidate checks, Comparator, independent kernel replay and full
Palomar verification are distinct from this completed mathematical inventory.
