# Independent review of the M2 roadmap

31 October 2026. Reviewer: independent AI agent `m2_inputs_review`, which did
not author the roadmap or exploratory interfaces. The reviewer read the source,
the relevant existing definitions and reductions, `M2_ROADMAP.md`, and
`exploration/HighPopulationInterfaces.lean`. Only this review file was written.
No Lean/Lake invocation was run by the reviewer.

Source: `main.tex`, Theorem 1.2 at lines 245–253, its proof at lines 894–946,
and cited assertions E1/E2. Its SHA-256 was independently checked as
`7b7d6ef6e2200b3129cbd4a74ef45c09fbf758643ce63489bf67f2aef93301f3`.

## Verdict and limits

**PASS for the mathematical plan and the proposed B1–B4 interfaces.** The
conditional implications in the exploratory file have the advertised meaning
on the actual RRT height laws. The discrete amplification, deficit argument,
corrected-index margin and final uniform assembly are mathematically sound.
The C1/C2 construction and renewal identities are consistent, and C4's time
inversion and constants check.

This is not a proof-completion verdict. The coordinator reports that the
exploratory file compiled cleanly; it contains definitions of propositions,
not proofs of its estimates. No new height theorem, axiom audit, kernel replay,
Comparator result or Palomar result is certified by this review. In particular,
the C3 barrier and overlap estimates remain substantial unresolved mathematics
to formalize. Their precise future declarations require the specified reviews.

## Statements and deterministic reduction

The proposed `lowerCenter` uses vertex count $n+1$, while the actual law
`Forward.heightLaw RRT.allAttach n` uses $n$ edges. Its regularization gives
$b_c(0)=0$. `lowerDeficit` is the integral of the nonnegative shortfall from
this center, and `ConstantSuccessSeed` places both constants before the
universal size quantifier. `UniformLowerDeficit` likewise has one constant
for all sizes. The implication `AssemblyTarget` concludes the existing exact
probability and expectation targets; the estimate premise is visible and is
not inserted into either paper target.

The corrected cutoff remains `highPopulationIndex`, corresponding eventually
to $r_n-1$. The existing size bounds imply the displayed margin

$$
b_c(m_n)-\operatorname{mainThreshold}(n)
\geq (5-e-c)\log\log n-e\log6-c\log3.
$$

Thus $0\leq c<5-e$ suffices, with $c=2$ leaving $3-e>0$. The proof must retain
this strict positive margin. Natural subtraction and integer subtraction agree
after the eventual positivity condition is established. Upper tails at real
thresholds transport through `Word.HeightLE` using `Nat.ceil_le`. The final
validity index is chosen independently of the word, as required by Theorem 1.2.

## Discrete amplification and integration

For $n\geq1$, the first-edge split has component edge counts $k,n-1-k$,
and vertex counts $k+1,n-k$ summing to $n+1$. The counts of indices having
both vertex counts at least $(n+1)/4$ are exactly the four values in the
roadmap; in particular their proportion is at least one half. For $c\geq0$,
the subtracted logarithmic term gives the asserted upper bound on center loss.
No monotonicity of the entire center function is assumed.

With $L=e\log4$, $\rho=1-p/2$ and $a_j=(1-p)\rho^j$, a central split has
conditional failure probability at most $a_j(1-p)$, by actual conditional
independence from E3. Outside the central set, the larger component gives the
bound $a_j$. Averaging gives at most $\rho a_j$. This is an induction on $j$
whose hypothesis includes all sizes. It is not a circular induction on the
tree size. At size zero the event is empty, including the boundary cases
$A=0$ and $j=0$; the case $p=1$ also causes no problem.

The finite grid estimate is valid even when the deficit is exactly a grid
multiple, with the strict events used in the roadmap. It yields

$$
D_c(n)\leq A+\frac{L(1-p)}{1-\rho}.
$$

The deficit is bounded by $\max(b_c(n),0)$ for each size, so integrability
cannot become an unproved client assumption. Enlarging $A$ to cover finitely
many sizes turns an eventual seed into the stated uniform seed, using only
nonnegativity of height. Markov and the deterministic margin then give the
probability conclusion, while integrating $H_n\geq b_c(n)-(b_c(n)-H_n)_+$
gives the mean conclusion. The low branch, including terminal extinction,
is already available for the final case split.

## C1/C2 construction and renewal sanity check

The proposed clock coordinates admit the required disjoint decomposition:
the coordinate at the root for its first birth; the later root clocks and
all subtrees whose first index is positive; and all coordinates below the
first child, whose first index is zero. Reindexing the latter two pieces
produces independent copies of the original clock family. Successive waiting
times, rather than cumulative sibling birth times, are the independent objects.

The geometric distribution is on the number of edges, with parameter
$e^{-t}$ and support starting at zero. If $F_n(h)$ denotes the true RRT CDF,
the stated convolution recurrence implies

$$
g_h(t)=e^{-t}+\int_0^t e^{-s}g_h(t-s)g_{h-1}(t-s)\,ds.
$$

The first-birth decomposition of the clock construction has the same equation:
the residual root tree has height bound $h$, and the first-child tree has
height bound $h-1$. The base case is $g_0(t)=e^{-t}$, including $t=0$.
Multiplication by $e^t$ converts the renewal equation to a linear integral
equation with the preceding height level as coefficient. Bounded measurable
solutions obtain their required continuity from that equation, so uniqueness
does not need an assumed continuity premise.

These are checks of the proposed construction, not completed existence,
measurability, reindexing or integral proofs. For implementation precision,
define a path born **by** time $t$ using `birth v ≤ t`, consistently with C3.
Using a strict inequality instead would require an additional no-atom bridge.

## C4 inversion and retained obligations

For $\ell=\log(n+1)$ and eventually positive
$d=\lceil b_2(n)-A\rceil$, the ceiling contributes at most $1/e$ to $d/e$.
When $A\geq1$, $d\leq e\ell$, and hence
$\log d\leq1+\log(1+\ell)$. These give exactly

$$
\frac d e+\frac{3}{2e}\log d+K
\leq\ell-\frac{1}{2e}\log(1+\ell)-\frac A e+\frac{5}{2e}+K.
$$

The choice $A\geq e(D+K)+5/2$ therefore puts the path event inside time
$t=\ell-D$. The geometric mean gives the tail loss at most $e^{-D}$ via the
natural event $N_t\geq n+1$. Size monotonicity bounds the geometric mixture
by the size-$n$ success probability plus that tail. No independence between
size and height is assumed. The stated choice of $D$ leaves success at least
$p_0/2$, and the finite prefix is absorbed as above.

C3's asserted first- and second-moment interfaces would suffice: summing
the proposed inequalities over the finite set of good paths gives
$\mathbb E Z_d^2\leq C_0\mathbb E Z_d$, then Cauchy–Schwarz gives positive
success probability. This review does **not** certify the missing barrier
estimates, their exact AF13 transcription, or the uniform overlap bound.

E1, E2, the sharp-expansion subclaim in H3, and the other retained source
obligations remain open. The roadmap correctly distinguishes a future proof
of M2 by this route from checking the paper's full cited asymptotic argument.
No existing coverage status should advance on the basis of this planning pass.

## B1 production review

31 October 2026, subsequent implementation review by the same independent
reviewer. **PASS for statement fidelity and the mathematical proof route of
B1.** Files read: `FreezingGrowth/RRTLowerCenter.lean`,
`FreezingGrowth/HighPopulationWeakCentering.lean`, and the changed
`FreezingGrowth/HighPopulationCentering.lean`. No Lean/Lake command was run
by this reviewer; mechanical validation is the coordinator's separate task.

The production APIs reviewed are:

- `RRT.lowerCenter`, `RRT.lowerCenter_zero`;
- `RRT.lowerCenter_sub_le_log_ratio`,
  `RRT.lowerCenter_sub_le_quarter`;
- `RRT.lowerDeficit`, `RRT.lowerDeficit_integrable`,
  `RRT.lowerDeficit_nonneg`;
- `highPopulation_lowerCenter_gap_lower`;
- `tendsto_highPopulation_lowerCenter_gap`;
- `tendsto_highPopulation_lowerCenter_two_gap`;
- the newly public `eventually_populationRatio_ge_four`.

The definitions reproduce the accepted regularized center and the positive
deficit under `Forward.heightLaw RRT.allAttach n`, with $n$ still counting
edges. The zero-size identity holds for every real $c$. Deficit integrability
and nonnegativity hold for every real $c$ and every natural $n$; integrability
is established directly by domination by the constant $\max(b_c(n),0)$.
No height asymptotic, probability seed or moment bound has been assumed.

The logarithmic size-loss inequality has the correct direction: for
$c\geq0$ and $k\leq n$, monotonicity of the regularized logarithmic correction
reduces the loss. The quarter-size theorem additionally requires precisely
$n+1\leq4(k+1)$, on vertex counts, and concludes loss at most $e\log4$.
It does not assert monotonicity of the center and does not exclude zero-edge
components when the quarter condition permits them.

The quantitative gap assumes only $c\geq0$, $\log n\geq1$, and the existing
size-ratio condition $n/(3\log n)\geq4$. It preserves the actual
`highPopulationIndex` and obtains the displayed coefficient $5-e-c$ without
substituting away its strict margin. The limit theorem adds
$c<5-e$, with $c$ fixed before the eventual size quantifier. The coefficient-two
specialization discharges this condition using $e<3$.

The visibility change exposes the existing deterministic eventual ratio
lemma under the name `eventually_populationRatio_ge_four` and updates its
old consumer. The corrected index, the sharp center `rrtHeightCenter`, and
the earlier sharp-center gap statements retain their mathematical content.

B1 supplies deterministic and integrability infrastructure only. The seed,
amplification, uniform deficit bound, final M2 conclusions, and retained
E1/E2 obligations are not proved by these modules. The paper inventory counts
therefore remain unchanged. No actionable mathematical finding was found
in the reviewed B1 code; axiom closures and current compilation evidence
must still be recorded from the coordinator's checks.

## B2a production review

31 October 2026, independent statement and proof-route review by the same
reviewer. **PASS for the B2a mathematical interfaces and their derivation
from the proved E3 law.** Files read: `FreezingGrowth/RRTSplitCDF.lean` and
`FreezingGrowth/RRTCentralSplits.lean`, together with the relevant definitions
in `RRTSplitIntegrals`, `RRTSplitSymmetry` and `RRTSplitSupport`. The coordinator
is handling serial compilation; this reviewer ran no Lean/Lake commands.

The exact APIs reviewed in namespace `FreezingGrowth.RRTSplit` are:

- `heightLaw_event_split`;
- `heightPairLaw_rectangle`, `heightPairLaw_real_rectangle`;
- `heightLaw_real_lt_succ`, `heightLaw_cdf_succ`;
- `centralSplits`, `centralSplits_eq_Ico`, `card_centralSplits`;
- `half_le_card_centralSplits`, `centralSplits_subset_range`;
- `larger_component_vertices`.

The event projection compares the actual height law with
$\max(H_{\mathrm{root}},H_{\mathrm{child}}+1)$, preserving the first-edge
offset. The rectangle law is the average of products of the genuine component
height marginals, obtained from E3's mixture of product measures. It does not
assert unconditional independence of the two heights. For a total of $n+1$
edges, the component sizes are $k,n-k$ with $k\in\{0,\ldots,n\}$, and the
normalizing coefficient is $1/(n+1)$.

The strict real-threshold identity consequently uses thresholds $t$ and
$t-1$, with no positivity assumption on $t$. Negative thresholds simply give
empty events on natural heights. The natural CDF identity uses thresholds
$h+1$ and $h$, avoiding an incorrect natural subtraction at zero. As a
mathematical endpoint check, $n=0$ gives the deterministic height-one law for
the one-edge tree; $n=1$ and $h=0$ give height-one probability $1/2$ for the
two-edge tree. These are sanity checks of the formulas, not additional Lean
executions or numerical certificates.

For the counting APIs, `centralSplits n` deliberately uses $n$ as the total
edge count rather than the recurrence's predecessor index. Its range is
$k<n$, with vertex counts $k+1$ and $n-k$. Both quarter conditions are exactly
equivalent to

$$
k\in[\lfloor n/4\rfloor,\ n-\lfloor n/4\rfloor).
$$

The resulting cardinality $n-2\lfloor n/4\rfloor$ gives at least half of
the $n$ split indices. The empty case $n=0$ is retained correctly. The
larger-component inequality assumes $k<n$, as needed to recover the vertex
sum $n+1$ in the presence of natural subtraction. Its conclusion is the
required half-vertex bound; no independence or probabilistic estimate enters
these arithmetic lemmas.

The future amplifier must keep the two indexing conventions explicit when
using these APIs: a recurrence applied at argument $n$ corresponds to
`centralSplits (n+1)`. No additional seed or height estimate has been assumed,
and no M2/E1/E2 coverage advances on the basis of B2a. No actionable
mathematical finding was identified in the reviewed code. Compilation,
axiom-closure and integration evidence remain separate coordinator checks.

### B2a boundary and non-strict-threshold addendum

The subsequent additions to `RRTSplitCDF.lean` also receive **PASS** for
statement fidelity and mathematical proof route:
`RRTSplit.heightLaw_real_le_succ`, `RRTSplit.heightLaw_cdf_initial`, and
`RRTSplit.heightLaw_cdf_zero`.

The non-strict real recurrence preserves the same total-size and child-edge
indexing, with thresholds $t$ and $t-1$ and no restriction on the real $t$.
It does not round a threshold or conflate strict and non-strict events. The
initial boundary is $F_0(h)=1$ for every natural $h$, including zero. The
other boundary is $F_{n+1}(0)=0$ for every natural $n$, so it excludes the
zero-edge tree correctly. The proof of that zero probability uses the actual
split representation, whose child side contributes at least one to total
height. These supply exactly the natural CDF boundary values needed in C2.

No mathematical finding arose. The reviewer again ran no Lean/Lake commands;
the coordinator's serial checks remain the source of mechanical evidence.

## B2b production review

31 October 2026, independent statement and proof-route review by the same
reviewer. **PASS for the B2b mathematical interfaces and proof route.** Files
read: `FreezingGrowth/SplitContraction.lean` and
`FreezingGrowth/RRTLowerTailAmplification.lean`, against the previously reviewed
B1/B2a interfaces and the discrete amplification argument above. No Lean/Lake
command was run by this reviewer. The coordinator is compiling serially and
will record mechanical validation separately.

The exact APIs reviewed are `RRTSplit.split_average_contraction` and the
following declarations in namespace `FreezingGrowth.RRT`:

- `lowerTail`, `SeedAt`, `ConstantSuccessSeed`;
- `lowerTail_nonneg`, `lowerTail_le_one`, `lowerTail_mono`;
- `lowerTail_geometric_of_seed`.

`lowerTail` uses the actual natural-height law with the strict real event
$H_n<t$. `SeedAt` and `ConstantSuccessSeed` are explicitly proposition
definitions. No instance or theorem asserts their truth. The geometric-tail
theorem requires the seed as a visible premise, together with $c\geq0$,
$A\geq0$ and $0<p\leq1$, and is not an unconditional paper result.

The generic averaging lemma assumes a nonnegative uniform bound $a$ and
$p\geq0$. It subtracts $ap$ on the central indices, whose number is at least
half of the positive total $N$. The sign $ap\geq0$ gives the required
direction. It does not incorrectly replace the central proportion by exactly
one half. No nonnegativity of the individual summands or upper bound on $p$
is required for this algebraic lemma; the amplification supplies stronger
probability conditions where needed.

The main proof inducts on the grid depth $j$, generalizing over every tree
size. For a total of $n+1$ edges it applies the strict-threshold recurrence
to component sizes $k,n-k$, and counts `centralSplits (n+1)`. The child vertex
count $n+1-k$ is identified with $n-k+1$ under $k<n+1$. Thus both quarter
conditions refer to the correct total vertex count $n+2$.

The local component estimate uses the previously proved center-loss bound
and the inductive hypothesis at the component's own size. Its additional
seed bound follows because $jL\geq0$. The child event initially has threshold
$t-1$; the proof replaces it by the larger event with threshold $t$ before
using these estimates. This is the correct favorable weakening. For a central
split it bounds the root factor by $a_j$ and the child factor by $1-p$.
Elsewhere it bounds the larger component by $a_j$ and the other probability
by one. Conditional independence is inherited from the genuine E3 CDF
recurrence, not imposed on unconditional marginals.

The zero-size successor step has an empty event because $b_c(0)=0$,
$A\geq0$ and $L\geq0$. The case $p=1$ gives $a_j=0$ and remains valid;
the proof only uses nonnegative factors, with $1-p/2\geq0$. There is no
unmentioned lower bound on component size, positivity condition on a real
threshold, or asymptotic estimate in the argument.

No actionable mathematical finding was identified. The result verifies the
conditional amplification step only. The actual seed, a uniform deficit
bound and the unconditional M2 exports remain unproved at this milestone;
the paper inventory counts therefore do not advance.

## C2 proposed geometric interfaces: early checkpoint

Independent mathematical interface review, before substantial dependent work.
The reviewer received the proposed definitions from worker `rrt_sharp_sources`
and checked their meaning against the pinned Mathlib geometric distribution.
**PASS for the proposed interfaces described here.** This does not yet review
future code or its elaboration; changes to these semantics require a recheck.

Time is $t\in\mathbb R_{\geq0}$, the success parameter is $p_t=e^{-t}$ as an
element of `unitInterval`, and the index law is `geometricMeasure p_t` on the
number of edges. The proposed height law binds that index to
`Forward.heightLaw RRT.allAttach n`. Its event probabilities are therefore

$$
\sum_{n\geq0}(1-e^{-t})^n e^{-t}\,
\mu_n(E).
$$

The proposed initial law is the height-zero Dirac measure, the index mean is
$e^t-1$, and its exact upper tail at natural $n$ is
$(1-e^{-t})^{n+1}$. The transfer inequality

$$
\mathbb P_{\mathrm{mixture}}(H\geq d)
\leq \mu_n\{H\geq d\}+\mathbb P(N_t>n)
$$

follows from actual RRT height monotonicity for indices at most $n$, and the
probability bound one for the remaining indices. It does not assume size and
height independent and does not assume a PWIT representation.

Mathlib's geometric parameter is the success probability, with support starting
at zero. Its value at parameter zero is totalized separately, so production
proofs must explicitly use $p_t>0$ when invoking the ordinary geometric
formulas. At $t=0$, $p_t=1$, which correctly gives the zero index, zero height,
and zero upper tail. The mean statement should be accompanied by integrability
of the actual index observable, rather than relying solely on an identity of
totalized integral and totalized sum. No new probability estimate or paper
coverage is certified by this early checkpoint, and no Lean/Lake was run.

## C1 clock construction and first-birth checkpoint

Independent source-code review of the proposed `FreezingGrowth/PWIT/Basic.lean`
and mathematical review of the first-birth interfaces supplied by worker
`rrt_lower_route`. **PASS for the reviewed definitions, Basic statements and
proposed first-birth semantics.** Compilation is pending with the coordinator;
this reviewer ran no Lean/Lake commands. The future first-birth implementation
will still need to be checked against these interfaces.

`PWIT.Vertex` is `List ℕ`, a path address read from the root, and child index
$i$ means mathematical rank $i+1$. `clockLaw` is `expMeasure 1`;
`law` is its actual independent product over `Vertex × ℕ`.
`childDelay` sums exactly the first $i+1$ waiting times at the parent.
`childSample` prefixes the child index to the address, so nested evaluation
preserves the intended ancestral order. `birth` adds the successive finite
ancestral delays, with root birth time zero.

`reaches d t` asserts existence of a path of length $d$ with birth time at
most $t$. Its countable existential makes it measurable without assuming a
minimum over the generation is attained. The reviewed statements give actual
coordinate marginals and independence, positivity of all clocks almost
surely, positivity of all non-root births almost surely, monotonicity in time,
and the correct zero-generation event. Simultaneous positivity is justified
by the countability of the clock coordinates.

The proposed first-birth decomposition extracts the coordinate at `([],0)`.
The residual-root reindexing sends `([],j)` to `([],j+1)` and `(i::v,j)` to
`((i+1)::v,j)`. The first-child reindexing sends `(v,j)` to `(0::v,j)`.
Their images, together with the extracted coordinate, are disjoint and cover
the original coordinate set. Thus the target joint law
`clockLaw.prod (law.prod law)` has the correct semantics. The proposed birth
identities for paths starting with zero or with $i+1$ are exact algebraic
identities, with one copy of the first waiting time added in each case.

One domain point was emphasized to the worker: `Sample` also contains clock
functions with negative entries. Consequently the event `reaches d 0` for
$d>0$ is null under the law, but is not literally the empty subset of all
samples. Arguments excluding births before the first clock must use the
proved almost-sure positivity event. No global population finiteness,
chronological labeling, minimum attainment or RRT representation has been
assumed or certified by this checkpoint.

### C2 geometric mixture: source-code checkpoint

The reviewer subsequently read `FreezingGrowth/RRTGeometricMixture.lean`.
**PASS for its mathematical statements, definitions and proof route.** The
reviewed source had not yet completed compilation; no Lean/Lake was run by
the reviewer. The exact namespace is `FreezingGrowth.RRT`, and the reviewed
public APIs are:

- `geometricParameter`, `geometricParameter_coe`,
  `geometricParameter_ne_zero`;
- `geometricIndexLaw`, `geometricHeightLaw`, and their probability instances;
- `geometricIndexLaw_singleton`, `geometricIndexLaw_zero`,
  `geometricHeightLaw_zero`;
- `geometricHeightLaw_real_eq_integral`, `geometricHeightLaw_real_series`,
  `geometricHeightLaw_event_integrable`, `geometricHeightLaw_event_summable`;
- `geometricIndexLaw_tail`, `geometricIndexLaw_integrable`,
  `geometricIndexLaw_mean`;
- `geometricHeightLaw_tail_le`.

These implement the previously accepted success-parameter convention and
actual-law mixture. Parameter nonvanishing is derived from exponential
positivity. Event summability and index integrability accompany the integral
and series identities, so the use of Mathlib's totalized formulas does not
conceal a convergence obligation. The exact strict tail $N_t>n$ has exponent
$n+1$, including time zero. The mean counts edges and therefore subtracts one
from $e^t$.

The transfer proof compares each index at most $n$ by the existing genuine
RRT height monotonicity and bounds later indices by one. Integration gives
exactly the advertised additive index-tail loss, without asserting any
independence between height and index. The natural threshold $d=0$ is also
admitted correctly. No seed estimate, renewal identity or identification with
the PWIT event is assumed or proved by these interfaces. No actionable
mathematical finding was identified; mechanical validation remains separate.

## B3 production statement and proof-route checkpoint

Independent review of `FreezingGrowth/DeficitGrid.lean`,
`FreezingGrowth/RRTLowerDeficit.lean` and
`FreezingGrowth/HighPopulationAssembly.lean`. **PASS for the mathematical
interfaces and proof route present in these files.** The coordinator is
performing compilation; this reviewer ran no Lean/Lake. This checkpoint
does not certify successful compilation of the reviewed drafts.

The reviewed APIs include `positivePart_le_grid`, `geom_sum_le_inv_one_sub`,
`RRT.UniformLowerDeficit`, `RRT.lowerDeficit_le_of_seed`,
`RRT.uniformLowerDeficit_of_seed`, `RRT.lowerCenter_sub_deficit_le_mean`,
`RRT.gap_mul_lowerTail_le_deficit`, `Word.HeightLE.real_tail`,
`Word.high_population_at_cutoff`, the two
`highPopulation_uniform_*_of_deficit` statements, and
`uniformHeightClaims_of_deficit` / `uniformHeightClaims_of_seed`.

The finite grid lemma includes its grid endpoints correctly with strict
inequalities in the indicators. Its zero-length and zero-spacing cases are
valid under the stated upper-bound premise. In the deficit proof the spacing
is strictly positive, and a finite grid above $b_c(n)$ also lies above
$b_c(n)-h-A$, because $h,A\geq0$. The pointwise bound then adds $A$ outside
the positive part. This remains valid for negative centers and for a grid of
length zero. The integrated geometric estimate multiplies by nonnegative
$L(1-p)$ and uses $0\leq\rho<1$, yielding exactly the reviewed uniform
constant. No infinite integration/summation interchange is hidden here.

The mean inequality integrates an actual pointwise inequality using the
proved height and deficit integrability. The lower-tail inequality integrates
a constant indicator on the strict event $H_n<t$, with a positive gap
$b_c(n)-t$ available to its client. It therefore controls the complement of
the paper's non-strict success event without an endpoint mismatch.

The real-threshold domination uses the natural ceiling correctly for every
real threshold. The cutoff bridge identifies integer subtraction followed
by `toNat` with natural subtraction under the explicit positivity premise,
retaining the corrected index $r_n-1$. Both high-branch conclusions choose
their validity index before the word. The probability proof chooses gap at
least $C/\varepsilon+1$, hence strictly positive, and obtains failure at most
$\varepsilon$ from the deficit bound. The final case split uses the existing
low-branch results, including their treatment of terminal extinction.

The resulting conjunction has precisely the existing
`UniformHeightProbabilityClaim` and `UniformHeightExpectationClaim` types.
The seed is still a visible premise of `uniformHeightClaims_of_seed`; no
numbered paper theorem is made conditional and counted as complete.

Scope note communicated to the coordinator: the roadmap's B3a also includes
absorption of an eventual seed's finite prefix. That helper was not present
in this reviewed snapshot. It must still be supplied before declaring all of
B3a complete, or explicitly retained for C4. This is a remaining task, not a
mathematical defect in the reviewed theorems. No other actionable finding
was identified, and no paper inventory count advances at this checkpoint.

### C1 first-birth source-code checkpoint

The reviewer subsequently read `FreezingGrowth/PWIT/FirstBirth.lean`.
**PASS for the exact definitions, statements and mathematical proof route.**
Reviewed APIs include `firstClock`, `leftIndex`, `rightIndex`, `leftSample`,
`rightSample`, their measurability and injectivity/disjointness statements,
`map_firstClock`, `map_leftSample`, `map_rightSample`, `indepFun_reindex`,
`indep_left_right`, `indep_firstClock_pair`, `firstBirth_joint_law`,
`childDelay_left`, `childSample_left`, `birth_firstChild`,
`birth_laterChild`, and `reaches_succ_firstBirth`.

The actual index maps have exactly the accepted meanings. Injective
reindexing gives each full remaining sample the original product law, while
disjoint coordinate families give their joint independence. The generic
`indepFun_reindex` requires disjoint ranges, as appropriate; it does not
unnecessarily require injectivity within each block. The first-clock
independence concerns the pair of complete remaining samples, not merely
pairwise independence of three random objects. Consequently the claimed
joint measure is exactly `clockLaw.prod (law.prod law)`.

The delay and birth identities retain the correct single first-clock
contribution. The event identity partitions nonempty paths by whether their
first address is zero or positive, preserving lengths $d$ and $d+1$ on the
two branches. It is valid for every sample, including samples with negative
clock coordinates: the residual events themselves retain those possibilities.
No condition that the first clock is at most $t$ is inserted into this
deterministic identity. Subsequent renewal proofs must still use almost-sure
positivity when eliminating negative residual-time events.

No actionable mathematical finding was identified. This checkpoint does not
certify the future renewal integral or height-law identification. No Lean/Lake
command was run by the reviewer; compilation evidence remains separate.

### B3 finite-prefix addendum

The subsequent `RRT.constantSuccessSeed_of_eventual` addition receives
**PASS**. It assumes $c\geq0$, $0<p\leq1$ and the displayed seed from a
fixed natural index $N$ onward. The original offset $A$ need not be
nonnegative. The replacement

$$
A'=\max\bigl(A,\ e\log(N+1)\bigr)
$$

is nonnegative and at least $A$. For $n<N$, the nonnegative logarithmic
correction and logarithm monotonicity give $b_c(n)\leq e\log(N+1)$, making
the strict lower-tail event empty. For $n\geq N$, threshold monotonicity
preserves the given bound. The same positive success probability $p$ is
retained for every size, including $N=0$.

This addition discharges the finite-prefix scope item noted in the B3
checkpoint. It does not assume or compute finite-size RRT probabilities,
and it does not supply the still-missing eventual seed. No Lean/Lake was
run by the reviewer.

## C3a finite path clocks: early source-code checkpoint

Independent review of `FreezingGrowth/PWIT/PathClocks.lean`, supplied by worker
`rrt_lower_route` before dependent work. **PASS for the mathematical
definitions, statements and proof route present in this preliminary module.**
Compilation remains the coordinator's task; the reviewer ran no Lean/Lake.

Reviewed APIs: `rankSum`, its zero/cons and length-plus-sum identities;
`pathCoordinates`, `pathCoordinates_length`, `pathCoordinates_nodup`;
`birth_eq_sum_pathCoordinates`, `map_pathClocks`, `map_birth_finite_sum`;
`rankClass`, `mem_rankClass`, `mem_rankClass_iff_rankSum`, and
`rankClass_disjoint`.

The flattened clock list uses $i+1$ root waiting times when the first child
address is $i$, and prefixes that address to the coordinates of the remaining
path. Root and descendant coordinate blocks are disjoint, and induction
preserves distinctness within the descendant block. Thus the number of
independent exponential waits is exactly the sum of the positive child ranks.
The claimed finite-product marginal is derived from the actual independent
clock family, and the birth law is the pushforward of that finite product
by its sum. No Gamma convolution theorem has been assumed.

`rankClass d k` is the image of the finite natural antidiagonal tuples under
`List.ofFn`. Its exact meaning is depth $d$ and zero-based address sum $k$,
equivalently positive rank sum $d+k$. The root case $d=k=0$ and empty classes
at $d=0,k>0$ are retained. Different $k$ give disjoint classes. No cardinality
of an infinite generation is substituted for this finite object.

This checkpoint does not approve future AF13 window/barrier definitions or
cyclic-leading assertions. Those require the announced source comparison.
In a future Gamma-law identification, zero rank must remain the deterministic
zero sum rather than an invalid positive-shape specialization. No seed,
barrier estimate or source coverage is certified here.

### C2 generating-function renewal: proposed-interface checkpoint

Worker `rrt_sharp_sources` proposed a real-variable analytic extension
$g_h(t)=e^{-t}F_h(1-e^{-t})$, where $F_h$ is the generating series of the
actual RRT CDF coefficients. Its interpretation as a probability is restricted
to $t\geq0$, with the corresponding nonnegative-time mixture. **PASS for this
proposed interface and the following mathematical derivation.** Source-code
and elaboration review of the new declarations remain to be performed.

The successor-index derivative is

$$
g'_{h+1}(t)=-g_{h+1}(t)+g_{h+1}(t)g_h(t),\qquad t\geq0.
$$

It follows from the CDF generating recurrence and the chain rule. The initial
values are $g_h(0)=1$ and the base function is $g_0(t)=e^{-t}$. Multiplication
by $e^t$ and integration yield

$$
g_{h+1}(t)=e^{-t}+e^{-t}\int_0^t e^u g_{h+1}(u)g_h(u)\,du,
$$

which becomes the accepted convolution renewal equation by $u=t-s$. The
real-variable extension avoids a hidden truncated subtraction inside this
integral; every argument interpreted probabilistically lies in $[0,t]$.
At time zero, a two-sided `HasDerivAt` statement is legitimate if the
generating-series derivative is established on $|z|<1$, since $z=0$ is then
an interior point. A derivative known only from nonnegative series arguments
would not by itself establish that particular two-sided statement.

This checkpoint assumes no probabilistic interpretation for negative real
times and does not certify the missing PWIT equality. No Lean/Lake was run.

### C3 good-path definitions: source-fidelity checkpoint

**PASS** for `PWIT/GoodPaths.lean` definitions and finite-count infrastructure.
The reviewer independently read [AF13 v3](https://arxiv.org/pdf/1012.2544v3),
§2, §4 (PDF pages 8–10), §5's opening and §6's good-set definition (page 18).
`rankWindow`, `timeCenter`, `leading`, `badInterior`, `badRanks` and `goodEvent`
match those source definitions at positive depth with window membership.
The prefix-zero checks are redundant there. `goodEvent` outside that domain
is only a helper extension. `goodCount` sums actual indicators over the
finite window, and its measurability, integrability and cardinality bound
introduce no moment estimate. Future ballot and overlap claims remain
unreviewed. No Lean/Lake was run.

### C2 analytic renewal: source-code checkpoint

Independent review of `FreezingGrowth/RRTGeometricRenewal.lean`: **PASS for
its mathematical interfaces and proof route**. Reviewed public APIs include
`heightCdfCoefficient` and its bounds/boundaries, `heightCdfGenerating` and
its summability and derivative statements, the successor generating-function
ODE, `geometricHeightLaw_cdf_eq_generating`, `geometricCdf` and its actual-law
identification, initial/base values, successor derivative, continuity,
`geometricCdf_renewal_integratingFactor`, `geometricCdf_renewal`, and
`integral_geometric_kernel`.

The coefficients remain actual RRT CDF probabilities. Differentiation is
established on the open domain $|z|<1$, using a uniform summable derivative
majorant on a smaller open interval. This covers the two-sided derivative at
time zero. Absolute summability justifies the Cauchy product, and the
coefficient identity is precisely the previously reviewed natural CDF
recurrence. The chain rule, integrating factor and substitution have the
correct signs, height indices and exponential factors.

The real extension's probability identification is restricted to nonnegative
times. The scalar geometric-kernel integral is legitimately stated for all
real times because its interval integral is oriented and its antiderivative
is globally differentiable. No missing positivity premise is needed there.
No actionable mathematical finding was identified. The source was awaiting
the coordinator's serial compilation; this review supplies no Lean/Lake
execution or independent kernel evidence.

### C2 PWIT renewal: first integral checkpoint

Independent review of `FreezingGrowth/PWIT/HeightRenewal.lean`: **PASS for
the statements and proof route currently present**. The reviewed declarations
are `heightCDF`, its nonnegativity/upper bound, `heightCDF_antitone`,
`measurable_heightCDF`, `heightCDF_eq_one_of_nonpos`,
`measurableSet_shifted_reaches`, and `heightCDF_firstBirth_integral`.

`heightCDF h t` is the actual probability that no depth-$h+1$ path is born by
$t$, without introducing a maximum over an infinite population. Its
antitonicity in time and measurability follow from the event's time
monotonicity. At nonpositive times its value is one by almost-sure positivity
of every non-root birth, rather than an invalid literal empty-event claim
on arbitrary clock functions.

The first-birth integral uses root-remainder and child absence events at
depths $h+2$ and $h+1$. Their joint measurability in the clock/time shift is
proved by a countable union over finite paths. Transport through the complete
joint law and bounded-indicator Fubini then gives, for every real $t$,

$$
q_{h+1}(t)=\int q_{h+1}(t-s)q_h(t-s)\,d\operatorname{Exp}(1)(s).
$$

No independence of an index and its height, global population finiteness, or
chronological enumeration is assumed. The exponential-tail separation,
base-height formula and uniqueness bridge were not yet in this reviewed
snapshot and remain distinct tasks. No actionable mathematical finding was
identified. No Lean/Lake was run by the reviewer.

### C3a Gamma and finite first moments

Independent source-code review of `PWIT/Erlang.lean`, `PWIT/RankCounts.lean`,
`PWIT/FirstMoment.lean`, and `integrable_goodCount_sq`: **PASS**. The worker
reports clean builds; this reviewer did not run Lean/Lake.

`gammaMeasure_nat_succ_conv_exp` derives the rate-one convolution by the
explicit density integral, with shape increasing from $n+1$ to $n+2$.
`map_birth_gamma` uses actual independent path clocks and shape `rankSum v`,
requiring a nonempty path. The empty path is separately Dirac at zero.
Rank cardinalities and the finite indicator-sum expectation have the correct
positive-generation hypothesis. `rank_density_factor` uses generation
$d+1$, excess rank $k$, hence Gamma shape $d+k+1$. These match the finite
slice formulas of [AF13 v3, §§2–3](https://arxiv.org/pdf/1012.2544v3).
No Gamma or expectation identity is assumed as an extra estimate. Square
integrability of the good count follows from its finite cardinality bound.
No asymptotic first moment, barrier or second-moment bound is certified.

### C2 scalar uniqueness and finite-time equation

Independent review of `RenewalUniqueness.lean`, `PWIT/HeightBase.lean`,
`PWIT/ClockIntegral.lean` and `PWIT/HeightEquation.lean`: **PASS for the
mathematical statements and proof route**; no Lean/Lake was run.

`eq_zero_of_volterra_le` correctly iterates its integral inequality to the
bound $t^k/k!$ and uses convergence of those terms to zero. In
`scalar_renewal_unique`, values in $[0,1]$ give an absolute difference at most
one, and the kernel $e^{u-t}r(u)$ lies in $[0,1]$ on $0\leq u\leq t$.
Bounded measurability supplies compact-interval integrability. Pointwise
renewal equations then imply pointwise uniqueness without an assumed
continuity of the solutions or coefficient.

`reaches_one_ae` and `heightCDF_zero_height` identify the first-birth boundary
using almost-sure positivity. `integral_clockLaw` and
`setIntegral_clockLaw_Iic` retain the exponential density's nonnegative
support; their unrestricted integral identities are used on genuinely
integrable bounded functions in `heightCDF_renewal`. The tail above time $t$
has integrand one and probability $e^{-t}$. The remaining interval has the
correct convolution integrand, including the successor height offset.
`heightCDF_renewal_integratingFactor` is the same equation after a valid
interval substitution. No global finite-population or maximum assumption is
introduced.

### C4 deterministic seed-index checkpoint

Independent review of `RRTSeedIndex.lean`: **PASS** for `seedIndex`,
`lowerCenter_two_lower`, `tendsto_lowerCenter_two`, `tendsto_seedIndex`, and
`seedIndex_time_upper`. The reviewer ran no Lean/Lake.

The chosen index is $\lceil b_2(n)-1\rceil_+$. The lower bound by
$(e-2)\log(n+1)$ proves divergence. Under $b_2(n)\geq2$, the index is
positive and strictly below $b_2(n)$: subtracting one before taking the
ceiling absorbs the rounding loss. The time-center bound therefore has
constant $3/(2e)$, rather than the earlier roadmap's more conservative
constant. Its negative logarithmic correction accommodates any fixed later
time shift. This deterministic refinement preserves the target seed and
uses the already reviewed finite-prefix absorption. It supplies no actual
success estimate.

### C2 height-law identification: proposed checkpoint

The proposed `PWIT.heightCDF_eq_geometricCdf` for nonnegative times and
`reaches_probability_eq_geometric_tail` for positive natural depth receive
**PASS at the mathematical interface level**. The successor induction uses
the common predecessor only on $[0,t]$, where the induction hypothesis
applies; no negative-time identification is needed. The tail statement uses
complements of the natural events at depths $d-1$ and $d$. Source-code review
and mechanical validation remain pending for these new declarations.

### C2 height bridge: source-code checkpoint

The reviewer subsequently read `PWIT/HeightBridge.lean` and the accompanying
`RRT.geometricCdf_nonneg`, `geometricCdf_le_one`, and
`geometricHeightLaw_tail_eq_one_sub_cdf`. **PASS for mathematical meaning
and proof route.** The induction uses the geometric predecessor as the common
coefficient, replacing the PWIT predecessor only on the nonnegative
integration interval. The actual-law bridge supplies the required probability
bounds and the continuity theorem supplies restricted measurability. The
tail identity has the correct positive-depth successor/complement indexing.
No chronological tree, global finiteness or height maximum is assumed. No
Lean/Lake was run by the reviewer.

### C4 conditional transfer: proposed checkpoint

The proposed `PWIT.ClockLowerSeed` places fixed $p,K,d_0$ before every
generation, with $0<p\leq1$ and actual path success at
`timeCenter d + K` for all $d\geq d_0`. The proposed theorem
`RRT.constantSuccessSeed_of_clockLowerSeed` receives **PASS at the semantic
interface level**, with that still-unproved seed as an explicit premise.

Taking $t_n=\log(n+1)+\log(p/2)$ gives a nonnegative time eventually. The
index mean and Markov bound give loss at most $p/2$, while the diverging
negative time-center margin absorbs $K$. The actual height bridge and size
transfer therefore give RRT success at least $p/2$ at the natural ceiling
of $b_2(n)-1$. The complement and the already reviewed finite-prefix lemma
produce the exact proposed seed on all sizes. No new estimate is certified
by this early checkpoint; actual code and mechanical checks remain pending.

### C3b proposed increment and cycle interfaces

**PASS at the proposed-interface level** for actual path increments
`childDelay ω (v.take i) (v.get i)` with `i : Fin v.length`, their product
Gamma law with shapes `v.get i + 1`, and the prefix-sum identity for
$j\leq|v|$. Parent prefixes at distinct depths have distinct lengths, giving
the injective clock-row reindexing required for independence. The empty
path remains an empty product and zero sum.

The proposed subsequent weighted-cycle route is mathematically sound provided
rotations preserve the **joint endpoint and increment law**, not merely the
centered-bridge marginal. Centered prefixes rotate with subtraction of the
new root value. A generic helper may assume these properties explicitly,
but the actual rank-class mixture must later discharge them and the
almost-sure absence of tied centered prefixes. The final identity must sum
over the finite rank class; no fixed-path leading probability is certified.
These precision conditions were communicated before dependent work. No
source code, ballot estimate or cyclic probability theorem is certified by
this proposed-interface checkpoint, and no Lean/Lake was run.

### C4 conditional transfer: source-code checkpoint

Independent review of `RRTLowerSeed.lean`, the added
`RRT.tendsto_seedIndex_time_gap`, and `RRT.geometricIndexLaw_tail_le_mean`:
**PASS for mathematical statements and proof route**. The source preserves
the accepted quantifier order in `PWIT.ClockLowerSeed` and keeps it as the
explicit premise of `constantSuccessSeed_of_clockLowerSeed`.

The eventual conditions ensure depth at least `max d₀ 1`, a genuine
nonnegative time, and the required path-time comparison. The exact law bridge,
index Markov bound at threshold $n+1$, and size-monotonic transfer yield
success at least $p/2$. The natural ceiling converts precisely to the
complement of the strict failure event at $b_2(n)-1$. Finite-prefix absorption
then supplies the all-size RRT seed. The negative time-gap limit is a direct
consequence of the reviewed deterministic upper bound, with its positive
logarithmic coefficient retained. No actual clock success estimate is proved
by this conditional transfer. No actionable finding was identified; the
reviewer ran no Lean/Lake and does not certify compilation here.

## C3c exact barrier inputs and bridge prerequisites

Independent mathematical source audit requested before the barrier campaign.
The reviewer reread [AF13 v3, Lemmas 4.4–4.6](https://arxiv.org/pdf/1012.2544v3).
For positive natural generation $n$, the exact uniform bounds are:

| Input | Domains | Bound |
| --- | --- | --- |
| Both leading and trailing events | $k\leq n$, $S>0$, $a\geq0$ | $C_4((an/S)^6+1)/n$ |
| Leading and bad interior | $2k\leq n$, $n/10\leq S\leq n$, $a\geq1$ | $C_5/(na^7)$ |
| Leading and bad ranks | $2k\leq n$, $n/10\leq S\leq n$, $a\geq0$ | $C_6 e^{-a}/n$ |

Each constant is absolute and chosen before all displayed parameters. These
are probabilities at a fixed endpoint $S$ under the explicitly constructed
bridge law, not quotients conditioning on a zero-mass singleton. The existing
strict/non-strict barrier definitions have the correct orientations.

### Minimal actual-law interface

Let $M_{n,k}$ be the current unnormalized `rankIncrementMeasure`, let
$s(x)=\sum_i x_i$, and let $p(x)=x/s(x)$. A sufficient interface is an actual
joint pushforward identity for endpoint and normalized increments. Positivity
of $s$ must hold almost surely for $n>0$, so the totalized division at zero
has no semantic effect. Define the reference `simplexLaw n` as the normalized
increment law of $n$ independent rate-one exponential variables; no new
unspecified probability measure is needed.

An additional derivation by this reviewer gives a useful simplification,
not yet a Lean proof. Finite multinomial expansion yields

$$
M_{n,k}=\pi_n\ \text{with density}\ \frac{s(x)^k}{k!},
$$

where $\pi_n$ is the product of $n$ rate-one exponential laws. Consequently,
once independence of $s$ and $p$ under $\pi_n$ is proved, the desired joint law is

$$
(p,s)_*M_{n,k}
=\binom{n+k-1}{k}
\bigl(\operatorname{simplexLaw}(n)\otimes\operatorname{Gamma}(n+k,1)\bigr).
$$

Thus the normalized bridge marginal is independent of the excess rank $k$.
The leading/trailing and bad-interior estimates may be reduced to the
reference bridge. This conclusion applies after summing the whole rank
class, not to a fixed rank word with unequal Gamma shapes. The proposed
positive-orthant radial-factorization route receives a mathematical **PASS**
with $n>0$ and actual-law characterization still to prove. For a general
radial tilt, either keep an unnormalized measure identity or require finite
positive total mass before normalizing. Any Haar polar normalization constant
must be retained until it cancels or is identified.

### Data which the present increment marginal does not retain

The bad-rank event needs the rank tuple. `rankIncrementMeasure` has forgotten
that tag. Preserve the finite tagged mixture of a rank tuple and its product
Gamma increment law, or retain the finite per-rank integrals explicitly.
Endpoint independence must then concern this full tagged normalized law.
A further useful characterization is that, given normalized increments $p$,
the excess-rank tuple has weights

$$
\frac{k!}{\prod_i r_i!}\prod_i p_i^{r_i},\qquad \sum_i r_i=k.
$$

This is an inferred finite multinomial kernel, not an assumed conditional
distribution. Its normalization and connection to the tagged actual law must
be proved. A bridge-marginal theorem alone cannot justify a bad-rank bound.

Disjoint clock blocks are independent before normalization. They are not
independent after fixing the total endpoint. The minimal bridge-splitting
API must retain a prefix fraction with its Beta law and, conditional on that
fraction, the two independently rescaled bridge blocks. For the reference
bridge split at $1\leq j<n$, the fraction has parameters $(j,n-j)$.
Using unconditional row independence in place of this disintegration would
leave a mathematical gap.

### Safe weighted formulations

For a bounded nonnegative measurable endpoint weight $w$ supported in
$[n/10,n]$, write $W=\int w(s)\,dM_{n,k}$. The required integrated bad-event
bounds are $C_5 W/(na^7)$ and $C_6e^{-a}W/n$, with the same parameter domains
as above. They are valid equally for normalized or unnormalized mixtures.
The leading-zero identity gives $W/n$. These formulations avoid singleton
conditioning while retaining precisely what the good-count argument needs.

Do not state the unrestricted leading bound as a real integral involving
$s^{-6}$ without an integrability hypothesis. That moment can diverge near
zero, and a totalized Bochner integral would no longer express the intended
upper bound. Use the pointwise bridge estimate at $S>0$, nonnegative extended
integrals, or endpoint weights supported away from zero.

For application to the good count, still prove that its entire rank window
eventually satisfies $2k\leq n$, and that its endpoint window lies inside
$[n/10,n]$. Fix the barrier parameter before the generation. Choosing it large
enough to make $C_5/a^7+C_6e^{-a}<1$ leaves positive leading mass; a separate
uniform first-moment lower bound is still required. These are concrete
dependencies, not supplied estimates. No barrier theorem or success seed
receives a proof-completion verdict here, and no Lean/Lake was run.

### C3c source-domain repair identified

The application of Lemma 4.4 inside the proof of Lemma 4.5, around equation
(4.10), requires an additional justification: its first block has generation
$m$ and excess rank $l$, whereas the stated Lemma 4.4 assumes excess rank at
most the generation. The global hypothesis $2k\leq n$ does not imply $l\leq m$.
See [AF13 v3, proof of Lemma 4.5](https://arxiv.org/pdf/1012.2544v3).
The independently derived rank-independent normalized bridge law above repairs
this call by extending the reference-bridge bound to every excess rank before
using it on a block. This is a proof-correspondence finding, not a change to
the requested source statement. Also make the real-parameter padding length
integral explicitly; an integer ceiling or monotonic extension from integer
barrier parameters suffices with controlled absolute constants.

## C3a actual whole-generation count checkpoint

Independent reviewer: `m2_inputs_review`. Reviewed the expanded
`PWIT/GenerationFirstMoment.lean` and new `PWIT/GenerationCount.lean` from disk.
Verdict: mathematical statements and proof route **PASS**. No Lean/Lake was
run by this reviewer; compilation and axiom evidence remain the coordinator's
separate responsibility.

`hasSum_integral_rankBirthCount` identifies the actual sum of finite rank-slice
expectations with $t^{d+1}/(d+1)!$ for $t\geq0$. The density identity uses
generation $d+1$, excess rank $k$, and Gamma shape $d+k+1$. Its dominated
convergence proof bounds the exponential-series partial sums by the integrable
polynomial $x^d/d!$ on $[0,t]$; it assumes no branching-process counting formula.

`generationCount` is the extended nonnegative sum of the actual finite
indicator counts. Every path of depth $d$ belongs to exactly the rank slice
indexed by its zero-address sum, and every finite count is nonnegative.
Consequently `ENNReal.ofReal` discards no mass. The exports
`one_le_generationCount_of_reaches` and `reaches_iff_generationCount_pos` hold
for every sample, including samples outside the almost-sure positive-clock
set. Tonelli and the proved `HasSum` then give `lintegral_generationCount`,
`ae_generationCount_finite`, and `reaches_probability_le_firstMoment` with the
correct positive-generation indexing. This establishes finiteness at each
fixed generation and time. It does not assert a global height maximum or a
positive lower seed.

## C3b actual cyclic leading interface checkpoint

Reviewed the actual implementations of `PWIT/Increments.lean`,
`CyclicMinimum.lean`, `SampledPath.lean`, `CenteredPath.lean`,
`PathNoTies.lean`, and `Leading.lean`. Mathematical/statement verdict: **PASS**
for these exact interfaces; proof compilation is separate and no Lean/Lake
was run by this reviewer.

The increment law is the product of independent Gamma laws with shapes
$r_i+1$, obtained from distinct actual clock rows. The rank increment measure
is the unnormalized finite sum over all excess-rank tuples, and its full
coordinate-permutation invariance is proved by reindexing that sum. No
exchangeability of a single unequal-rank word is asserted.

The centered bridge uses the $d$ prefix positions $0,\ldots,d-1$. Its periodic
extension gives the required centered rotation covariance. These positions
avoid counting the endpoint twice. `leading_zero_iff_minimumAt` restores the
endpoint condition using its exact zero centered value, and therefore matches
the existing `leading 0` predicate for every actual sample. Positive depth is
explicit through `NeZero d` or `NeZero v.length`.

The actual rank mixture is absolutely continuous with respect to finite
product volume. Distinct prefix functionals have proper linear tie kernels;
the explicit one-coordinate spike witnesses their inequality. Thus their
finite union is null, including the vacuous one-dimensional case. The generic
cyclic lemma assumes full measure-preserving rotations and an invariant
integrable weight; `integral_rank_leading` discharges those conditions for the
actual mixture and any integrable endpoint weight. Its division-free factor
is exactly $d$. The final finite sum over actual path integrals was not yet
present in the version of `Leading.lean` read for this checkpoint.

## C3c actual exponential simplex bridge checkpoint

Reviewed `PWIT/SimplexDensity.lean`, `SimplexPolar.lean`, and
`SimplexBridge.lean` from disk. Mathematical/statement verdict: **PASS** for
their positive-dimensional actual-law interfaces. No Lean/Lake was run by
this reviewer; these files were awaiting compilation at review time.

`normalizedSpacings_joint_law m` identifies the joint law of normalized iid
exponential spacings and their sum with `simplexLaw m` times
$\operatorname{Gamma}(m,1)$ for $m>0$. The normalization at a zero total has no
effect because every actual coordinate, and hence the total, is almost surely
positive. The simplex support has nonnegative coordinates summing to one.

The generalized polar identity retains the Haar angular and radial measures
and removes only the Haar-null origin in a nontrivial finite-dimensional
space. On the positive orthant the $\ell^1$ radius is the coordinate sum.
The actual exponential probability law fixes the product's total mass; the
proved product-of-marginals identity cancels the unknown normalization factors
without assuming a sphere or simplex volume. The endpoint marginal is supplied
by the already proved actual finite exponential-sum Gamma law.

This checkpoint does not yet certify a rank-mixture radial-tilt identity, a
tagged-rank disintegration, a Beta block split, or any barrier estimate. In
particular the independently derived extensions in the preceding C3c review
remain obligations until their actual-law bridges are proved. No paper
coverage count or main-result completion status changes here.

### C3c padding-factorization caution

Equation (4.4) in the [AF13 v3 padding argument](https://arxiv.org/pdf/1012.2544v3)
uses two padded-block event factors under a fixed full endpoint. Independence
of the unnormalized clock blocks does not justify independence under that
additional constraint. For implementation, retain the joint endpoint law and
prove a joint rectangle lower bound, or uniform iterated conditional bounds.
In the reference excess-rank-zero case this is a three-block simplex
disintegration with block parameters $(m,m,n)$. Their normalized internal
bridges can then be separated conditional on the block masses. This records
the precise location requiring the block-disintegration bridge already listed
above; no unsupported conditional-independence claim is accepted.

### Further interface checkpoints: radial tilt and moment assembly

The proposed `SimplexRadial` interface receives mathematical **PASS** for
$m>0$: the measure with density $B(\sum_i x_i)$ on the nonnegative orthant,
for measurable $B:\mathbb R\to[0,\infty]$, has normalized-vector/total
pushforward equal to `simplexLaw m` times its actual total marginal. No
finiteness or positive mass of this new density is required for this
unnormalized measure identity. The existing exponential probability case
fixes the angular factor; scalar cancellation uses its product mass equal to
one. The Haar-null origin remains null even for an infinite density there.
This is an interface checkpoint only; the new actual implementation was not
yet read.

The proposed conditional good-count assembly also receives mathematical
**PASS**. For $Z=\operatorname{goodCount}(d,a)$ and $C>0$, the explicit
per-vertex assumptions

$$
\mathbb E[1_{\operatorname{goodEvent}(v)}Z]
\leq C\mathbb P(\operatorname{goodEvent}(v))
$$

sum over the finite rank window to $\mathbb E Z^2\leq C\mathbb E Z$.
Integrating the nonnegative function
$Z^2-2CZ+C^2 1_{\{Z>0\}}$ gives
$\mathbb P(Z>0)\geq\mathbb E Z/C$. Thus an additional explicit lower moment
bound $0<c\leq\mathbb E Z$ yields $c/C$ as a lower success bound. A positive
good count supplies a path born by `timeCenter d` directly from the endpoint
condition. The per-vertex bound and first-moment lower bound remain unproved
hypotheses here; a uniform wrapper must choose their constants before the
generation. No success seed is supplied by this conditional assembly alone.

The actual `SimplexRadial.lean` implementation was subsequently read, together
with the new `normalizedSpacings_smul`,
`reconstruct_normalizedSpacings`, and
`finiteClockLaw_eq_scaled_simplex_gamma` in `SimplexBridge.lean`.
Mathematical/statement **PASS** now applies to those bodies as well. The radial
identity uses exactly the approved multiplicative normalization cancellation.
Scaling invariance allows any nonzero real scalar, while reconstruction uses
the necessary nonzero total and the law-level recovery discharges it almost
surely. Compilation was still pending and no Lean/Lake was run by the reviewer.

The proposed fixed-rank grouping interface also receives an early **PASS**:
for $N>0$ and a real linear map $G:\mathbb R^N\to\mathbb R^d$ preserving the
coordinate sum, the joint law of the normalized grouped vector and the
original total under `finiteClockLaw N` is
$(G_*\operatorname{simplexLaw}(N))\otimes\operatorname{Gamma}(N,1)$.
Normalization commutes pointwise with $G$, including at a totalized zero
denominator, so no positivity premise on $G$ is required for this algebraic
identity. The angular marginal is the displayed pushforward, generally not
`simplexLaw d` when block sizes differ. The intended fixed-rank application
must still supply the actual independent-clock grouping characterization.

The actual `PWIT/GoodCountMoment.lean` file was then read. Its finite-count
square identity, integrated per-vertex bound, polynomial second-moment
argument, and inclusion of success in `reaches d (timeCenter d)` receive
mathematical/statement **PASS**. Allowing arbitrary $c$ in the displayed
assumption $c\leq\mathbb E Z$ is valid; positivity is needed only in a later
positive-seed wrapper. The path depth is obtained from membership in the rank
window, and its time bound from the upper endpoint of `goodEvent`. A later
uniform wrapper can derive $c/C\leq1$ from the probability bound at one
admissible depth rather than assume it separately. No Lean/Lake was run by
the reviewer, and the two mathematical moment inputs remain explicit.

The concrete `SimplexGrouped` fixed-rank interface receives the same early
**PASS**: group $N=\sum_i(r_i+1)$ iid exponential coordinates into disjoint
blocks of sizes $r_i+1$. The actual grouped law is `incrementLaw r`, and for
$d>0$ its normalized-vector/total law is the pushforward of `simplexLaw N`
under the grouping map times $\operatorname{Gamma}(N,1)$. The chosen finite
coordinate equivalence only assigns independent clock coordinates to blocks;
it does not assert a coupling between different rank words. Positivity of the
dimension supplies $N>0$. Its implementation has not yet been read.

Source identity rechecked during this review: `main.tex` remains SHA256
`7b7d6ef6e2200b3129cbd4a74ef45c09fbf758643ce63489bf67f2aef93301f3`.
The original full source scope, including E1/E2, is unchanged.

## Handover checkpoint: proposed Poisson all-rank alternative

At the user's stop request, the coordinator's proposed alternative had been
mathematically assessed but not implemented or mechanically verified. For
the actual PWIT Poisson offspring, summing the joint arrival densities over
ordered distinct sibling ranks gives Lebesgue factorial intensity on the
positive quadrant. Splitting ordered path pairs by their last common ancestor
would therefore give an all-rank second-moment formula. This actual-law
factorial-intensity and pair-decomposition bridge still needs proof.

The proposed good paths retain the endpoint window, $L_a$, and the exclusion
of $B_a$, but omit the rank window and $D_a$. For a first good path, shared
prefix depth $j$, $q=d-j$, and $\delta=W_j-(j/d)m_d$, the other suffix has
total at most $y=q m_d/d-\delta$ and satisfies a near-leading condition with
parameter $A=a+\max(\delta,0)+1$. Integrating the required simplex bound
against $s^{q-1}/(q-1)!$ gives, for $q\geq12$ and $y\geq0$,

$$
Q_q(y,A)\leq\frac{C}{q}
\left(\frac{y^q}{q!}+A^6\frac{y^{q-6}}{(q-6)!}\right)
\leq C'(A^6+1)q^{-3/2}\exp(ey-q).
$$

If $y<0$, the positive-suffix event is empty and is handled separately.

The overlap factor $q^{-3/2}d^{3q/(2d)}$ is uniformly bounded: putting
$u=d/q\geq1$ gives
$(q/d)\log d-\log q=(u^{-1}-1)\log q+(\log u)/u\leq1$.
The interior exclusion $B_a^c$ supplies
$\delta>\min(j,q)^{1/40}-1$, yielding a summable overlap bound; finitely many
endpoint indices and small $q$ can be absorbed in a constant depending on the
fixed $a$. Thus no mathematical obstruction to this second-moment route was
identified. It still requires the near-leading and bad-interior estimates,
the actual pair law, all-rank count Tonelli, and current Lean evidence.

The first moment would use the all-rank endpoint intensity directly: its
window mass is of order $d$, exact cyclic leading divides by $d$, and the
bad-interior estimate removes at most a constant times $a^{-7}$ of that mass.
The rank-concentration and bad-rank estimates are unnecessary for this
alternative seed proof. They are not thereby proved, nor are the original
paper's E1/E2 obligations removed.

Crucially, the old fixed-labelled-vertex overlap hypothesis must not be reused
without justification. Conditioning on a fixed large child rank changes the
sibling law. The Poisson cancellation is valid after summing the two distinct
sibling ranks; use a global pair-intensity second-moment argument. This is a
substantive proposed proof departure, not a completed result.

The independently proposed `RankDensity` formula also passed its statement
checkpoint: the unnormalized rank mixture has orthant density
$e^{-s}s^k/k!$, including dimension zero with $0^0=1$. Its new code had not
yet been read. Likewise the newly written `SimplexLinear` and `SimplexGrouped`
bodies remain unread here; their previously recorded interface approvals
remain valid, with compilation evidence separate. No new review work or
Lean/Lake run was started after the stop request.

## Resumed actual-body review, 2026-11-01

Following the user's resumption, independent reviewer `m2_inputs_review` read
the previously pending implementations in `PWIT/SimplexLinear.lean`,
`SimplexGrouped.lean`, and `RankDensity.lean`. Mathematical statements and
proof correspondence receive **PASS**. This supersedes only their prior
unread-body status; the earlier interface reviews remain applicable. No
Lean/Lake was run by the reviewer, and coordinator compilation/axiom evidence
remains separate.

`normalizedSpacings_linear` proves the algebraic normalization identity
pointwise, including a zero total, from linearity and preservation of the
coordinate sum. Its joint-law export transports the established actual
simplex/Gamma product law. `groupRankWaits` assigns disjoint iid exponential
coordinates to blocks of sizes $r_i+1$ through a finite equivalence; their
total is exactly `rankWaitCount r`. The product regrouping and finite Gamma
sum laws identify this map with `incrementLaw r`. Positive edge dimension
ensures a positive Gamma shape. The resulting `rankSimplexLaw r` retains its
dependence on the fixed rank word, and the final `tupleIncrement` statement
uses the actual PWIT law already proved in `SampledPath`.

`rankIncrementMeasure_eq_withDensity` sums these actual product Gamma
densities. Its multinomial identity gives the orthant density
$e^{-s}s^k/k!$ without a class-cardinality divisor. Negative coordinates
contribute zero. The empty-dimensional cases are correct: $k=0$ gives mass
one on the empty vector, while $k>0$ gives the zero measure. This measure
forgets the rank tag, so the export does not assert a bad-rank estimate.
These are characterization bridges, not a success seed or a paper-coverage
advance; the full existing inventory, including E1/E2, remains in scope.

### Resumed shared-interface checkpoints

The proposed `SimplexMixture` exports receive **PASS** for $d>0$ and every
excess rank $k$: its actual normalized-vector/total joint law is
`simplexLaw d` times its actual endpoint marginal, the latter being the
rank-class cardinality times $\operatorname{Gamma}(d+k,1)$. Dividing by the
positive finite cardinality gives the corresponding probability product law.
No hypothesis $k\leq d$ is needed. Fixed positive endpoint statements should
use the canonical scaled-simplex bridge and actual weighted-law
reconstruction, not a supposed uniquely defined probability conditional on a
null singleton. The new implementation had not yet been read.

The proposed `OffspringIntensity` and `ManyToTwo` targets also receive early
mathematical **PASS**. Put $\Lambda=\operatorname{Lebesgue}|_{[0,\infty)}$ and
let $S_i$ be the actual arrival at child index $i$, with $i+1$ waits. Its
single-arrival intensity is $\sum_i\operatorname{Law}(S_i)=\Lambda$. The
joint law of $(S_i,S_{i+m+1})$ is obtained from independent Gamma variables
of shapes $i+1$ and $m+1$ by $(s,u)\mapsto(s,s+u)$. Summing over both ordered
distinct child labels gives $\Lambda\otimes\Lambda$; the diagonal and zero
boundaries are null. This remains a claim about the actual clocks to prove.

Writing $\Lambda_d=\Lambda^{\otimes d}$, the full ordered path-pair intensity
is proposed as its diagonal pushforward plus, for each $0\leq j<d$, the
pushforward of
$\Lambda_j\otimes\Lambda_{d-j}\otimes\Lambda_{d-j}$ that splices a shared
prefix into both suffixes. The coefficient of each term is one: the sibling
factorial intensity already includes both orientations. At depth zero only
the diagonal term remains. Exact joint clock-coordinate regrouping must
establish the independence of the common-prefix, branching, and disjoint
subtree coordinates; equality of their marginal intensities alone would not
suffice. These are reviewed proof targets, not supplied assumptions or
completed many-to-two evidence.

The coordinator's proposed analytic first-moment target receives **PASS**:
for each fixed real $s$,

$$
\frac{(m_n-s)^n}{n!\,n}
\longrightarrow\frac{\exp(-es)}{\sqrt{2\pi}}.
$$

Eventual positivity of $m_n-s$ and $n$ permits exponentiation of the log
limit. Subtracting the $s=1$ limit from $s=0$ gives
$(1-\exp(-e))/\sqrt{2\pi}>0$ for the endpoint-window intensity divided by
the positive generation. After the actual all-rank and cyclic bridges are
connected, this is the mean of exactly leading paths. It is not yet a
probability lower bound.

The actual `SimplexMixture.lean` bodies were subsequently read and receive
mathematical/statement **PASS**. The density and total-mass helpers retain
dimension zero; the Gamma endpoint and normalized probability exports require
positive dimension. The positive finite cardinality is proved before its
inverse is cancelled. Both actual marginals and the literal `IndepFun` result
have the advertised semantics. Compilation was pending at this checkpoint.

The current `TimeCenterEstimates.lean` implementation was also read. Its
uniform upper bound
$\sqrt n\,t^n/n!\leq\exp(et-n)$ for $n>0,t\geq0$, logarithmic Taylor
remainder, and critical log-intensity limit receive mathematical **PASS**.
The remainder uses the valid inequality $u-u^2\leq\log(1+u)$ for $u\geq0$;
eventual nonnegativity is derived for each fixed shift. The log-Stirling
normalization cancels exactly the $\tfrac32\log n$ term. The new
exponentiated/window-limit bodies were not yet present in the version read.

The proposed `GammaWindows` interfaces receive early **PASS**. For integer
$n\geq1$, $C\geq0$, $4C^2\leq n$, and $|x-n|\leq C\sqrt n$, they assert

$$
\frac{\exp(-1-2C^2)}{\sqrt n}
\leq f_{\operatorname{Gamma}(n+1,1)}(x).
$$

The hypotheses imply $x\geq n/2>0$. With $u=(x-n)/n\geq-1/2$, the bound
$\log(1+u)\geq u-2u^2$ and the upper Stirling factor $e\sqrt n$ give the
displayed constant. For fixed $A<B$ and $C=\max(|A|,|B|)$, integration over
$[n+A\sqrt n,n+B\sqrt n]$ gives the positive uniform mass lower bound
$(B-A)\exp(-1-2C^2)$. The proposed global density upper bound $1/\sqrt n$
is valid as well. The center here is the mode $n$, while the Gamma shape is
$n+1$; padding applications to shape $m$ must explicitly account for the
center $m-1$. These remain reviewed analytic targets until their actual
proof evidence is supplied. No Lean/Lake was run by this reviewer.

### Actual all-rank counts and overlap analytics

The current first half of `OffspringIntensity.lean` was read and receives
mathematical/statement **PASS**: the actual arrival-law sum, disjoint-block
Gamma laws, and increasing-arrival joint law have the reviewed indices and
supports. The blocks are independent; their cumulative arrival times are not
claimed independent. The ordered distinct-pair cancellation and full path-pair
decomposition were not yet present in the version read.

The actual `AllRankCount.lean` implementation receives **PASS**. Its extended
nonnegative count is a sum of finite disjoint rank slices, with exact event
existence for every sample and Tonelli without a preliminary integrability
assumption. Domination by the generation count gives finite expectation and
almost-sure finiteness at each positive generation before real integrals of
the `toReal` projection are used. `allRankGoodEvent` keeps precisely the
endpoint window, leading condition, and exclusion of bad interior, and is
explicitly distinct from the previous finite rank-window count. The one-way
all-sample inclusion from positive real count to `reaches` remains correct
even on exceptional infinite-count samples; no all-sample converse is claimed.

The actual `CriticalWindow.lean` limit and eventual positive lower bound also
receive **PASS**. Its exponential definition of the Stirling constant equals
the intended $1/\sqrt{2\pi}$ mathematically. When connecting the window
formula to actual path counts, require $m_d-1\geq0$, which holds eventually.
The formula is not the count intensity for every positive $d$ with a negative
lower endpoint (for example $d=1$); the present asymptotic exports do not make
that assertion.

The actual `OverlapEstimates.lean` bodies receive **PASS**. The factor bound
holds for real $1\leq q\leq d$, with all logarithm and rpow domains justified.
For fixed natural $k$ and positive real $c,\beta$, the summability proof bounds
$n^k\exp(-cn^\beta)$ eventually by $n^{-2}$ using
$\log n=o(n^\beta)$. The zero index is a harmless finite-prefix term. These
are analytic prerequisites only; no probabilistic overlap estimate is hidden
in them. Compilation and axiom evidence for all these modules remain
separate from this read-only mathematical review; no Lean/Lake was run.

The actual `GammaWindows.lean` bodies were then read and receive
mathematical/statement **PASS**. The lower-window proof derives the positive
domain and exact logarithmic error bound before invoking Stirling. The global
density upper bound applies the generation-intensity estimate at $x/e$ and
cancels the exponential factors correctly. Window probabilities are bounded
through nonnegative extended integrals and finite Gamma measure before taking
real values, with no unproved Bochner-integrability premise. The standardized
interval export permits $A=B$, yielding zero; strict positivity follows for
$A<B$. The mode/shape indexing remains unchanged. Compilation was pending
at this review checkpoint, and no Lean/Lake was run by the reviewer.

### Actual all-rank cyclic first intensity

Reviewed the new `AllRankLeading.lean` body and the completed finite-sum
`integral_leading_rankClass` body in `Leading.lean`. Mathematical statements
and proof correspondence receive **PASS**. The finite mixture's integrability
is inherited by its summands before actual `tupleIncrement` map laws transport
the integrals to PWIT paths. List reindexing preserves the entire rank class;
no single fixed-word cyclic probability is asserted.

For any measurable endpoint set $J$ and positive generation $d$, the exact
all-rank identity is kept in extended nonnegative integrals:

$$
d\,\mathbb E[\#\{v:|v|=d,\ S(v)\in J,\ L_0(v)\}]
=\mathbb E[\#\{v:|v|=d,\ S(v)\in J\}].
$$

Each finite-slice probability is finite before conversion from real values
back to measures. Tonelli then permits an infinite total endpoint mass. The
specialization to $J=(-\infty,t]$, $t\geq0$, cancels the positive finite
factor $d$ and gives $t^d/(d!d)$ using the actual generation expectation.
This verifies a first-intensity bridge, not a success lower bound. Build and
axiom evidence is supplied separately by the implementing workers and
coordinator; no Lean/Lake was run by this reviewer.

The subsequent `AllRankLeading` real-integral and endpoint-window extensions
were read, along with `pathEventCount_union`, and receive **PASS**. The
decomposition $(-\infty,t]=(-\infty,s]\sqcup(s,t]$ uses $s\leq t$; the
real count identity is obtained only on the proved almost-sure finite set.
The formula for the $(s,t]$ leading count explicitly requires $0\leq s$.
`eventually_exactLeadingWindowCount_mean_pos` establishes both $m_d\geq1$
and positive generation before using it. This resolves the earlier
lower-endpoint domain warning. Its strict lower endpoint is a subcount of the
closed window in `allRankGoodEvent`, sufficient for the intended lower bound
without an unproved atom-free endpoint identification. Neither interior
exclusion nor positive success probability is asserted.

The proposed deterministic `SimplexPadding` interface receives early
mathematical **PASS**. With $a\geq10$, $a^2\leq m\leq a^2+1$, $a^6\leq n$,
and the three windows

$$
Z_1\in[m+4a/3,m+5a/3],\quad
Z_2\in[m-8a/3,m-7a/3],\quad
Z_3\in[n-\sqrt n,n+\sqrt n],
$$

put $N=n+2m$ and $T=Z_1+Z_2+Z_3$. The claimed $T>0$ and normalized target
windows $NZ_1/T\in[m+a,m+2a]$,
$NZ_2/T\in[m-3a,m-2a]$ follow from
$|T-N|\leq2\sqrt n$, $0\leq Z_i\leq3a^2$ for $i=1,2$,
$T\geq n/2$, and $12a^2/\sqrt n\leq a/3$.
For natural Gamma shapes $m,m,n$, the approved density bounds with modes
$m-1,m-1,n-1$ and standardized constants $4,4,2$ give window masses at least
$e^{-33}/3,e^{-33}/3,2e^{-9}$. Their independent product lower bound is
$2e^{-75}/9$. These are proposed intermediate targets; their code had not
yet been read, and the near-leading estimate remains unproved at this
checkpoint.

### Stronger exactly-leading Poisson route: independent assessment

The coordinator proposed retaining only the endpoint window and $L_0$ in the
all-rank count. Independent mathematical assessment: **PASS as a proposed
route**, with the actual near-leading estimate and pair-moment proof still
outstanding. No completed seed follows from this assessment.

For common-prefix depth $j$, suffix length $q=n-j$, and
$\delta=s-(j/n)m_n$, two globally leading paths with endpoints in
$[m_n-1,m_n]$ imply $\delta\geq-j/n\geq-1$. Their common prefix and both
suffixes are each near-leading relative to their own endpoint with allowance
$A=\delta+1\geq0$. This follows by comparing the global and local chords;
it does not require an interior or rank barrier.

For a segment of length $l\geq12$, multiplying the required simplex
near-leading bound by its endpoint density and shifting the singular term
from power $l-1$ to $l-7$ gives a uniform upper bound

$$
C(1+A^6)l^{-3/2}\exp(es-l).
$$

The key factorial ratio is
$l^6(l-7)!/(l-1)!\leq64$, since its six denominator factors are at least
$l/2$. Both shifted lengths are positive and at least $l/3$. A suffix
endpoint window has length at most one, so integration preserves this bound
with its upper endpoint substituted into the exponential. No uniform
positive lower bound on the endpoint is required; the zero endpoint is null
and the polynomial form is harmless there.

For $j,q\geq12$, the resulting ordered-pair contribution is bounded by a
constant times

$$
\frac{n^{3-3j/(2n)}}{j^{3/2}q^3}
\int_{-1}^{\infty}(1+(\delta+1)^6)^3e^{-e\delta}\,d\delta.
$$

The integral is finite. For $j\leq n/2$ the prefactor is at most
$8j^{-3/2}$; for $j\geq n/2$ the reviewed overlap bound makes it at most
$2^{3/2}e^{3/2}q^{-3/2}$. Both sums are uniformly finite. At $j=0$ the
off-diagonal contribution is exactly the square of the first intensity.
For the finitely many positive $j<12$, a raw prefix polynomial is integrable
against the two suffix factors' $e^{-2e\delta}$ decay. For $q<12$, retain
nonnegative suffix totals, giving $-1\leq\delta\leq q m_n/n$; this is a
fixed bounded interval since $m_n/n$ is bounded. Raw suffix intensities and
the prefix overlap factor then suffice. Finitely many small generations can
be excluded by the eventual seed threshold.

The near-leading theorem must be uniform in all allowances $A\geq0$ and
segment lengths, since $A$ varies inside the integral. The argument still
requires the actual ordered-pair intensity and disintegration bridges; it
must not revert to a fixed-labelled-vertex conditional estimate. The
bad-interior and bad-rank estimates would be bypassed in this alternative
seed proof, not thereby verified. The main paper inventory and E1/E2 remain
unchanged.

The actual `AllRankMoment.lean` generic polynomial moment proof was read and
receives **PASS**. It explicitly assumes integrability of the count and its
square, a first-moment lower bound, and a global second-moment bound. Its
existing specialized wrapper still concerns `allRankGoodCount` with interior
exclusion; its generic lemma can later be applied to the exactly-leading
count once the new moment estimates are proved.

The proposed `BallotDensity` analytic helper receives early **PASS** with
$K=64\sqrt3\,e^7$, $n\geq12$, $A,s\geq0$. Its polynomial formulation is
valid at zero, and for $s>0$ it equals the near-leading prefactor times the
endpoint intensity. It introduces no probabilistic estimate as a hidden
premise.

### Actual ordered sibling intensity and subtree regrouping

Read the completed additions to `OffspringIntensity.lean` before compilation.
Mathematical statements and proof route receive **PASS**. The shear maps
positive-quadrant volume to the ascending birth triangle. Swapping gives the
descending triangle; the two triangles cover the quadrant and intersect
only on a volume-null diagonal. The child-pair equivalence enumerates each
ordered distinct pair once, producing the required factorial intensity with
coefficient one.

The new subtree joint laws retain the two cumulative arrivals' actual
correlation. The root row is independent of descendant coordinates, and two
different child prefixes give disjoint descendant samples with law `law`.
The final two-subtree factorization requires distinct child labels exactly
where necessary. Thus this source provides the actual joint foundation for
the proposed many-to-two argument; it does not yet provide that full
generation-level identity. No Lean/Lake was run by the reviewer.

### Shared vector barrier, padding bodies, and exact pair recursion

Read `VectorLeading.lean`. Mathematical/statement **PASS** covers the canonical
finite-vector barrier, its measurability and monotonicity, positive-scalar
equivalence with allowance $a/S$, and exact equivalence to `leading` on actual
tuple increments. Prefix indices include both zero and the endpoint. At
dimension zero the condition is exactly $0\leq a$, as documented. The
deterministic characterization assumes no positivity of the input vector.

Read `SimplexPadding.lean` through
`normalizedSpacings_three_block_joint_law`. Its deterministic normalization,
Gamma side/middle windows, and full interleaved product law receive **PASS**.
The middle helper correctly uses shape $n\geq17$, so its mode $n-1$ satisfies
the $C=2$ density lemma's required lower bound $16$. All three full internal
normalized paths and all three totals are retained, permitting product-event
assembly without assuming independence after conditioning on their sum.
The product-rectangle probability and final ballot estimate were not yet
present in the version read.

Read `ManyToTwo.lean` through `generationPairIntensity_succ`. Its actual
one-path intensity and exact ordered-pair recursion receive **PASS**. Summing
the finite rank densities gives `positiveOrthantVolume` with the correct
one-point zero-dimensional case. The same-child term prepends one shared
arrival to the joint descendant pair law. The distinct-child term uses the
proved correlated-arrivals/independent-subtrees joint law before summing
labels, and then the ordered sibling factorial intensity. `childHeadsEquiv`
partitions all ordered path pairs once. No coefficient two, rank normalization,
or independence of same-subtree descendants is introduced. The closed
common-ancestor expansion and its moment specialization remain to be proved.
These reviews inspect actual mathematical bodies; compilation and axiom
evidence remain separate, and the reviewer ran no Lean/Lake.

Read the actual bodies of `SimplexLeading.lean`, `LeadingSplit.lean`, and
`BallotDensity.lean`, together with the new vector-to-cyclic-minimum identity.
Mathematical statements and proof correspondence receive **PASS**.
`SimplexLeading` identifies the rank-zero mixture with the actual iid
exponential law, obtains its exact zero-leading probability $1/d$ from the
proved cyclic identity, and transports the event to `simplexLaw d` through
almost-sure positive normalization. Positive dimension is explicit.

`LeadingSplit` proves the chord comparisons pointwise. A whole zero-leading
path gives the same nonnegative splitting excess as an allowance for both
positive-length blocks. The endpoint-window version weakens that allowance
to $S-\frac{j}{j+q}m+1$ using only the lower endpoint bound $m-1\leq Z$;
it is therefore common to both paths sharing the prefix. No increment
positivity, clock independence, or missing upper endpoint assumption is
needed for these deterministic conclusions. Upper endpoint control is still
required separately in the subsequent suffix-intensity estimate.

`BallotDensity` proves the approved factorial shift and exponential bound
with $64\sqrt3e^7$. Its polynomial equality uses a positive endpoint, while
the upper bound itself includes zero safely. It remains purely analytic and
does not assert the probabilistic near-leading estimate. These files were
awaiting coordinator compilation at this checkpoint; no Lean/Lake was run
by the reviewer.

The new probability-rectangle bodies in `SimplexPadding.lean` and the
deterministic `SimplexConcatenation.lean` bodies receive mathematical **PASS**.
Both short blocks may use the forward zero-leading event. The middle
inequality uses nonnegative prefixes and $M\geq n$ directly. The last block
uses $(m-V)(1-P)\geq0$ for its unit-simplex prefix $P\leq1$, so the stronger
helper legitimately does not assume $V\geq0$. The actual independent-clock
concatenation law includes empty dimensions. An integration issue was reported
to both authors: `vectorPrefix_append_left/right` were declared in both
`LeadingSplit` and `SimplexConcatenation`; they must be consolidated before
the two modules are imported together. This is a declaration collision, not
a mathematical discrepancy.

The proposed `GenerationBridge` endpoint disintegration receives an early
**PASS** for $d>0$. The positive-orthant Lebesgue measure is the iid
exponential law tilted by $\exp(\sum_i x_i)$. Its normalized-vector/total
pushforward is `simplexLaw d` times the measure with density

$$
1_{\{s\geq0\}}\frac{s^{d-1}}{(d-1)!}.
$$

The exponential tilt cancels the Gamma endpoint's exponential factor.
The statement preserves the infinite endpoint mass; it must not normalize
that mass as a probability. Dimension zero is excluded because its endpoint
is the atom at zero. The $d=1$ case and density value at zero are consistent.
The actual implementation was not yet read at this checkpoint.

The duplicate prefix declarations were subsequently removed from
`SimplexConcatenation`, which now imports and reuses `LeadingSplit`; the
reported declaration collision is resolved in the source.

The proposed closed MRCA identity on `List ℝ × List ℝ` receives **PASS**.
Both actual increment vectors are pushed forward by `List.ofFn`, and shared
prefix increment lists are appended to each suffix. Fixed lengths preserve
the information needed by moment tests; $j<d$ gives total length $d$, and
depth zero still has only the diagonal term. This carrier change avoids
dependent finite-index transports without changing the mathematical law.

The proposed padding-probability assembly also receives **PASS**: reconstruct
the three iid clock blocks from the interleaved simplex/Gamma product law,
retain full-measure simplex supports in the angular events, and use the raw
Cartesian Gamma windows. The pointwise embedding and zero-leading
probability give

$$
\frac{c}{m^2}\mathbb P_{\operatorname{simplexLaw}(n)}
\{p:L_a(np)\}\leq\frac1{m+(n+m)},
$$

where $c$ is the proved positive padding-window constant. This is an approved
assembly target, not yet an actual-body or compilation verdict for the
near-leading theorem. No fixed-endpoint conditioning or post-conditioning
independence is used.

The MRCA common-carrier plan was subsequently changed to zero-extended
sequences $\mathbb N\to\mathbb R$, avoiding unavailable measurable-list
infrastructure. This revised interface receives **PASS** provided the exact
restriction identity on `Fin d` is exported. It gives injectivity at each
fixed dimension, not across different dimensions. Endpoint and barrier tests
must still use only the first $d$ coordinates. Shared-prefix concatenation
with $j<d$ then retains the same ordered-pair law. This replaces the proposed
list-carrier implementation choice without changing the mathematics.

Read the actual `GenerationBridge.lean` body: mathematical/statement **PASS**
now covers the orthant-product characterization, exponential tilting, exact
Gamma-density cancellation, endpoint marginal, and normalized joint law.
The positive-dimensional endpoint identification preserves its infinite mass;
only the preliminary tilting/restriction identities include dimension zero.

Read the actual `ThreeFactorOverlap.lean` body, including the new splitting
depth weights. Its numerator is
$n^{3/2+3q/(2n)}=n^{3-3j/(2n)}$ for $n=j+q$, exactly the previously assessed
critical pair weight. Both regime bounds and their combined domination
receive **PASS**. The explicit polynomial expansion and Gamma-type
integrability theorem also justify the finite translated-integral constant;
no numerical factorial evaluation is required. These are analytic and
characterization results, not a completed probabilistic second-moment bound.
No Lean/Lake was run by this reviewer.

### Resumed checkpoint: complete MRCA identity and uniform simplex ballot bound

Read the actual closed-identity portion of `ManyToTwo.lean`. Mathematical and
statement **PASS** covers `restrict_extendVector`, fixed-dimensional
injectivity, the actual extended pair-law recursion, and
`extendedGenerationPairIntensity_manyToTwo`. The intermediate sum includes
$j=d$, $q=0$ exactly once as its diagonal term; the final formula separates
that diagonal from $j<d$, where both suffixes have positive length. The
ordered off-diagonal overlap coefficient is one. The export
`extendedOverlapIntensity_eq_map` connects each sequence-space term back to
its finite-vector shared-prefix measure. All fixed-depth endpoint and barrier
tests can therefore be recovered by restriction; no injectivity across
different dimensions is asserted. This is an actual-model identity, not an
assumed many-to-two estimate.

Read the complete actual `SimplexNearLeading.lean` body through
`exists_simplex_nearLeading_bound`. Mathematical and statement **PASS** covers
the full interleaved product reconstruction, the full-measure simplex support
intersections, and the pointwise padding embedding. The canonical product
event has exactly the two short-block cycle factors, the middle angular
event probability, and the actual Cartesian Gamma-window mass. The resulting
inequality is

$$
\frac{c}{m^2}\mathbb P\{L_a(np)\}\leq\frac1{m+(n+m)},
$$

with the previously proved positive constant $c$. Neither independence
conditional on a specified endpoint nor any null-singleton conditional
probability is used.

For $a\geq10$, the implementation chooses $m=\lceil a^2\rceil$ and uses
$m^2\leq4a^6$. The case $n<a^6$ follows from probability at most one.
Replacing $a$ by $\max(10,a)$ then gives a single constant for every
nonnegative allowance and every positive dimension. Finally, positive
endpoint scaling gives precisely the allowance $an/S$, yielding

$$
\mathbb P_{\operatorname{simplexLaw}(n)}\{p:L_a(Sp)\}
\leq \frac{C}{n}\left(1+\left(\frac{an}{S}\right)^6\right)
\qquad(n>0,\ a\geq0,\ S>0),
$$

where $C=(4/c+1)10^6$ is independent of all three parameters. This uniform
quantifier scope is sufficient for the subsequent splitting-excess integral;
there is no hidden cutoff depending on that excess and no excess-rank
restriction. The proof is a substantive replacement of the source's informal
conditional-padding step, with the endpoint-independent simplex law supplied
by the already reviewed actual joint-law identities.

These are source-body mathematical verdicts. The new near-leading file and
closed MRCA implementation were still undergoing coordinator-managed
compilation at this checkpoint; this reviewer ran no Lean/Lake. No second
moment or actual positive-success seed is yet inferred from these statements
alone. The source inventory and all original obligations, including E1/E2,
remain unchanged.

Read the actual `PairCount.lean` body. Mathematical/statement **PASS** covers
the extended-nonnegative first and square moment identities, with all ordered
pairs and the diagonal counted once. Tonelli is applied to measurable actual
pushforward laws before any finiteness assumption. The subsequent real-square
integrability and integral conversion explicitly require finite actual pair
intensity and obtain almost-sure finiteness before using `toReal`. The exact
endpoint-leading count equality partitions all rank tuples by excess rank
and transports both endpoint and barrier through the actual increment map.
It includes dimension zero without silently discarding the empty path.

Read the actual `BallotIntensity.lean` body. Mathematical/statement **PASS**
covers endpoint measurability, nonnegativity, the factorial-shift exponential
bound for $d\geq12$, and its integration over nonnegative windows of width
at most one. The zero endpoint is handled by the positive power in the
generation density. Finite-window integrability is proved, rather than
relying on a totalized real integral. This file defines the density as the
actual simplex-event probability times the endpoint intensity density; the
downstream use must still transport the actual orthant event through
`GenerationBridge` to identify its measure with the corresponding integral.
For a suffix window whose lower endpoint is negative, that use must truncate
the lower endpoint to zero; a negative upper endpoint gives an empty event
on the orthant. The current window theorem correctly retains
$0\leq u\leq v$ and $v-u\leq1$ as explicit hypotheses. These files were
uncompiled at this review checkpoint; no Lean/Lake was run by this reviewer.

The implementation worker subsequently reported a clean `ManyToTwo` build
and an eight-export axiom probe showing exactly `propext`, `Classical.choice`,
and `Quot.sound`, including the closed MRCA identity and finite-vector
recovery exports. This is attributed build evidence supplied by the worker;
the reviewer did not run a compiler.

The proposed extension of the ballot intensity bound to every $d\geq1$
receives an interface-level mathematical **PASS**. For $2\leq d<12$, the
existing generation-intensity estimate with exponent $d-1$, together with
$\sqrt{d-1}\geq1$ and $d\sqrt d\leq d^2\leq144$, supplies the constant
$144e$. For $d=1$, the raw endpoint density is one even at zero, and
$e\exp(es-1)\geq1$ for $s\geq0$. Adding $144e$ to the previous constant
therefore covers every positive dimension and removes the need for separate
small-prefix and small-suffix estimates in the overlap sum. The actual
extension body was not yet available at this checkpoint.

The proposed actual overlap-event disintegration bound also receives an
interface-level **PASS** for positive prefix and suffix dimensions $j,q$.
Put $n=j+q$ and $A(S)=S-jm/n+1$. Two whole zero-leading paths with endpoints
in $(m-1,m]$ imply a common prefix and two suffixes near-leading with this
same allowance, which is nonnegative on the event. The outer integral must
retain $S\geq0$ and $A(S)\geq0$. The inner suffix integral may retain the
full interval $(m-1-S,m-S]$, using the endpoint density's zero value at
negative arguments. The actual orthant disintegration and nonnegative
Tonelli then give the product of one prefix density and the square of the
suffix-window integral. Joint measurability in allowance and endpoint must
be supplied for this varying-allowance use. No prior real integrability or
second-moment estimate is assumed by this measure-level interface.

Read the actual `BallotIntensityUniform.lean` body. The previously approved
all-positive-depth interface now receives actual-body mathematical **PASS**,
including $d=1$, $s=0$. The file also extends the exponential bound to every
real endpoint: negative endpoints have exactly zero intensity. Consequently
its width-at-most-one window estimate permits arbitrary real $u\leq v$,
including windows crossing zero. This legitimately removes the earlier
explicit truncation requirement when using this stronger export. Genuine
finite-window integrability is established inside the proof. An exported
version of that integrability fact was requested for the downstream
nonnegative-to-real integral conversion; replacing `Icc` by `Ioc` changes
only null endpoints. Compilation remained pending at this checkpoint, and
the reviewer ran no Lean/Lake.

### Actual three-factor overlap transport and analytic assembly checkpoint

Read all of `OverlapIntegral.lean`, `OverlapProduct.lean`, and
`PairDecomposition.lean`, plus the added full finite depth-sum theorem in
`ThreeFactorOverlap.lean`. Mathematical/statement **PASS** applies to these
actual source bodies; compiler checking of the new overlap modules remained
pending at this checkpoint.

`lintegral_generation_leading_weighted` transports a measurable allowance and
an arbitrary nonnegative extended-real weight depending on the endpoint
through the actual unnormalized orthant law. The simplex sum-one support
justifies the endpoint substitution. It does not divide by an endpoint
probability or require preliminary integrability. The suffix law is the
actual endpoint-window/near-leading event mass; its joint parameter
measurability is explicit. The two descendant sections form an ordinary
product, so their contribution is the square of that mass. `LeadingSplit`
supplies the same allowance to the shared prefix and both descendants. The
final restriction to nonnegative prefix endpoints follows from exact zero
intensity at negative endpoints.

`OverlapProduct` gives the exact exponent and denominator separation. For
$n=j+q$ and $em=n+\frac32\log n$, the exponential product is

$$
n^{3/2+3q/(2n)}\exp(-e\delta).
$$

The denominators yield exactly the previously reviewed depth weight. The
translation $u=\delta+1$ contributes the factor $\exp(e)$ already retained
in `threeBallotIntegralConstant`. Actual integrability is proved before the
real integral bound. The coefficient $U$ is arbitrary in the identities and
integrability statement; nonnegativity is explicit where multiplication of
inequalities needs it. The natural-dimensional time-center corollary has the
same critical coefficient $3/2$.

One downstream boundary transport remains explicit: the stochastic
restriction $A(S)\geq0$ yields the closed half-line
$S\geq jm/n-1$, while the analytic integral export uses the corresponding
open half-line. Their difference is one volume-null singleton. A direct set
inclusion cannot replace that null-boundary argument.

`PairDecomposition` evaluates the actual sequence-space identity after
restriction to the fixed dimension. It gives the diagonal mean, the
independent-root squared mean, and precisely the ordered interior overlaps
$1\leq j\leq d-1$. No factor two is introduced. The unrestricted identity
includes dimension zero; the decomposition separating the root term
requires $d>0$. All identities remain valid in extended nonnegative reals
before finiteness is proved. The full depth sum is bounded by two convergent
$3/2$-power series, using injectivity of $j\mapsto d-j$ on the relevant
finite interval; empty depth ranges are included.

The newly exported `BallotIntensityUniform` finite-window integrability and
`Ioc` bound were also read and receive **PASS**. The coordinator reports clean
builds for these ballot modules, the generation reconstruction, and the full
depth-sum theorem. Separately, the near-leading worker reports a clean
`SimplexNearLeading` build and an eight-export axiom probe with exactly
`propext`, `Classical.choice`, and `Quot.sound`. These are attributed
implementation-worker checks, not compiler runs by this reviewer. The actual
uniform success seed and the original paper obligations are not advanced by
this review alone.

Read the actual `ClockSeedMoment.lean` body. Mathematical/statement **PASS**
covers measurability, nonnegativity, positive-depth first integrability by
generation-count domination, and the pointwise inclusion from positive
exact-leading count to the actual reachability event. The assembly theorem
keeps the uniform square-moment bound and square integrability as explicit
premises. Given an eventual positive first-moment lower bound $c$ and a
positive square-moment upper bound $B$, it sets $C=B/c$, obtains
$\mathbb P(Z_d>0)\geq c^2/B$, and chooses
$p=\min(1,c^2/B)>0$ with time shift $K=0$. The eventual threshold explicitly
includes $d\geq1$. This conditional helper does not by itself discharge the
actual seed or any main-paper statement.

Also read the new extended-overlap preimage/restriction exports in
`OverlapIntegral` and the closed-half-line integral and integrability exports
in `OverlapProduct`: mathematical **PASS**. The latter use the null boundary
singleton explicitly, so the earlier open-versus-closed integration detail
is now resolved within those public interfaces. The former recover exactly
the finite-dimensional event without changing its mass or overlap
coefficient. Source and scope are unchanged, and this reviewer ran no
Lean/Lake.

Read the full actual `OverlapBound.lean` body. Mathematical/statement **PASS**
covers the nonnegative suffix-window integral bound and both finite-vector
and extended-sequence critical overlap estimates. The real suffix integral
is used only after its actual integrability is available. The three pointwise
ballot factors apply on the explicit nonnegative-allowance domain; their
product is nonnegative. Enlarging that domain to the closed half-line is
therefore legitimate. The previously proved product integrability justifies
the final nonnegative-to-real integral conversion. The resulting constant is
exactly

$$
\bigl(\texttt{uniformBallotIntensityConstant}\bigr)^3
\,\texttt{threeBallotIntegralConstant},
$$

times the reviewed depth weight, for every pair of positive natural
dimensions $j,q$. The endpoint center is exactly `timeCenter (j + q)`.
There is no hidden short-depth cutoff, rank-window hypothesis, fixed-label
cancellation, or supplied overlap estimate. This actual overlap bound still
requires the separate finite depth sum and first-moment upper bound before
it yields a global second moment. The implementation was uncompiled at
this source-body checkpoint; no Lean/Lake was run by the reviewer.

Read the complete actual `GlobalSecondMoment.lean` body through
`clockLowerSeed`. Mathematical/statement **PASS** covers the unconditional
source-level assembly. The exact-leading endpoint-window mean is bounded by
the exact leading cumulative intensity
$m_d^d/(d!d)$. Its already proved critical limit supplies a fixed eventual
upper bound $M$. The actual pair decomposition gives the diagonal mean,
its independent-root square, and the interior overlap sum. The transport
$j+(d-j)=d$ preserves the original critical event in every interior term;
both dimensions are positive there. The overlap estimate and uniform depth
sum yield the stated constant without a fixed-labelled-path assumption.

The source then proves finite actual pair intensity before deriving real
square integrability and converting its integral. Choosing
$B=1+M+M^2+C D$ supplies the required positive uniform second-moment bound,
where $C$ is the overlap constant and $D$ is the depth-sum constant. The
final `clockLowerSeed` uses the reviewed actual first-moment lower bound and
the moment-to-success helper; no additional unproved probabilistic premise
appears in this assembly. This is a mathematical source-body verdict, not
yet kernel evidence: the new file and its overlap dependencies were still
undergoing coordinator-managed compilation. An unconditional theorem in
uncompiled source does not by itself advance the paper coverage record.
The original source inventory remains unchanged, and this reviewer ran no
Lean/Lake.

### Theorem 1.2 final source and statement milestone

Recomputed the unchanged `main.tex` SHA-256:
`7b7d6ef6e2200b3129cbd4a74ef45c09fbf758643ce63489bf67f2aef93301f3`.
Re-read the source family definition, the Introduction's Theorem 1.2
(lines 245–253), its high/low proof, and the current `MainStatements`,
`UniformHeightBounds`, `FamilyMinima`, finite-word law, RRT seed transfer,
deficit amplification/integration, corrected high-population margin, and
final high/low assembly. The prior independent reviews cover the actual
PWIT, simplex ballot, pair intensity, and global moment dependencies added
along this route.

The final statement correspondence receives **PASS**:

| Feature | Source and formal target correspondence |
| --- | --- |
| Family | Every admissible word with exactly $n$ attachments; admissibility permits extinction at the final step, as does the source condition $\tau\geq m$. |
| Observable | The actual forward tree's maximum height and its actual expectation; no active-vertex depth or clock surrogate remains in the final target. |
| Threshold | Exactly $e\log n-5\log\log n$. Totalized logarithms at small indices do not affect either eventual conclusion. |
| Probability | For every positive error tolerance there is one threshold in $n$ valid for every word in the family; the success event uses height greater than or equal to the real threshold. |
| Expectation | One threshold in $n$ works for every word in the family. |
| Minima | The family is finite and nonempty, and the existing `FamilyMinima` equivalences identify these uniform targets with the displayed minimum limit and eventual minimum-expectation bound. |
| Extra premises | `uniformHeightClaims` and its two projections have no seed, moment, asymptotic, or coupling hypothesis. |

The proposed `Paper.theorem_1_2` conjunction and probability/expectation
projections are therefore faithful publication-facing statements. The actual
source proof transports the proved clock success estimate to the genuine
RRT edge-index law, amplifies it to a bounded positive deficit, and uses the
coefficient-two regularized center. At the corrected high-population index
$r_n-1$, the remaining logarithmic margin has positive coefficient $3-e$.
The low-population branch and its extinction correction are reused without
weakening their scope. Taking the maximum of the two branch thresholds
preserves uniformity in the choice word.

This proof is a documented departure from the paper's appeal to sharp
centered RRT asymptotics. It proves the required weaker input directly using
actual all-rank exactly-leading paths, the Poisson sibling pair intensity,
and a global second moment. The interior and rank-barrier arguments bypassed
by this route are not thereby certified. E1/E2 remain full unresolved
obligations; the literal printed high-prefix index $r_n$ remains uncertified
as recorded in SF2, with the corrected $r_n-1$ form used here. H3/H4 may be
credited for their corrected final lower-bound conclusions after proof
verification, with the source's sharp-expansion step still explicitly
unverified under E1. D5 is the exact final branch assembly, not a new
assumption.

At this milestone the unconditional source chain was still undergoing its
coordinator-managed `UniformHeightBounds` build and refreshed axiom audit.
Accordingly this is **source/statement PASS**, not yet a certification of
kernel-checked completion. No coverage status is advanced solely by this
review, no full-paper coverage is claimed, and no Lean/Lake was run by the
reviewer. The source and inventory scope have not changed.

### Coarse upper-tail interface checkpoint

The proposed actual RRT upper-tail estimate receives an interface-level
mathematical **PASS** for all $n\geq0$ and natural $d\geq1$:

$$
\mathbb P(H_n\geq d)\leq
2\exp\bigl(e\log(2(n+1))-d\bigr).
$$

At $t=\log(2(n+1))$, the geometric index counts edges, so the lower mixture
comparison uses $N_t\geq n$ and the tail exponent is $n$, not $n+1$.
Bernoulli's inequality gives this event probability at least
$1-n/(2(n+1))\geq1/2$. The actual PWIT generation first moment and its
Stirling bound then give the displayed estimate.

The proposed positive-excess bound above $b_n=e\log(n+1)$ also has the
correct constant:

$$
\mathbb E[(H_n-b_n)_+]
\leq e\log2+\frac{2}{1-\exp(-1)}.
$$

Shift the unit-grid center by $e\log2$ before applying the tail estimate.
Every ceiling threshold is then at least one, including when $n=0$, and
the $j$th tail is bounded by $2\exp(-j)$. The actual height support bounds
justify the finite grid before summing the geometric majorant. These are
approved interfaces only; no new implementation body was available at this
checkpoint. Neither estimate supplies the sharp $3/2$ logarithmic correction
or the full E1/E2 assertions, which remain in scope.

### M2 checked-build milestone and affected-inventory reconciliation

The coordinator reports a clean full `lake build` of 4,082 jobs. Read the
current full axiom-audit log at
`/private/tmp/freezing-growth-m2-final-2026-11-01-axioms.log`: its header
records 3,123 checked `FreezingGrowth` declarations with transitive axioms
restricted to `propext`, `Classical.choice`, and `Quot.sound`. The explicit
final queries include the actual global second moment, `PWIT.clockLowerSeed`,
`uniformHeightClaims`, and all three new `Paper.theorem_1_2` exports with
exactly those permitted axioms. Also read the actual numbered exports in
`PaperResults.lean`; they match the previously approved conjunction and
projections. The separate 67-module kernel replay was still running at this
checkpoint. This reviewer did not run Lean/Lake or independently rerun that
audit.

Reconciled the five affected inventory rows against their existing complete
scope, including the source's intermediate mathematical assertions:

| ID | Recommended current status | Exact reconciliation |
| --- | --- | --- |
| M2p | Complete | `Paper.theorem_1_2_probability` proves the unchanged uniform target; the existing minima equivalence supplies the displayed minimum limit. |
| M2e | Complete | `Paper.theorem_1_2_expectation` proves the unchanged eventual uniform inequality, and the minima equivalence preserves its source meaning. |
| H3 | Partial | The final corrected high-profile expected-height lower bound is now proved. The displayed fine RRT mean expansion with $-\frac32\log\log r_n+O(1)$ is still unproved under E1, including at the corrected index. Its presence in this row prevents classifying the entire row as complete. |
| H4 | Complete in corrected form, via an alternative proof | The corrected centered-threshold limit and the uniform high-profile probability conclusion are proved. The new bounded-deficit argument replaces the appeal to full centered tightness. The printed $r_n$ domination remains uncertified under SF2/H2, and E1 retains the full centered-tightness assertion. |
| D5 | Complete | `uniformHeightClaims`, exported as `Paper.theorem_1_2`, assembles the high/low branches with thresholds uniform in the word; `FamilyMinima` supplies the exact minimum formulations. |

Thus H3 must not be upgraded merely because Theorem 1.2 is now proved.
Similarly, H4's corrected-form completion does not certify the literal
printed $r_n$ comparison or the sharp external asymptotics. E1/E2 remain
unchanged full obligations. Starting from the prior 85-ID baseline of
39 complete, 12 partial, 31 pending, and 3 open questions, these updates
alone give **43 complete, 9 partial, 30 pending, and 3 open questions**.
No source or scope change was found, and no complete-paper or publication
readiness claim follows from this milestone.

### Subsequent M1 helper checkpoints: actual depth moments and coarse height tail

Read the complete actual `RRTUpperTail.lean` body through
`uniformUpperExcess`. Mathematical/statement **PASS** now covers the actual
geometric-mixture lower comparison, the edge-index tail at $N\geq n$, the
PWIT first-moment upper bound, and the integer and real-strict RRT tail
estimates. The finite unit grid uses the genuine almost-sure support
$H_n\leq n$ and includes the empty grid at $n=0$. All integrability is
provided by the actual finite law. The final positive-excess constant is
exactly the previously approved $e\log2+2/(1-\exp(-1))$. This source was
outside the completed M2 import/replay milestone and awaiting its own
compilation; the sharper E1/E2 obligations are unchanged.

Read the foundational actual `RRTDepthMoments.lean` definitions, arbitrary-test
integral recurrence, mean identity, and centered-first-moment identity.
Mathematical/statement **PASS** covers those bodies. The proposed subsequent
variance and fourth-moment recurrences receive an interface-level **PASS**.
Here $\mu_n$ is the actual uniform-vertex mean depth, $p=1/(n+2)$, $V_n$ its
centered second moment, and $K_n$ its centered fourth moment:

$$
\mu_{n+1}=\mu_n+p,\qquad
V_{n+1}=V_n+p(1-p),
$$

$$
K_{n+1}=K_n+6p(1-p)V_n+p(1-p)^4+(1-p)p^4.
$$

Both odd cross terms in the fourth expansion vanish by centering. The
parameter bound $p\leq1/2$ gives $\mu_n/2\leq V_n\leq\mu_n$; the Bernoulli
fourth term is $p-p^2-3[p(1-p)]^2\leq p$, which suffices for
$K_n\leq3\mu_n^2+\mu_n$. These recurrences derive from the actual marginal
law, not an assumed joint coupling of vertices.

The proposed actual tree-mean variance interface also receives **PASS**.
For the all-attachment state, let $M$ be its active mean depth. Given a
uniform parent of depth $d$, the new centered mean is

$$
(M-\mu_n)+\frac{d-M}{n+2}.
$$

Averaging its square and then integrating the actual state law yields
$v_{n+1}=(1-p^2)v_n+p^2V_n$. State-level identities must retain the valid
all-attachment support and active cardinality $n+1$; they do not hold in
this form for arbitrary empty or frozen states. Finite height bounds justify
the square integrability. The invariant
$v_n\leq1-\mu_n/(n+1)\leq1$ closes by exact algebra using $V_n\leq\mu_n$.
No martingale or conditional-independence premise is needed.

Finally, the proposed scalar moment-to-absolute-moment estimate has the
correct constant. For $\mu\geq1$, take $t=4\sqrt\mu$ in
$y^2\leq ty+y^4/t^2$. The fourth-moment term is at most $\mu/4$, so the
variance lower bound implies $\mathbb E|D-\mu|\geq\sqrt\mu/16$. The tree-mean
variance bound gives $\mathbb E|M-\mu|\leq1$. Conditional finite averaging
then gives the same-tree pair-gap lower bound, with distinct sampling
requiring at least two vertices. The without-replacement average is
$N/(N-1)$ times the with-replacement absolute-gap average. This prospective
route bypasses a CLT; it does not prove E4 or any M1 statement at this
checkpoint. The reviewer ran no Lean/Lake.

Read the completed actual bodies of `RRTDepthMoments.lean`,
`AbsoluteMomentBounds.lean`, and `RRTMeanDepthVariance.lean`.
Mathematical/statement **PASS** now covers their full statements and proof
routes, beyond the earlier interface checkpoints. The fourth-moment
polynomial correctly retains its linear term pointwise, then removes it
using the actual centered first integral. A misleading comment that said
both odd terms canceled pointwise was corrected by the author; the proof
body already made the proper distinction. The fourth Bernoulli polynomial
upper bound is valid even for arbitrary real parameters by its exact
$p-p^2-3[p(1-p)]^2$ identity; the probabilistic recurrence still uses the
actual parameter $p=1/(n+2)$.

The scalar absolute-moment lemmas retain the necessary integrability of the
first, second, and fourth powers. Their constants and inequality directions
are correct. The bounded-absolute-deviation lemma explicitly assumes a
probability measure. The tree-mean implementation retains valid-state and
nonempty-active-set hypotheses for the conditional update, obtains active
cardinality $n+1$ from the actual almost-sure state counts, and applies the
genuine transition-law integral identity. Its square integrability follows
from finite height bounds, before any recurrence is integrated. The exact
variance invariant and the absolute-deviation bound one therefore concern
the actual random tree mean, without independent-vertex or martingale
assumptions. These new M1 helpers were still awaiting their own compiler
phase; no M1, E1, E2, or E4 completion follows from this review. The reviewer
ran no Lean/Lake.

The proposed uniform-freezing pair-average bridge receives an interface-level
mathematical **PASS**. For an active set of cardinality $N$ and an observable
with $f(k,k)=0$, the full ordered double sum divided by $N(N-1)$ equals the
actual ordered-distinct-vertex average. Distinct vertices of equal depth
remain part of the sampling space; their contribution happens to vanish for
this observable. When $N\geq3$, each ordered distinct label pair survives
exactly $N-2$ choices of the uniformly frozen vertex. This gives the exact
one-freeze invariance after division by $(N-1)(N-2)$ in the smaller set.
The guard cannot be weakened to $N\geq2$: the two-to-one transition generally
destroys the gap. Iteration from $m+1$ active vertices through $m-1$ freezes
therefore requires $m\geq1$, with $m=1$ the zero-freeze base case. The absolute
gap consequence does not establish the full arbitrary-test pair law; that
stronger obligation must remove the vertex-label diagonal explicitly, not
the equal-depth pairs.

The proposed rough height absolute-deviation interface also receives
mathematical **PASS**. With $b=e\log(n+1)$ and
$r=2\log(1+\log(n+1))\geq0$, the pointwise inequality

$$
|H-b|\leq(H-b)_+ +(b-r-H)_+ +r
$$

combines the actual upper excess and coefficient-two lower deficit. Their
uniform bounds give an unconditional $C+2\log(1+\log(n+1))$ absolute-deviation
bound, including $n=0$. This is a coarse bound only; it does not certify the
sharp centered E1/E2 assertions. Neither proposed new body had yet been
read at this interface checkpoint.

Subsequently read the complete actual `RRTRoughAbsoluteDeviation.lean` body:
mathematical/statement **PASS**. Its finite-law integrability, nonnegative
regularization correction, pointwise absolute-value split, and seed-derived
uniform deficit are explicit. The final constant is the sum of the proved
upper-excess constant and the actual lower-deficit constant, uniformly for
all natural edge counts. It adds neither an E1/E2 premise nor a sharp
asymptotic conclusion. Compilation remained pending; no Lean/Lake was run
by this reviewer.

### Actual uniform-freezing and same-tree gap bodies

Read the actual `FinitePairAveraging`, `ForwardFiniteSupport`,
`ForwardPairAveraging`, `TwoSurvivorGap`, and `RRTDepthGap` source bodies.
Mathematical/statement **PASS** covers all five. The finite-support argument
constructs an explicit finite set of possible states at every finite horizon,
including the unchanged state after extinction. Every real state observable
is therefore integrable; no moment bound for an unbounded-horizon process is
being inferred. The forward step enumeration uses the valid label bound and
retains the actual transition law.

The zero-diagonal finite averaging identities preserve ordered pair counts
without requiring symmetry. Their freezing invariance explicitly requires
at least three active vertices. The source prefix with $m$ attachments and
$m-1$ freezes has exactly two active survivors for $m\geq1$, and the iterated
freeze expectation equality is proved under the actual forward law. Equal
depths are allowed throughout. Its absolute-gap statistic agrees with the
actual RRT's ordered-distinct gap, and the divergence transfers along this
equality.

`RRTDepthGap` explicitly identifies both the same-tree with-replacement
double average and the ordered-distinct `uniformRootPair` integral. The
off-diagonal restriction is on vertex labels. The finite triangle/Jensen
inequality, actual marginal centered moments, and actual tree-mean deviation
give the lower bound $\sqrt{\mu_n}/16-1$. All real integrations use proved
finite-horizon integrability, and the comparison with distinct sampling
retains $n\geq1$. This verifies the absolute-gap consequence; it does not
assert the full arbitrary-test two-survivor law or the source's joint CLT.
The coordinator reports `ForwardFiniteSupport` compiled; the remaining new
helper chain was undergoing its own compilation at this source checkpoint.
No Lean/Lake was run by the reviewer.

The proposed `RRTSplitRoughGap` interface also receives mathematical **PASS**.
`heightPairLaw n` is the unshifted pair of component heights for the first-edge
split of an $(n+1)$-edge tree, with edge counts $k,n-k$ and uniform
$0\leq k\leq n$. The two rough-deviation terms contribute
$2C+4\log(1+\log(n+1))$. The average difference of the logarithmic centers is
at most $2e$, using reflection of the finite sum and
$\log((n+1)!)\geq(n+1)\log(n+1)-(n+1)$. Thus the proposed uniform bound has
the correct constant and includes $n=0$. The attaching edge's extra one is
not part of `heightPairLaw`; any later shifted-gap observable must include
its separate unit correction. This interface does not prove E1/E2.

The proposed arbitrary-test `activePairHeightMean` bridge receives an
interface-level mathematical **PASS**. Its zero diagonal is imposed by the
vertex-identity test $u=v$, while the test function may depend arbitrarily
on both depths and the full tree maximum. Freezing leaves that full maximum
unchanged, so the same $N\geq3$ deletion-count identity applies without
assuming a zero depth-diagonal for the test. For exactly two active vertices
the value is the average of the two orientations; it reduces to one oriented
value only when the test is symmetric in its first two arguments. For a
nonsymmetric test it still represents an explicitly uniform ordered pair,
as needed when a later freeze chooses which root survives.

This proposed bridge preserves dependence between the two depths and the
initial full maximum. It characterizes that actual profile's expectations,
not the entire labelled-tree grafting construction or a joint coupling of
both final heights. Those stronger source claims remain separate obligations.
The split-gap worker's proposed use of actual pair-law symmetry to reduce
the estimate to twice one marginal deviation also receives **PASS**; it
preserves the same constant and all zero-edge boundary cases.

Read the actual `RRTSplitRoughGap.lean` body: mathematical/statement **PASS**
now covers the exact height-pair mixture, first-marginal integral identity,
swap integral identity, logarithm-defect sum, larger-center absolute-moment
comparison, and final uniform coarse imbalance bound. Actual pair-law
symmetry gives the factor two, and the logarithm-defect average costs at most
$e$ for one marginal. All finite-law integrability and the unshifted component
convention remain explicit. This does not prove the sharper uniformly bounded
imbalance asserted in the source.

The proposed polynomial-suffix depth-gap domination receives an
interface-level mathematical **PASS**. The actual mean satisfies
$\mu_m/\log m\to1$, and for fixed positive natural $K$ the regularized
$\log\log(m^K+1)$ term is negligible compared with $\sqrt{\log m}$.
For an arbitrary real coefficient $C$, replacing it by $|C|$ gives a safe
lower comparison. Thus the already reviewed actual distinct-gap lower bound
implies divergence after subtracting that logarithmic-logarithmic term.
Choosing suffix size $m^9$ may supply the main existential witnesses; it
does not alone establish the full source assertion indexed by every large
$n$ with $m=\lfloor n^{1/9}\rfloor$. That stronger source obligation remains
retained. No compiler was run by this reviewer.

Read the actual `ForwardPairMaximum.lean` body and the new
`twoActivePrefix_pair_height_mean` and `twoActivePrefix_profile_integral`
bodies: mathematical/statement **PASS**. The arbitrary test retains the
full old maximum. Its identity diagonal is removed before averaging, and
the exact two-active profile identity uses a multiset, so equal-depth
survivors retain both occurrences. The general profile integral therefore
preserves the actual dependence between both survivor depths and the old
maximum. It still forgets the labelled-tree geometry.

Read the actual `RRTDepthGapAsymptotics.lean` body: mathematical/statement
**PASS** covers the scalar square-root/logarithm comparison, deterministic
polynomial-horizon bound, eventual comparison with the actual mean depth,
and divergence after subtracting any fixed multiple of the regularized
polynomial-horizon logarithmic-logarithmic term. The implemented exponent
range includes $K=0$, which is valid because that error is then constant.
The final natural-power cast preserves the suffix indexing exactly. This
module was uncompiled at the checkpoint; no compiler was run by the reviewer.

### Proposed I1/I8 helper-milestone coverage reconciliation

Re-read the exact existing inventory rows and source line 437. Once the
actual prefix-gap theorem has clean build and axiom evidence, **I8 may be
marked complete by an alternative proof**: `tendsto_expectedTwoSurvivorGap_atTop`
is exactly the asserted absolute-depth-gap expectation divergence. The cited
normal-limit argument is bypassed, not verified, and **E4 remains pending**.
The moment proof does not need uniform integrability or a joint CLT.

**I1 should be partial.** The actual prefix has two active vertices, and the
reviewed arbitrary depth/full-maximum profile expectation identity is
available. The full underlying labelled-tree law with its conditional
uniform pair of vertex labels is not exported, so the entire I1 assertion
is not yet certified. I2/I3's full grafting and joint-height coupling claims
remain separate. The coarse height and component-gap estimates do not
automatically complete L1/L2, I5/I6/I7/I9, or E1/E2/E4.

If these are the only changes from the current 85-ID baseline, upgrading I8
from pending to complete and I1 from pending to partial gives
**44 complete, 10 partial, 28 pending, and 3 open questions**. This is a
classification recommendation contingent on the corresponding proof
evidence, not a report update or a complete-paper claim by the reviewer.

The proposed real-threshold exponential lower-tail interface receives
mathematical **PASS**. With $L=e\log4$, $\rho=1-p/2$, and
$\alpha=-\log\rho/L>0$, the existing grid estimate gives

$$
\mathbb P(H_n<r)\leq
\exp\bigl(\alpha(A+L+r-b_c(n))\bigr).
$$

For a nonnegative grid parameter, its natural floor supplies the correctly
oriented threshold comparison, and multiplying the floor inequality by
$\log\rho<0$ reverses its direction as required. A negative parameter is
covered by probability at most one. The endpoint $p=1$, zero-edge tree, and
all real thresholds are included. The unconditional coefficient-two version
can take offset $B=A+L\geq0$ from the actual seed. Its rate is seed-dependent;
the source's fixed E2 rate and L1 exponent are not implied automatically.

The proposed `SeededPrefixExpectations` interfaces receive mathematical
**PASS**. The baseline continuation tower followed by the arbitrary profile
test preserves dependence among the two depths and the old maximum. The
freeze-then-attach continuation is the equal mixture of the two possible
surviving-root profiles. The attach-then-freeze continuation has six
occurrence-level branches of weight $1/6$. After attaching to depth $a$,
their active multisets are $\{a,b\}$, $\{a+1,b\}$, and $\{a,a+1\}$, all
with maximum $\max(M,a+1)$; the three corresponding branches after attaching
to depth $b$ retain $\max(M,b+1)$. The raised maximum is retained even when
the new child is frozen, and coinciding depths do not collapse the sampling
weights. The intended source domains $m\geq1$, $n\geq0$ are correct. These
are profile/height-law bridges, not a certification of the complete
labelled-tree joint grafting construction.

Read the complete actual `RRTLowerTailExponential.lean` body:
mathematical/statement **PASS**. The natural-floor inequalities, positive
rate, identity $\alpha L=-\log\rho$, and exponent rearrangement have the
correct directions. The negative-grid-parameter case uses probability at
most one. The final unconditional bound has offset $A+L\geq0$ and retains
every natural edge count and real threshold. No fixed sharp source rate is
asserted. Compilation was pending, and the reviewer ran no Lean/Lake.

The proposed actual old-tree residual bounds receive interface-level
mathematical **PASS**. For the actual old height $M$ and split-component
maximum $Y$, the pointwise split
$(M-Y)_+\leq(M-T)_+ +(T-Y)_+$ is valid without independence. Under the true
old-tree support and $T\geq0$, it yields the preliminary tail estimate
$2m\exp(b_m^{\mathrm{upper}}-T)+T\mathbb P(H_{\lfloor n/2\rfloor}<T)$.
The split maximum dominates the half-size RRT because each split has at
least one component with that many edges. All zero-edge boundaries remain
included.

For the main existential comparison, the weaker uniformly bounded residual
is sufficient. If $e\log(m+1)\leq T=b_2(\lfloor n/2\rfloor)$, decreasing-test
stochastic monotonicity gives

$$
\mathbb E[(M-Y)_+]
\leq \operatorname{upperExcess}(m)
   +\operatorname{lowerDeficit}(2,\lfloor n/2\rfloor).
$$

The center comparison itself implies $T\geq0$. Actual one-step height growth
and finite-horizon integrability justify the proposed antitone-test proof;
no independent replacement of the old maximum is required. This supplies
a uniform eventual constant for $n=m^9$. It does not prove I5's stronger
zero-limit assertion, which remains separately retained.

The main scalar comparison's coefficient was also checked: for real $d$ and
$\delta$,

$$
\max(0,d+\delta)-\max(1,\delta)
\geq \max(0,d)-|\delta|-1.
$$

Thus one component-imbalance expectation, not two, suffices in the proposed
main lower bound. Ordered-pair averaging gives half the expected absolute
depth gap without independence from the old maximum. The local six-branch
attach-then-freeze interface remains valid for arbitrary natural depths and
maximum, even for algebraically inconsistent profiles; actual source
profiles separately satisfy their consistency conditions. Repeated-depth
occurrences retain all six sampling weights.

### Actual seeded word, residual, and comparison checkpoint (2026-11-01)

Read the complete actual bodies of `ProfileWordExpectations.lean`,
`SeededPrefixExpectations.lean`, `SeededDeletionExpectations.lean`,
`AttachFreezeSeeds.lean`, `AttachFreezeWordExpectation.lean`,
`RRTSplitResidual.lean`, `SeedComparison.lean`, `SeededGrowthGap.lean`, and
`AttachFreezeMeanComparison.lean`. Mathematical/statement verdict:
**PASS**. This is an independent source-body review; the reviewer ran no
Lean/Lake and does not infer completion from source alone.

The word tower uses actual finite-horizon profile laws and genuine
integrability of arbitrary real observables. The baseline, freeze-then-attach,
and attach-then-freeze expectation identities average over the actual old RRT
state and its ordered-distinct active vertex pairs. In particular, the two
depths and the full old maximum remain correlated. The arbitrary profile
test retains the multiset multiplicities when both depths coincide. The
six attach-then-freeze branches each have weight $1/6$, and retain the
maximum of the newly attached child even when that child is frozen. These
are precise height/profile identities, not a proof of the stronger complete
labelled-tree grafting law.

The residual is the positive-part expectation under the actual product of
the old RRT height law and the split height-pair law. Antitone-test time
monotonicity follows from actual one-step tree-height monotonicity and
finite-horizon integrability. In each split at least one component has
$\lfloor n/2\rfloor$ edges, which gives the stated split-deficit domination,
including $n=0$ and arbitrary real threshold. The threshold split and center
separation therefore prove the uniform residual bound without a decay
premise. The two Fubini/pushforward exports identify it exactly with the
integral of `splitDeficitAt` evaluated at the actual old tree maximum.

The terminal polynomial-suffix lemmas have the correct natural-division
and logarithm directions. For $m\geq2$, putting $q=\lfloor m^9/2\rfloor$
gives $q\geq m^8$, $m+1\leq m^2$, and

$$
e\log(m+1)\leq2e\log m
\leq8(e-2)\log m
\leq(e-2)\log(q+1)\leq b_2(q).
$$

The middle inequality uses $e>8/3$. Thus `uniformResidualBound_pow_nine`
holds for every $m\geq2$. It does not prove the source I5 zero limit.

`SeededGrowthGap` represents all three growth means under the same actual
split law. The star profile's raised maximum is absorbed by its nonnegative
new-child component height. The scalar maximum/minimum identities then
give exactly

$$
\operatorname{base}-\operatorname{FA}
\geq \frac{|a-b|}{2}
 -\operatorname{roughHeightGap}(n)-1
 -\operatorname{splitDeficitAt}(n,M),
$$

under the explicit consistency condition $\max(a,b)\leq M$. There is one
component-imbalance error and one added-edge error. The deterministic scalar
lemma itself uses no unwarranted probabilistic independence.

`AttachFreezeMeanComparison` uses the same actual split law to show that
increasing both seed depths and the retained maximum by at most one increases
the eventual mean by at most one. Both seed-profile consistency conditions
are explicit. Four nonstar branches are at most the baseline mean plus one;
the two star branches sum to twice the freeze-then-attach mean. Consequently

$$
\operatorname{AF}\leq
\frac{\operatorname{FA}+2\operatorname{base}+2}{3},
\qquad
\operatorname{base}-\operatorname{AF}\geq
\frac{\operatorname{base}-\operatorname{FA}-2}{3}.
$$

The proposed global averaging interfaces also receive **PASS**. For
$m\geq1$, the old RRT has $m+1\geq2$ active vertices, so its actual
ordered-distinct pair mean is a positive normalized average. Averaging the
local inequalities gives the freeze-then-attach word gap at least
`expectedDistinctDepthGap m / 2 - roughHeightGap n - 1 - residual m n`,
and the attach-then-freeze word gap at least one third of that first word
gap minus $2/3$. All $n\geq0$ remain included. Along $n=m^9$, the already
reviewed depth-gap-minus-loglog divergence and bounded residual suffice for
the main existential conclusions. The full floor-indexed source I9 and the
sharp E1/E2 estimates remain separate obligations.

The planned admissibility bookkeeping has the correct domains: the
two-active prefix with $m\geq1$ ends with two active vertices; the two local
balanced words have intermediate counts one and three respectively; an
arbitrary all-attachment suffix remains positive. A late active-count
formula must be used on the actual finite prefix or an explicitly defined
infinite schedule. No paper coverage is advanced by these interface checks.

Read the subsequent complete bodies of `PairMaximumStatistics.lean`,
`FreezeAttachGap.lean`, `AttachFreezeGap.lean`, and
`TwoSurvivorAdmissible.lean`: mathematical/statement **PASS**. The explicit
uniform-pair integral removes only equal vertex labels, not equal depths.
Its constant, linearity, and monotonicity exports retain the common full
maximum. Actual old-tree validity and active cardinality supply both seed
consistency and a nonzero ordered-pair normalization. Both global word-gap
proofs use these facts before integrating, and preserve all stated finite
domains $m\geq1$, $n\geq0$.

The actual freeze-then-attach gap divergence has the correct error
coefficient: subtracting eight times the regularized loglog term from the
depth gap before dividing by two exactly accounts for the component-gap
bound's coefficient four. The bounded residual contributes only a constant.
The eventual ninth-power result and its arbitrary-large-gap witness retain
$m\geq2$. The attach-then-freeze bound subtracts two before division by
three, matching the six-branch calculation.

The admissibility file explicitly documents the false-default infinite
extension used by its late active-count identity. Its positivity and
admissibility applications remain within the finite word. The endpoint
count is two and the local intermediate counts are one or three; $m=1$ and
$n=0$ are included. No stochastic premise is hidden in this bookkeeping.

The reviewer also read the completed historical M1-helper axiom log
`/private/tmp/freezing-growth-m1-helper-2026-11-01-axioms.log`. Its header
reports **3283 FreezingGrowth declarations**, with all transitive axioms
among `propext`, `Classical.choice`, and `Quot.sound`; its explicit queries
include the two-survivor gap divergence and profile integral. This evidence
applies to that integrated helper closure. The newer global gap and local
seed files still require their own integration/build/axiom evidence before
main-result coverage is advanced. No compiler was run by the reviewer.

### Introduction wrappers and coverage recommendation (2026-11-01)

Read `MainDeletionClaims.lean` and compared the unchanged `MainStatements`
targets with `main.tex` lines 210–231. Actual-body and statement-fidelity
verdict: **PASS**, subject to the coordinator's subsequent clean compiler
and axiom evidence. `removeFreezeAttachClaim` chooses $(m,n)=(m,m^9)$ once,
proves the three required word admissibilities, and obtains the freeze-only
consequence by appending one final attachment to the baseline. Both
inequalities therefore use exactly the same witnesses. The second wrapper
requests a freeze-then-attach gap at least $3A+2$ and applies the verified
affine comparison, giving the exact attach-then-freeze target. Not using the
hypothesis $A>0$ in these implementations strengthens their applicability;
it does not replace or weaken the source statements.

After clean integration/build/axiom evidence, **M1i, M1f, and M1ii may be
marked complete by this alternative proof**. From the current 85-ID count
of 44 complete, 10 partial, 28 pending, and 3 open questions, these three
upgrades alone give **47 complete, 10 partial, 25 pending, and 3 open
questions**. The report should distinguish source dependencies from the
actual alternative dependency chain; sharp height estimates and the cited
joint CLT are not premises of these new main proofs.

No stronger source intermediate follows automatically. In particular,
I9/II5 retain their full floor-indexed asymptotic assertions, II3 retains
its sharper $1/(n+1)$ conditional error, and the complete labelled joint
grafting/conditional-independence claims in I1–I3 and II1–II2 remain
separate from the height/profile mean laws. I5's zero residual limits,
I6/I7's bounded-error statements, and E1/E2/E4 remain in scope. The
polynomial-suffix witness route does not delete these obligations.

### Full floor-indexed continuation checkpoint (2026-11-01)

The proposed full-sequence extension receives interface-level **PASS**.
The paper's prefix is now defined exactly as
$m_n=\lfloor(n:\mathbb R)^{1/9}\rfloor$, with a real exponent. Read the
complete actual `PaperPrefixSize.lean` and
`RRTSplitResidualPolynomial.lean` bodies: mathematical/statement **PASS**.
The former proves, including $n=0$,

$$
m_n^9\leq n<(m_n+1)^9,
\qquad m_n\longrightarrow\infty,
$$

and $n\leq m_n^{18}$ whenever $m_n\geq2$. The proof first uses
nonnegative-real ninth powers and only then casts the inequalities to
naturals. The upper comparison follows from $m_n+1\leq m_n^2$ on that
explicit domain.

The residual extension derives $m^8\leq\lfloor n/2\rfloor$ directly from
$2m^8\leq m^9\leq n$ for $m\geq2$. It repeats the checked logarithm
comparison and uses the same actual uniform residual constant, without
assuming monotonicity of the regularized lower center. It therefore covers
every pair $m\geq2$, $n\geq m^9$, rather than only exact ninth powers.

These interfaces suffice for the proposed exact I9 target: compose the
depth-gap-minus-loglog divergence at exponent 18 with $m_n\to\infty$, bound
the actual suffix's loglog term by the one at $m_n^{18}$, and use the uniform
residual bound. The same full-sequence attach-then-freeze gap follows from
the verified affine comparison. The latter would prove II5's final limit;
its explicit conditional case-(c) assertion remains distinct unless an
actual conditional/branch formulation is also exported. Compilation and
the subsequent full limit implementation are not certified by this
interface checkpoint. The reviewer ran no Lean/Lake.

Read the complete subsequent `FloorDeletionGaps.lean` body: **PASS**. The
suffix remains the full natural index $n$ throughout; only the prefix is
$m_n$. The loglog monotonicity comparison has the correct sign for the
negative error term, and the factor four matches the earlier coefficient
eight before division by two. `freezeAttachExpectedGap_floor_tendsto`
is the exact I9 conclusion after unfolding its actual word-gap definition.
`attachFreezeExpectedGap_floor_tendsto` proves the corresponding final
full-sequence limit for item (ii), using the same $(m_n,n)$ and the actual
affine bound. These source-body checks do not replace the new files'
compiler and axiom evidence.

Separately, the Introduction milestone now has current reported mechanical
evidence: the coordinator reports a clean **4110-job full build**. The
reviewer read
`/private/tmp/freezing-growth-introduction-2026-11-01-axioms.log`, whose
header reports **3381 FreezingGrowth declarations** with only the three
permitted transitive axioms. Explicit queries include both new main claims,
`Paper.proposition_1_1_i`, `Paper.proposition_1_1_ii`, and the combined
`Paper.proposition_1_1`. Read the actual numbered exports and confirmed
they retain the exact unchanged Claim types. This supports the earlier
M1i/M1f/M1ii completion recommendation and the 47/10/25/3 count. The new
floor-indexed extension is outside that earlier milestone closure.

The proposed stronger residual-decay interface also receives mathematical
**PASS**: for every $\varepsilon>0$, eventually in $m$, uniformly for all
$n\geq m^9$, the actual residual is at most $\varepsilon$. With
$T=2e\log(m+1)$, the finite-threshold bound has upper term at most
$2\exp(e\log2)\exp((1-e)\log(m+1))$. The lower term is bounded by

$$
2e(\log m+\log2)
\exp\bigl(\alpha(B+2e\log2-(6e-16)\log m)\bigr).
$$

Here $6e-16>0$ follows from $e>8/3$, and both envelopes tend to zero for
the actual fixed seed rate $\alpha>0$. Their independence from the suffix
index justifies the stated uniform quantifier order. The finite-threshold
argument must retain $T\geq0$ and the strict lower-tail event. This would
prove decay of the common residual; I5's two source-specific remainders
and displayed stochastic inequalities remain separate until their actual
observables/laws are connected. No specified sharp E2 rate is inferred.

Read the complete subsequent `RRTResidualDecayAsymptotics.lean` and
`RRTSplitResidualDecay.lean` bodies: mathematical/statement **PASS**. The
finite support bound uses the strict upper event and $T\geq0$ correctly;
the split maximum's strict lower event is exactly the product rectangle.
The larger-component comparison and its averaging retain $n=0$. All
envelope inequalities have the required direction, and the final uniform
decay theorem obtains its positive rate from the actual proved RRT seed.
The generic scalar limits accept arbitrary constant offsets and use only
the explicit positive rates. No sharp rate or source estimate is assumed.

The reviewer also checked the new negative-sign AF floor-limit wrapper:
its observable is exactly the manuscript's long-word mean minus baseline,
and its target is `atBot`. The coordinator reports the full floor milestone
build clean at **4113 jobs**. Read the corresponding log
`/private/tmp/freezing-growth-floor-gaps-2026-11-01-axioms.log`, whose header
reports **3395 declarations** and only the permitted three axioms. This
supports I9 complete and II5 partial, with its final full-sequence limit
proved and conditional case-(c) assertion retained: **48 complete,
11 partial, 23 pending, 3 open questions**. Residual-decay files are outside
that earlier integration milestone until separately checked.

### Actual height-coupling and freezing-case interface checkpoint

The proposed canonical source height coupling receives **PASS**. Its old
law is the actual RRT state followed by the uniform ordered-distinct pair
kernel, mapped to the two depths and full maximum $(a,b,M)$. For $m\geq1$
that kernel is a probability law; its $M$ marginal must be shown to be the
actual old RRT height law. Taking its product with the actual split height
law preserves the dependence between $(a,b,M)$ and supplies precisely the
independent continuation heights $(X,Y)$. The source-oriented formulas are

$$
H_{\mathrm{base}}=\max(M,a+X,b+Y),
\qquad H_{\mathrm{FA}}=\max(M,a+1+X,a+Y).
$$

When the existing seeded-growth law lists the child second, its component
swap must be explicit in the FA marginal proof. The ordered-pair symmetry
justifies the uniform surviving-root average. Once both actual word-height
marginals and the exact source formulas are proved, this is a joint
**height** coupling sufficient for I3. Defining the source $Z,\hat Z$ and
proving their pointwise maximum decompositions then suffices for I4.
Neither completion logically requires certifying the stronger labelled
tree grafting construction in I2, which remains separate. This conclusion
is a semantic interface assessment, not a declaration that those new
proofs have been implemented.

For I5, domination by the common residual supplies the two expectation
limits after their actual observables are connected. Its displayed
stochastic bounds additionally require the indicator comparison against
$M\geq H_{\lfloor n/2\rfloor}$, including equality; the strict lower-tail
estimate alone should not be silently substituted for that assertion.

The proposed label-aware `ForwardTwoSeedCases` interface also receives
**PASS**. At a valid state with active IDs $\{u,v\}$ and $u\ne v$, the
fresh ID $n+1$ is distinct from both. After fixing the parent $u$, the
three possible frozen IDs are distinct even if the old depths coincide.
The joint tag/profile law has three Dirac branches of weight $1/3$, with
the common retained maximum $\max(M,a+1)$, including the frozen-child
case. The catch-all tag only needs to identify $v$ on the actual sampling
support. This proves a fixed-state conditional law and a uniform tag
marginal; it does not assert unproved global conditional independence.
No Lean/Lake was run by the reviewer.

### Joint law bodies and fixed-height threshold checkpoint (2026-11-01)

Read `SeedDepthMaximum.lean`, `TwoSeedHeightModel.lean`,
`ForwardTwoSeedCases.lean`, and `RRTBoundedHeight.lean` in full:
mathematical/statement **PASS**. The depth/maximum law samples actual
ordered-distinct vertex IDs before forgetting labels. It proves its
probability normalization for $m\geq1$, actual support
$\max(a,b)\leq M\leq m$, integrability of every real test from finite
support, the actual two-survivor profile marginal, and the old RRT height
marginal. The product model preserves this dependence and has the expected
depth-swap invariance. Its `longHeight` definition is explicitly child-first,
matching the source orientation. These files do not yet supply the later
word-height marginal proofs by their definitions alone.

The label-aware freezing file derives fresh-ID distinctness from valid
vertex support, computes the three actual post-freeze profiles, and proves
the joint tag/profile law and uniform tag marginal. Equal depths cause no
collapse of the three vertex choices, and the child maximum remains after
freezing the child. This supplies exact fixed-state conditional information;
full independence from later grafting variables is not asserted by that
file alone.

The fixed-height CDF theorem concerns the actual RRT law and states that for
each fixed natural $h$ and every $\sigma>0$, some $D\geq0$ satisfies
$\mathbb P(H_n\leq h)\leq D\sigma^n$ for all $n\geq0$. The double induction
has no hidden height estimate: the height induction uses rate $\sigma/2$,
the strong size induction bounds the same-height smaller tree, and the
reflected geometric sum is at most two. The cutoff makes
$2C/(n+1)\leq\sigma$, and the finite sum of reciprocal powers covers all
smaller sizes. The zero-height and zero-edge boundaries are retained.

Compared the proposed Q2a interface directly with `main.tex` lines 957–960.
It faithfully quantifies over arbitrary real threshold sequences $h(n)$
and all real stochastic-domination test thresholds, with no extra eventual
lower bound on $h$. Restricting the domination hypothesis to $n\geq1$
proves a slightly stronger sufficient statement for the asserted asymptotic.
For each natural $K\geq1$, if $h(n)\leq K$, testing at $K+1$ against the
alternating word forces

$$
\mathbb P(H^{\mathrm{RRT}}_n\leq K)
\geq \mathbb P(H^{\mathrm{alt}}_n\leq K)
\geq2^{1-n}.
$$

The proved fixed-height CDF estimate at $\sigma=1/4$ eventually contradicts
this inequality. Cofinality of the natural $K$ then proves $h(n)\to\infty$.
This is an interface/proof-route PASS for Q2a, not a claim that the open
optimization question Q2 is solved or that its final wrapper has yet been
checked.

The proposed `TwoSeedRemainders` stochastic interfaces also receive **PASS**.
For $0\leq r<m$, a positive remainder above $r$ implies split maximum
strictly below $M$. The larger-component strict CDF comparison then bounds
this by $\mathbb P(H_{\lfloor n/2\rfloor}<M)$, and hence by the required
non-strict comparison $\mathbb P(H_{\lfloor n/2\rfloor}\leq M)$. For $r<0$
both nonnegative-variable upper tails equal one; for $r\geq m$, actual
support makes the remainder upper tail zero. The actual old-maximum
marginal and product transport must remain explicit. Domination by the
common residual then supplies both expectation limits along the full floor
prefix once the actual word-height marginals identify the source coupling.
No Lean/Lake was run by this reviewer, and no new coverage is certified by
an interface check alone.

Read the complete actual `TwoSeedHeightMarginals.lean`,
`TwoSeedRemainders.lean`, and `Question2Threshold.lean` bodies:
mathematical/statement **PASS**. The marginal proof compares every real
test of height, rather than only the expectation. The child-first FA
orientation is obtained by commuting the active multiset before applying
the actual seeded maximum-law theorem; the raised maximum is then absorbed
by the nonnegative child-component height. This is a valid explicit
orientation proof even though it does not separately invoke a split-map
swap. The actual depth-law swap turns the two possible surviving-root
terms into equal integrals. Both actual finite-word height marginals are
therefore realized on the same declared model law, as required for I3.

The two remainder definitions match the source signs and component
orientation exactly. Their common-residual mean is identified through the
actual old-maximum/split pushforward, and the full floor-indexed limits
follow from the uniform residual decay by a nonnegative squeeze. The
stochastic inequalities are stated for every real strict upper-tail test
against the independent actual pair law with observable
$m\mathbf 1_{\{H_{\lfloor n/2\rfloor}\leq M\}}$. Their proof handles
negative, intermediate, and high thresholds separately and includes the
source comparison's equality case. This is the full pair of displayed
stochastic bounds, not merely a mean bound or a strict-event replacement.

After clean integration/build/axiom evidence, these files support I3 and
I5 **complete**. I4 still requires its explicit source maximum
decompositions. I2's stronger full labelled graft construction remains
separate; the actual joint height law is already sufficient for the
height-level conclusions just reviewed.

The Q2a wrapper retains arbitrary real $h$, every real tail test, and every
admissible word of the specified size. Its eventual fixed-CDF-versus-star
comparison is valid at rate $1/4$; taking complements at threshold $K+1$
has the correct inequality direction. Natural ceilings supply cofinal
bounds for every real target, proving the exact real-valued `Tendsto`.
After clean proof evidence, Q2a may be marked **complete**. This proves
only the asserted necessary divergence and does not solve Q2's open
optimization/existence question. The reviewer ran no Lean/Lake.

Read `TwoSeedHeightDecomposition.lean` in full: mathematical/statement
**PASS**. Its imbalance is $\Delta=Y-X$. The two displayed identities are
exactly

$$
H_{\mathrm{FA}}=X+a+\max(1,\Delta)+Z_+,
\qquad
H_{\mathrm{base}}=X+a+\max(0,b-a+\Delta)+\hat Z_+.
$$

Both hold pointwise on the same model sample, and the module imports the
actual height marginals and source remainders. Thus the missing I4
identities are now represented by actual bodies, rather than only generic
scalar algebra. Subject to fresh clean integration/build/axiom evidence,
I3/I4/I5/Q2a may all be marked complete. From 48 complete, 11 partial,
23 pending, and 3 questions, these four upgrades alone give **52 complete,
9 partial, 21 pending, and 3 questions**.

For the integrated label-aware three-case kernel, the recommended scoped
classifications are **II1 partial** and **II2 partial**. II1 now has the
exact tagged post-freeze profiles, including the retained frozen-child
maximum; its full labelled graft coupling remains open. II2 now has the
actual conditional uniform $1/3$ tag law at each valid original state and
fixed parent; the explicit global independence from the other source
coupling variables remains to be exported. These two pending-to-partial
refinements would yield **52 complete, 11 partial, 19 pending, and
3 questions**. The local kernel by itself does not justify marking either
row complete. This is a coverage recommendation pending mechanical
evidence, not an independent report mutation or whole-paper claim.

### Remaining first-order and global tag interfaces (2026-11-01)

Compared the proposed `RRTFirstOrder` target with `main.tex` lines 329–339:
interface/source **PASS**. The exact actual-law statement is that for every
$\varepsilon>0$,

$$
\mathbb P\left(\varepsilon\leq
 \left|H_n/\log n-e\right|\right)\longrightarrow0.
$$

The totalized values at $n=0,1$ affect only finitely many initial terms.
Eventually $\log n>0$, so the actual rough absolute-deviation estimate can
be divided by $\log n$, adding the bounded center shift $e\log2$. Read the
initial analytic prelude: its regularized-loglog comparison and limit are
correct. For $\log n\geq1$,
$\log(1+\log(n+1))\leq\log3+\log\log n$, and division by $\log n$
tends to zero. Actual finite-law Markov then gives the desired non-strict
deviation event. A normalized mean-height limit would follow from the same
$L^1$ estimate. This is first-order O5 information; E1's second-order
expansion remains separate, and the final probabilistic body has not yet
been read at this checkpoint.

The proposed `TaggedTwoSeedHeightModel` interfaces receive **PASS**. The
carrier retains $(a,b,M)$, a uniform tag in three cases, and the fresh
actual split pair. The three branch heights are respectively
$\max(M,a+1,a+X,b+Y)$,
$\max(M,a+1,a+1+X,b+Y)$, and
$\max(M,a+1+X,a+Y)$, which preserve the source's three frozen-ID meanings.
An explicit tag/data product-law identity proves independence from both
the old depth/maximum data and the fresh split. Restricting to a tag must
give $1/3$ times its normalized branch height law; the case-(c) normalized
law should be the actual freeze-then-attach word law.

The connection to the actual labelled fixed-state freeze kernel is
essential in addition to the untagged AF word marginal: the tags must
represent the source's freezing choices. Once that connection, the product
independence, and the normalized branch identity are proved, II2 and II5's
conditional case-(c) assertion can be discharged on the actual height
coupling. This does not require or certify the stronger complete labelled
graft construction in II1. No new coverage is advanced by these interface
checks; no Lean/Lake was run by the reviewer.

Read the completed `RRTFirstOrder.lean` body: mathematical/statement
**PASS**. The actual normalized absolute-mean estimate explicitly uses
$n\geq2$ when dividing by $\log n$; all later limits correctly ignore the
finite initial exceptions. The finite-law Markov proof retains the
non-strict event $\varepsilon\leq|H_n/\log n-e|$, and the normalized mean
limit follows from the actual integral identity and the absolute-integral
inequality. Subject to clean proof evidence, this completes the missing
RRT half of O5; its already-proved alternating half is unchanged. It does
not establish E1's finer centering or bounded errors.

Read the completed `TaggedTwoSeedHeightModel.lean` body:
mathematical/statement **PASS**. `actual_tagged_profile_kernel` identifies
the model tag with the true vertex-ID freezing kernel before depth
averaging. Each `caseProfile` is connected to actual subsequent seeded
growth. The tagged AF height marginal is proved for every real height
test using the exact six-row word law and the actual old-depth swap.
The tag/data product identity is an explicit coordinate permutation of
the product measure, so it proves uniform tags independent of the entire
retained old-depth/maximum and split-height data. The branch restriction
has exactly mass $1/3$, with its normalized law given by `caseHeightLaw`.
`caseHeightLaw_two` is exactly the actual FA word-height law, not an
assumed surrogate law.

These statements supply II2's needed independence on the actual height
coupling. The full labelled graft geometry in II1/I2 remains separate.
To complete II5, the conditional case-(c) mean-minus-baseline limit should
still be exported from the normalized branch identity and the existing
full-floor FA gap theorem; its final AF limit alone was previously
recorded as partial. Equal-depth multiplicities and the frozen-child
maximum are retained throughout. No compiler was run by this reviewer.

### Boosted lower-tail rate and L1 interface checkpoint (2026-11-01)

The proposed seed-boosting route receives mathematical **PASS**. Given
the actual constant-success seed at any $c\geq0$, choose a finite grid index
$j$ so that $(1-p)(1-p/2)^j\leq1/4$. The existing all-size amplification
then gives success probability $3/4$ at the shifted offset
$A'=A+j e\log4\geq0$. Its new geometric factor is $5/8$, and

$$
(5/8)^3=125/512\leq1/4,
\qquad
\frac{-\log(5/8)}{e\log4}\geq\frac1{3e}.
$$

The real-threshold exponential theorem therefore yields a positive constant
$C$ with
$\mathbb P(H_n<b_c(n)-x)\leq C\exp(-x/(3e))$ for every $n$ and $x\geq0$.
The factor $C$ absorbs the finite shifted offset. The $p=1$ boundary causes
no difficulty. This rate is centered at the regularized lower center,
**not** at the actual mean, so it does not prove E2's two-sided centered
bound.

For L1, the proposed cutoff $(e/2)\log n$ gives a lower-half tail of order
$n^{-1/6}$ times a fixed logarithmic power, eventually bounded by a constant
times $n^{-1/8}$. The small-tree upper tail decays faster. The non-strict
event $H\leq T$ must be connected explicitly to the strict lower-tail API,
for example by using $T+1$. The existing first-order mean limit supplies
the two eventual mean comparisons needed for LP1's centered event
inclusions without assuming E1. The second source inclusion must keep the
same random-tree copy on both sides, as already recorded in SF5 at source
line 461; the literal printed copy switch is not certified. These are
interface/proof-route checks only, with all existing sharp obligations
retained and no Lean/Lake run by the reviewer.

Read the actual `TaggedCaseLimits.lean` body: **PASS**. The normalized
case-(c) height law is the actual FA word law, so its mean minus the
baseline mean is exactly the negative FA gap. The full floor-indexed
limit targets `atBot` and uses $m_n\geq1$ only eventually. Together with
the already-reviewed branch restriction of mass $1/3$ and actual
vertex-tag identification, this supplies the formerly missing conditional
case-(c) assertion in II5. The other parts of that row, the final AF limit
and the main existential claim, were already proved. A complete II5
classification is therefore supported after fresh clean proof evidence.

The proposed `TaggedCaseBounds` interfaces receive **PASS**. In case (a),
if the first split-component height $X\geq1$, the baseline already includes
$a+X\geq a+1$, so the retained frozen child cannot raise the maximum.
Otherwise the increase is at most one. The exact probability
$\mathbb P(X=0)=1/(n+1)$ therefore supplies the source's sharper
conditional-mean error. In case (b), the branch height lies pointwise
between the baseline and baseline plus one, giving the absolute-difference
bound as well as its conditional expectation consequence.

The proposed explicit size-tag bridge is important and correct: under the
actual tagged split mixture, a nonzero first-component size gives positive
component height almost surely, and the actual first-edge split joint law
transports that statement to the source RRT. The parent RRT has $n+1$
edges and its two components have total $n$ edges. Thus the source
$I_n\ne0$ condition is retained, rather than replaced by an unrelated
height event. The domains $m\geq1$ and every $n\geq0$ are consistent. This
last paragraph is an interface checkpoint awaiting the new actual body;
it does not certify the full labelled graft-tree coupling.

Read the complete actual `TaggedCaseBounds.lean` body:
mathematical/statement **PASS**. Its deterministic bounds in fact hold for
every natural-valued model sample; a separate $a\leq M$ premise is not
needed because the baseline already covers $a+X$. This is a valid stronger
helper, with no weakening of the source statements.

The positive-height bridge is proved under the actual `componentLaw`,
summed to `mixtureLaw`, and transported to `firstEdgeSplit` of the genuine
$(n+1)$-edge RRT. The nonzero size condition is explicitly retained. The
exact first-component zero-height probability is $1/(n+1)$, including
$n=0$. Integrating the case-(a) indicator bound under the true height model
gives its precise conditional-mean error. The case-(b) height is between
baseline and baseline plus one pointwise, proving both its absolute
difference and mean bound.

After clean build/axiom evidence for this file and the tagged model, II3
and II4 may be marked **complete**. The actual tagged model and
`TaggedCaseLimits` additionally supply II2 and II5 at the source's height
coupling level. The full labelled grafting assertion II1 remains partial.
No compiler was run by the reviewer and no report row was mutated here.

### Critical seed, paper-rate bounds, and exploratory E1 route (2026-11-01)

Read the actual `RRTLowerTailPaperRate.lean`,
`RRTCriticalLowerSeed.lean`, `PaperMeanThresholds.lean`, and
`PaperHeightComparison.lean` bodies: mathematical/statement **PASS**.
The finite grid boost preserves the all-size seed, and the positive tail
constant precedes every size and deviation quantifier. The fixed-rate
exponent comparison uses $x\geq0$ in the correct direction. The critical
seed transfer accounts for both ceiling and logarithm losses: writing
$\ell=\log(n+1)$ and $g=\log(1+\ell)$, for
$d=\lceil e\ell-(3/2)g-A\rceil$ one has eventually

$$
t_d\leq\ell+\frac{5/2-A}{e}.
$$

Taking $A=\max(1,5/2+e(K-\log(p/2)))$ permits the same actual geometric-index
transfer with loss $p/2$. The arbitrary-offset finite-prefix extension
then yields the unconditional critical seed and bounded lower deficit.
No critical clock estimate beyond the already-proved clock seed is
assumed, and the earlier coefficient-two exports are unchanged.

The L1 implementation uses a stronger simplification than the initial
logarithmic-power plan. Eventually,

$$
\frac e2\log n+1
\leq b_2(\lfloor n/2\rfloor)-\frac{3e}{8}\log n.
$$

The boosted rate therefore gives exactly $n^{-1/8}$ after the explicit
non-strict-to-strict threshold shift. The small-tree upper event is bounded
using the cutoff minus one. The actual independent comparison-law union
bound and the final real-power expression are correct. The source mean
margins and both centered inclusions are also proved for the same height
sample, preserving the SF5 correction. After clean evidence, L1 and LP1
may be complete; the eventual common $c_1$ with part L2 must still be
reconciled by enlargement when L2 is established. None of these statements
proves mean-centered E2 or the full E1 expansion.

The exploratory `E1_ROADMAP.md` has been independently audited at the
mathematical level. Verdict: **conditional route PASS after the stated
correction and explicit domain/normalization lemmas**, not proof evidence
or source-coverage credit. The actionable correction is to retain the
first-half crossing bound with polynomial factor $(1+x)^P$; using only
the displayed unified factor $(1+x+\log(q+1))^P$ would leave a spurious
unbounded $\log d$ factor for small $j$. The second-half allowance may
include $c\log(q+1)$. The coordinator reports that this piecewise correction
has been made.

The cyclic occupancy normalization is

$$
\mathbb P(\text{soft leading})
\leq\frac1n+
\sum_{k=1}^{n-1}\mathbb P(\text{leading},\ 0\leq Y_k\leq L_k).
$$

The leading indicator must remain. Rotating to the unique minimum supplies
a factor $n$ that cancels the initial rotation average. Equivalently,
use the rotation-invariant good-rotation count as the weight in the
cyclic-minimum identity. A good rotation at $r$, evaluated at the inverse
index $-r$, gives $b_r-b_0\leq w_{-r}=w_r$. The nearby-position count itself
need not be rotation-invariant. Cancellation requires $n>0$; finite counts
give integrability, while actual simplex rotation invariance and no ties
must still be instantiated.

The positive-total-band alternative to an explicit beta density also
passes. On total $T\in[n,n+1]$ and prefix surplus $0\leq y\leq L\leq q/2$,
the two raw Gamma totals satisfy
$Z_1\in[k,k+L+1]$ and
$Z_2\in[n-Z_1,n+1-Z_1]$. The two canonical internal bridge allowances
are at most $L$ and $2L$. Their angular laws are independent of the totals;
the full angular event is independent of $T$. The Gamma density upper
bounds and positive total-band mass therefore yield the degree-13
occupancy estimate without conditioning on an endpoint singleton.

Read the actual `PWIT/GammaBridgeBounds.lean` body: **PASS**. For every
integer shape $n\geq1$ it gives global density at most $2/\sqrt n$ and
mass at least $e^{-3}/\sqrt n$ on $[n,n+1]$. Shape one and negative inputs
are included. The lower bound uses the nonnegative logarithmic ratio on
the unit band and the proved factorial-density estimate; no finite-size
enumeration is needed.

In the exceptional occupancy regime $q<2L$, the inequality forces
$q\leq\operatorname{poly}(1+A+c)$. When $k\geq n/2$, retaining just the
first block's near-leading factor gives the required polynomial divided
by $n$ after summing those positions. When $k<n/2$, the whole dimension
is polynomially bounded and the trivial probability bound suffices.
The resulting fixed degree $P$ may be enlarged; the exact value is not
yet a proved export.

For the first-crossing route, integrate endpoint densities over
$[0,b_j]$, obtaining the exponential endpoint factor with a constant
$1/e$, rather than treating the set as a width-one window. Generic
factorial shifts apply for $j>2P$; taking
$A_0>2P\cdot5/(2e)$ makes every smaller crossing barrier negative.
The root barrier is negative as well. The first-half and second-half
depth sums are then uniformly summable with their separate polynomial
factors. The return to RRT size additionally needs an explicit lower bound
$\log d\geq\log(1+\log(n+1))-C$, which follows eventually from
$d\geq(e-3/2)\log(n+1)$ at the critical upper index. This makes the clock
deviation at least the height deviation minus a constant. These remain
new substantial bridge/barrier/count obligations, and E1/E2 are not
certified by this roadmap assessment.

The proposed full-labelled I1 interface also receives **PASS**.
`TreeSkeleton` retains vertices, graph, parent map, and heights, while
`TreePairSample` retains the actual ordered survivor IDs. Forgetting
freeze timestamps is faithful to I1. The exact bind kernel represents
conditional uniformity given the old tree, without claiming independence
from the tree. Skeleton invariance under freezing permits the arbitrary
labelled-pair averaging proof. Include the prefix's two-active cardinality
and the original RRT's active-equals-vertices support, then the proposed
law equality would prove the full I1 assertion. Discrete measurability
is legitimate on these possibly uncountable carriers; finite-horizon
support, not unproved countability, must justify real-test integrability.
The actual I1 implementation has not yet been reviewed at this checkpoint.

Read the subsequent actual `PWIT/CyclicBarrier.lean` body:
mathematical/statement **PASS**. The composition order of finite rotations
is correct, and finite reindexing proves good-count invariance. Evaluating
a good rotation at the inverse index gives the count-to-near-count
inequality even without a minimum premise; the probabilistic theorem
still correctly retains its minimum-at-zero indicator. It proves
$\mathbb E[\mathrm{count}]=d\mathbb P(\mathrm{soft})$, applies the weighted
cyclic-minimum identity, and cancels only under the explicit `NeZero d`
hypothesis. Integrability is supplied by finite indicator sums.

The generic theorem retains symmetry of the allowance, true
measure-preserving sample rotations, bridge covariance, and almost-sure
no ties as hypotheses. It does not silently instantiate these for a fixed
labelled PWIT path or assert the new actual simplex occupancy estimate.
No compiler was run by this reviewer; the exploratory E1/E2 work receives
no paper-coverage credit from this generic lemma alone.

Read the complete actual `ForwardPairSkeleton.lean` and
`TwoSurvivorTreeLaw.lean` bodies: mathematical/statement **PASS**. The
projection retains the actual labelled vertex set, graph, parent map,
height map, and ordered survivor IDs. Only changing active/frozen status
and timestamps are omitted. Freeze invariance of this skeleton is exact.
Arbitrary real labelled-pair tests are integrable by explicitly finite
reachable support; no countability of the skeleton carrier is assumed.

The erase-average identity is applied only with at least three active
vertices, stopping at exactly two. The final equality of measures compares
the actual prefix's complete tree-and-survivor law with the original
$m$-edge RRT and its conditional uniform ordered-distinct pair. The final
vertices-kernel export explicitly uses the original RRT's
active-equals-vertices support. Together with the existing exact
two-active-prefix cardinality, this is sufficient for **I1 complete**
after clean build/axiom evidence. It preserves the dependence of the
pair on the same sampled tree and makes no false independence claim.
The reviewer ran no Lean/Lake.

### Integrated cases milestone and next actual simplex bridge (2026-11-01)

The inventory arithmetic was checked independently. Starting at
52 complete, 11 partial, 19 pending, and 3 questions, completing
I1/O5/II2/II3/II4/II5/L1/LP1 removes four partial and four pending rows.
Recording E1 as partial for its actual critical lower seed/deficit adds
one partial and removes one pending row. The result is **60 complete,
8 partial, 14 pending, and 3 questions**, still 85 IDs. E1 partial is
honest only with its one-sided scope explicit: critical upper control,
two-sided tightness, and bounded mean error remain unresolved. E2 and L2
remain unresolved, including eventual reconciliation of the common L1/L2
constant.

The coordinator reports a clean **4135-job full build**. The reviewer read
`/private/tmp/freezing-growth-cases-comparison-2026-11-01-axioms.log`, whose
header reports **3690 declarations** with only the permitted three
transitive axioms. This supports the integrated cases/comparison
milestone; it is not evidence for newer files outside that import closure
or for a fresh publication/independent-kernel validation.

Read the actual `PWIT/SimplexTwoBlockBand.lean` foundation and
`PWIT/SimplexCyclicBarrier.lean` bodies: mathematical/statement **PASS**.
The two-block reconstruction is the actual iid clock law, its normalized
global vector has the actual simplex/Gamma product law, and regrouping
retains independence of both internal angles from both totals. The
slanted band has first-coordinate width $L+1$ and second-coordinate slice
width one, giving exactly $4(L+1)/(\sqrt k\sqrt q)$ for positive $k,q$.
The all-real Gamma interval bound permits slices crossing zero.

The actual simplex rotation theorem transports raw iid-clock coordinate
invariance through normalization. No ties transfer by the positive inverse
total and then by the nonzero dimension scalar. The simplex law is
singular on its ambient space; no ambient absolute-continuity assertion
is used. All generic occupancy hypotheses are discharged on the actual
canonical simplex bridge with positive dimension. Quantitative occupancy
and logarithmic-barrier estimates remain separate and uncredited.

The proposed reverse distinguished-initialization interfaces were compared
with source lines 732–755: **PASS with the explicit guards stated here**.
Insertion needs a fresh distinguished label, and the original root count
must be at least one before choosing a distinct pair from the enlarged
forest. Reordering by swapping the distinguished receiver with its donor
must be guarded by valid root-pair membership; otherwise a nonroot label
could violate the ordered-forest invariant. In the receiver case, swapping
the two labels in the order and then deleting the donor places the retained
distinguished root in the donor's former slot, exactly as printed. The
child case removes the initial root-order entry; avoidance retains it.

When used, the distinguished **singleton component** disappears; its
vertex remains in the graph. The stored delayed pair must retain the
original natural positions $0,\ldots,N$. In the unused branch those
positions are $1,\ldots,N$, and later short-forest interpretation subtracts
one rather than reusing post-merge long-forest positions. This checkpoint
concerns initialization/local update laws only; it does not certify C4/C5
or the delayed-history conditional-independence argument under SF6. No
compiler was run by the reviewer.

### Reverse initialization and quantitative simplex helpers (2026-11-01)

Read the complete actual `ReverseDistinguishedInitialization.lean` body:
mathematical/statement **PASS**. The guarded root-position swap changes
only the stored order, and its subsequent join projects to the ordinary
actual graph join even in totalized invalid cases. Under a valid pair,
the singleton-root characterization distinguishes avoidance, distinguished
receiver, and distinguished child correctly. With the distinguished root
at the head, the three explicit list formulas match the source operation.
The receiver case retains that root in the donor's former slot; the child
case removes its root status without removing its graph vertex.

The initialization samples the genuine uniform ordered-distinct original
positions in the enlarged list. Its delayed pair stores those original
natural positions, and its flag records whether position zero was used.
Freshness and a nonempty original root set are explicit where needed for
probability and validity. The actual graph marginal equals fresh insertion
followed by the ordinary join law. This is a valid generic initialization
implementation, not yet the source's common-tail almost-sure validity
wrapper or the later delayed-history induction. C4/C5 remain separate.

Read the actual `PWIT/LogBarrierGeometry.lean` and
`PWIT/LogBarrierBounds.lean` bodies: mathematical/statement **PASS**.
The logarithmic chord inequality includes both endpoints. The bridge
comparison uses the two halves of the prefix interval correctly, and the
integer minimum-window product comparison has the required domains
$i\leq j\leq d$. The coarse time-center bound also handles zero through
the existing totalized definition. These are deterministic estimates,
without a first-crossing probability assertion.

The exceptional-window estimate is valid for $c,q\geq0$:

$$
q\leq 2(A+c\log(q+1))
\quad\Longrightarrow\quad
q\leq4A+16c^2+1.
$$

The further bound by $21(1+A+c)^2$ correctly adds $A\geq0$.
The finite cyclic allowance uses $\min(r,d-r)$, with the zero index
handled separately in its negation symmetry proof. Its short-suffix
corollary replaces the minimum by the actual suffix length in the correct
direction. No hidden large-dimension premise is introduced.

Read the complete actual `PWIT/SimplexTwoBlockOccupancy.lean` body:
mathematical/statement **PASS**. With $k,q>0$, $0\leq y\leq L$, and
$2L\leq q$, the first and second normalized internal bridges have
allowances $L$ and $2L$. In particular, $q-y\geq q/2>0$ justifies the
second normalization. The total-band event has first-total interval
$[k,k+L+1]$ and total interval $[k+q,k+q+1]$, as required.

The actual product-law argument preserves the joint leading-occupancy
probability multiplied by the independent positive Gamma total-band
mass before dividing. It never conditions on an endpoint singleton.
Combining the two internal ballot factors with the band estimate and
its positive denominator yields the stated constant
$256C_{\mathrm{ballot}}^2/\exp(-3)$ and the bound

$$
C(1+L)^{13}\frac{\sqrt{k+q}}{(k\sqrt{k})(q\sqrt{q})}.
$$

This controls the probability of leading **and** the specified occupancy,
not the probability conditional on being leading. The distinction is
essential for the later cyclic normalization.

Read the complete actual `PWIT/SimplexTwoBlockPrefix.lean` body:
mathematical/statement **PASS**. Retaining only the first internal bridge
requires no condition relating $q$ and $L$. The first scale $k+y$ is
positive, and $y/(k+y)\leq L/k$ follows from $0\leq y\leq L$.
Actual almost-sure positive total and sum-one angular support justify
the normalized reconstruction. The actual first-angle marginal then
gives the bound $C_{\mathrm{ballot}}(1+L^6)/k$. The preceding event
inequality for arbitrary real $L$ is also valid; occupancy is empty when
$L<0$. This supplies the exceptional-suffix helper without Gamma-band
division.

The source inventory and manuscript hash remain unchanged. These are
independent mathematical/body reviews only; no Lean/Lake command was
run by this reviewer, and the new barrier work does not complete E1/E2.

### Early F2 policy and general polynomial-density checkpoints (2026-11-01)

The proposed full labelled-forest order-invariance interface receives
**PASS**, including deterministic join-order policies that depend on the
freshly selected pair, the current complete ordered forest, and time.
Pointwise certificates must preserve the entire actual underlying rooted
forest, while pair sampling remains the genuine uniform ordered-distinct
root kernel. Initial and insertion policies have analogous exact
projection certificates. The fallback below two roots must remain
order-only, and the existing hold after the horizon must be preserved.
Kernel projection and bind induction then give the same full labelled
forest law at every phase, including extinction. Permutations, front
insertion, and the distinguished-receiver relocation are concrete
instances. These certificates constrain deterministic order changes;
they are not missing stochastic estimates. This target covers F2, not
the C4/C5 history or delayed-pair independence argument. Its implementation
has not yet been reviewed here.

The proposed `PWIT/PolynomialBallotDensity.lean` interface also receives
**PASS**. For natural $P$, $n\geq2(P+1)$, and $A,s\geq0$, the shifted
mode $n-P-1$ is at least $n/2\geq1$, and each of the $P$ factorial-ratio
factors is at least $n/2$. Thus the stated coefficient
$2^P\sqrt2\exp(P+1)$ controls both the shifted and ordinary intensity
terms. The case $P=0$ correctly doubles the ordinary term, and at $s=0$
both polynomial powers have positive exponents. The equivalent quotient
formula must retain $s>0$, as proposed. This is an analytic helper
checkpoint, not a proof or coverage claim for the logarithmic barrier.

Read the subsequent complete `ReverseOrderInvariance.lean` body:
mathematical/statement **PASS**. The stronger pair-dependent policy is
implemented with exact whole-forest projection certificates. The genuine
uniform-root-pair kernel, identity fallback below two roots, and hold
after the horizon are explicit. Kernel projection and bind induction
prove `map_lawAfterWithOrdering` for every sequence and all horizons and
phases. `treeLaw_order_independent` therefore proves the full labelled
terminal-forest order invariance, including the source tree case.
Permutation, front insertion, and distinguished-join policies are actual
constructors. This supplies **F2 completion once current compilation and
axiom evidence pass**. It does not identify the full Algorithm 3 history
with a policy or prove the delayed second-process marginal.

Read the subsequent complete `PWIT/PolynomialBallotDensity.lean` body:
mathematical/statement **PASS**. Its factorial-product comparison and
half-size estimates discharge the announced coefficient without an
extra analytic assumption. The exponent shift is exactly $P+1$, and
$1+2^P A^P\leq2^P(1+A^P)$ preserves the final bound. The domains and
zero-degree/zero-endpoint cases match the earlier checkpoint. Compiler
evidence remains the coordinator's responsibility; this reviewer ran none.

The sharpened actual simplex soft-barrier target with fixed degree
fourteen receives an early mathematical/statement **PASS**. Put
$M=1+A+c\geq1$. If $d\leq42M^2$, the probability bound by one is
already at most $42M^{14}/d$. Otherwise, each exceptional suffix has
$q\leq21M^2<d/2$, hence prefix length $k>d/2$. Also
$q+1\leq25M^2$ implies $L\leq11M^2$. The one-block probability bound
summed over at most $22M^2$ exceptional positions has degree fourteen.
In the regular regime, split according to which of $k,q$ is smaller:
the larger block contributes at most $4/d$, while the remaining factor
is bounded by the summable positive-index sequence
$(1+\log(k+1))^{13}/k^{3/2}$, with the symmetric variable on the other
half. The cyclic zero index contributes $1/d$. The actual bridge minimum
and prefix-surplus identifications must remain explicit in the assembly.
This target is a new actual-law helper, not completion of E1/E2.

The proposed `ReverseInitializationValidity.lean` source instantiation
receives an early **PASS** against `main.tex` lines 732–755. For an
admissible word consisting of $k\geq1$ attachments, one freeze, and its
tail, the actual forest after reversing exactly the tail is at phase
$k+1$, has $k$ roots, and has not yet acquired the label of that freeze.
The enlarged list therefore has $k+1$ roots. At $k=1$ the distinct pair
necessarily uses position zero, as required. Binding this actual law
with the initialization kernel gives the source's fresh uniform index
choice, sizes, and delayed-position/flag invariants. The shorter field
is the common incoming forest. Identifying its frozen IDs with those of
the shortened word still requires the separate relabelling/common-tail
coupling; this checkpoint does not assume that identification or C4/C5.

The proposed `RRTCriticalUpperTransfer.lean` interface receives an early
**PASS**. Its `CriticalClockUpperBound` remains an explicit unproved
premise until the actual first-crossing estimate supplies it. For
$b(n)=e\log(n+1)-(3/2)\log(1+\log(n+1))$, one has
$b(n)\geq\log(n+1)\geq0$. Choosing

$$
A=\max\bigl(\max(1,d_0),\,1+e(\log2+A_0)\bigr)
$$

ensures that $d=\lceil b(n)+A+x\rceil$ satisfies $d\geq d_0$ and
$d\geq1+\log(n+1)>0$ for every $n\geq0$ and $x\geq0$. Thus the
logarithmic term in the time center cancels the critical regularization
in the correct direction, giving
$t_d\geq\log(n+1)+(A+x)/e$. The actual geometric transfer at
$\log(2(n+1))$ therefore loses only the proved factor two. A non-strict
real height threshold uses the ceiling, exactly as proposed. The
zero-size case, degree zero, and arbitrary real $A_0$ cause no missing
boundary condition. This uniform conditional transfer provides no
independent proof of the clock upper bound or E1/E2 completion.

Read the actual `PWIT/SimplexSoftBallot.lean`,
`PWIT/LogBarrierSeries.lean`, and `PWIT/LogBarrierSummation.lean` bodies,
the additions to `PWIT/LogBarrierBounds.lean`, and the finite-sum
integral expansion in `PWIT/CyclicBarrier.lean`: mathematical/statement
**PASS**. The canonical minimum is exactly the zero-leading event, and
on actual unit-sum simplex support the canonical prefix value is the
two-block surplus. A minimum at zero supplies the otherwise implicit
nonnegative-surplus condition, so the near-position event is the joint
leading-occupancy event, including for negative allowances. Index zero
has probability exactly $1/d$ under its nonnegative allowance.

The integral expansion retains the minimum indicator and produces the
sum of actual event probabilities, with no extra dimension factor.
Logarithmic weights are controlled eventually by a quarter-power and
then by the summable power $5/4$. The positive-index denominator shift
loses only the stated constant four. The totalized zero-index weight is
zero; no division at zero is used for a positive-index estimate. The
finite-sum bound uses a genuinely summable nonnegative series, with an
added one ensuring a positive uniform constant. The new $11M^2$
allowance estimate and multiplicative logarithmic factor bound have
exactly the required nonnegative domains. These actual helpers support
the reviewed degree-fourteen assembly but do not themselves prove its
full probability estimate. No Lean/Lake was run by this reviewer.

Read the complete actual `ReverseInitializationValidity.lean` body:
mathematical/statement **PASS**. The actual tail law is at phase $k+1$,
its root count is exactly $k$, and the freeze label is fresh by the
existing actual `ValidAt` support. Binding its conditional initialization
kernel proves probability under the explicit source assumption $k\geq1$.
The all-$k$ almost-sure validity helper is also sound: at $k=0$ the
distinct-pair initializer has zero mass, and no probability claim is made.

The output invariants retain the two root counts, original pair positions,
their distinctness and positivity when unused, and the exact
singleton-root/flag equivalence. The shorter-field marginal remains the
actual incoming forest law. The separate $k=1$ theorem correctly proves
that the distinguished singleton must be used. Together with the
previously reviewed exact local laws and list formulas, this supports
**C2 completion after current build/axiom evidence**. The common-tail
frozen-label relabelling in C1 and the later C4/C5 history assertions
remain separate, without being silently imported into this conclusion.

Read the complete actual `RRTCriticalUpperTransfer.lean` body:
mathematical/statement **PASS**. The source-facing clock premise is
retained explicitly. The regularized center lower bound, positive
ceiling, dimension cutoff, logarithmic cancellation, time monotonicity,
actual PWIT/geometric bridge, and genuine index-tail factor two all
match the earlier checkpoint. The non-strict real height event is
identified exactly by `Nat.ceil_le`. A separate sign assumption on the
clock constant is unnecessary for this conditional implication; the
actual clock inequality itself supplies any needed sign when used.
No small-size or finite-prefix exception is omitted.

The proposed `ReverseDelayedMatching.lean` local interface receives an
early **PASS**. A fresh distinguished label is different from both old
selected roots. Therefore adjoining its singleton commutes with joining
those old roots in every actual rooted-forest field, not merely in
height. Joins preserve vertices, so freshness persists. The corresponding
ordered-list equality is filtering an old donor through a fresh head;
the distinguished update agrees with the ordinary join on this avoidance
branch. Positive original source positions must subsequently be
transported by subtracting one. This proves one concrete delayed
matching operation, without claiming the global C3/C6 induction or a
probabilistic history-independence statement. No compiler was run here.

Read the subsequent full `ReverseDelayedMatching.lean` body:
mathematical/statement **PASS**. The extensionality proof compares all
actual forest data, and the ordered equality retains the complete root
list. Valid old roots ensure the distinguished avoidance branch.
`prependIndex` adds one, `lowerPositiveIndex` subtracts one under its
strict-positivity guard, and their inverse theorem recovers every
positive original position. The final initialization matching theorem
retains the original shifted delayed positions while proving the actual
forest-and-list identity. This remains a local C3/C6 step.

The proposed conditional `RRTCriticalDeviation.lean` interfaces receive
an early **PASS**. The exponential-series term at $(1+x)/2$ gives

$$
(1+x)^P e^{-x}
\leq 2^P P!e^{1/2}e^{-x/2}
\qquad(x\geq0).
$$

The case $P=0$ is included. For a nonnegative reference level, a finite
unit grid starting at zero bounds the positive part by strict-tail
indicators, so a tail $De^{-x/2}$ yields expected excess at most
$D/(1-e^{-1/2})$, without an additional unit constant. Actual height
support supplies the finite truncation. The transferred non-strict tail
also bounds these strict events. Using the shifted critical center,
then adding its fixed shift and the already proved critical lower
deficit, gives conditional uniform absolute deviation and hence mean
error. Nonnegativity of the envelope constant must be supplied; it
follows from the actual clock premise at zero deviation, or can be
ensured by taking its positive part. The clock upper premise remains
explicit, so this does not independently complete E1/E2.

Read the full actual `RRTCriticalDeviation.lean` body:
mathematical/statement **PASS**. The finite unit grid uses the true
$H_n\leq n$ support with indices strictly below $n$, including the
zero-size case. Strict events are bounded by the transferred non-strict
events in the correct direction. The coefficient's nonnegativity is
derived from the actual clock premise at zero deviation, and the shifted
reference center is proved nonnegative. The offset integral, actual
critical lower deficit, and norm-of-integral estimate preserve the single
explicit clock upper premise throughout the absolute and mean bounds.

The proposed `ReverseDelayedDynamics.lean` interface receives an early
**PASS** against `main.tex` lines 757–800. When already used, the same
fresh zero-based positions are joined in both equal-size lists and the
stored pair is retained. When unused, the shorter list first consumes
the old positive pair after subtracting one; the longer list uses a
fresh pair from $0,\ldots,N-1$ and stores that original pair. If zero is
avoided, the local commutation theorem supplies the next exact pending
forest/list identity, and the new positive stored positions are at most
$N-1$, as required at the new size.

The used branch needs the general fact that joining cannot turn a
nonsingleton distinguished component into a singleton; the existing
lemma beginning with a singleton is insufficient for that branch.
This necessary ingredient was flagged to the implementer. At size one,
an unused state would require two distinct positive stored indices at
most one, so it is impossible. Finite actual-kernel iteration can prove
the proposed C3/C6 validity and matching invariants. C4/C5 marginal and
history assertions, and C7's one-component graft relation at first use,
remain separate. This is an interface review, not completed iteration
evidence; no compiler was run by this reviewer.

The subsequent unused-step implementation refinement also passes: put
$G$ equal to the shorter forest after consuming the old stored pair, then
reuse `initializationLaw G i`. On the invariant, the current longer
forest is exactly `prependLabel G i`, so this is the identical source
fresh-pair kernel. An explicit equality with the direct current-longer
transition is still required. Probability on valid/reachable states
suffices; inconsistent arbitrary metadata need not define a probability
kernel.

For the upcoming first-crossing assembly, the precise polynomial-density
cutoff was flagged to the coordinator. With degree fourteen, its current
interface requires prefix length at least $2(14+1)=30$. The negative
barrier argument must therefore exclude all lengths below thirty,
including twenty-nine; an older schematic cutoff at $2P$ alone would
miss one length. Choosing $A_0>30\cdot5/(2e)$ safely covers them using
the proved coarse time-center bound. Endpoint normalization gives the
factor $(1+(a+c)j/s)^{14}/j$, which is bounded by
$2^{13}(1+((a+c)j/s)^{14})/j$ before using the polynomial-density helper.
These are prospective assembly requirements, not defects in the current
proved helper statements.

Read the complete actual `PWIT/SoftBallotSummation.lean` and
`PWIT/LogBallotKernel.lean` bodies, together with the new finite-sum
lemmas in `PWIT/LogBarrierSummation.lean`: mathematical/statement
**PASS**. The good regime gives the symmetric smaller-block logarithmic
weight. In the exceptional regime, the actual first-angle estimate,
$L\leq11M^2$, and $k\geq d/2$ give the stated degree-twelve point
bound. Reflection of indices is injective on the summed range, so the
weight sum is at most twice the fixed summable-series constant.

The number of exceptional suffix positions is at most
$\lceil21M^2\rceil\leq22M^2$. The zero cyclic position is handled
separately, with its weight equal to zero and its short-suffix indicator
absent in the large-dimension branch. Thus exactly one $1/d$ term is
present. The resulting coefficients are $8C_{\mathrm{occ}}S$ and
$22K_{\mathrm{short}}$, and the additional constant forty-three safely
covers the unit numerator and all small dimensions. The final actual-law
bound has fixed degree fourteen, covers every positive dimension and
all $A,c\geq0$, and introduces no unproved probability estimate.
Compilation of the final assembly is being performed by the coordinator;
the reviewer ran no Lean/Lake.

Coverage arithmetic was checked for the proposed next integrated
milestone: from 60 complete, 8 partial, 14 pending, and 3 questions,
promoting F2 from partial to complete and C2 from pending to complete,
then recording C6's local matching as partial, gives **62 complete,
8 partial, 12 pending, and 3 questions**, still 85 IDs. These promotions
require the new integrated build/axiom evidence. C6's local scope does
not complete the delayed iteration, C4/C5, or E1/E2.

The proposed `PWIT/LogBarrierIntensity.lean` interface receives an early
**PASS**. At positive endpoint $s$, scaling the actual normalized bridge
replaces $A,c$ by $Ad/s,cd/s$. The safe factor $2^{14}$ reduces its
degree-fourteen bound to the existing polynomial-density estimate for
$d\geq30$, with the stated coefficient. Measurability of an endpoint
set must be retained for exact disintegration, negative-endpoint density
is zero, and the zero endpoint is handled using the positive density
power. Integrating over $[0,b]$, $b\geq0$, gives the additional factor
$1/e$. The actual all-rank generation-count and existence bounds use
this exact intensity measure; no fixed-label path claim or conditioning
on a null endpoint is permitted. Its explicit soft-bound premise can
be discharged by the actual degree-fourteen theorem after compilation.

Read the complete actual `PWIT/LogBarrierIntensity.lean` and
`PWIT/LogBarrierIntensityActual.lean` bodies: mathematical/statement
**PASS**. The exact endpoint transport retains the unnormalized
generation density and a measurable endpoint set. It uses the actual
simplex reconstruction, including totalized negative endpoints through
zero endpoint density. Both coefficients scale in the correct direction
for positive endpoints. The zero endpoint and polynomial cutoff are
discharged by $d\geq30$.

Local integrability is proved before conversion from the nonnegative
integral to a real integral. Endpoint integration has exactly the factor
$1/e$. The count and existence exports use the actual all-rank vector
count, Tonelli, and a pointwise witness contributing at least one. The
`Actual` adapter genuinely discharges `LogSimplexBound` with the proved
degree-fourteen simplex theorem; it leaves no probability estimate as
an assumption. This is the prefix-intensity ingredient, not yet the
critical clock first-crossing estimate.

Read the complete candidate `ReverseDelayedDynamics.lean` body:
mathematical/statement **PASS**. It supplies the necessary singleton
noncreation lemma. The exact direct pending-kernel equality justifies
reuse of initialization, and the synchronized branch preserves the
source's stored pair. Bounds on that pair are required only while it
is unused, which is essential once the component count has decreased.
Valid-state transition probability, finite iteration, source-tail bind,
and terminal used flag all have the correct domains, including $k=1$.
The generic invalid-state totalization is not misrepresented as an
everywhere probability kernel.

An immediate explicit next-shorter marginal equal to the Dirac mass at
`consumeDelayed z` was requested for valid unused states. It exposes
C6's literal neighbouring-phase relation, which follows directly from
the implemented pending kernel. The current complete body is a valid
state-invariant construction; its compiler evidence is still pending.

The proposed next C4 projected-transition and phase-marginal targets
receive an early **PASS**, with a scope warning. The source at line 798
asserts the law of the whole first forest sequence. Equalities of all
individual phase marginals alone are weaker. The proposed actual
projected transition kernel depends only on the current longer forest,
so a finite projected-history induction can supply the stronger claim.
That history identification, with the actual common tail prepended,
is needed for C4 completion; phase marginals alone should be recorded
as partial. This distinction was sent to both coordinator and implementer.
It supplies no C5 delayed-pair independence assertion. The reviewer ran
no Lean/Lake commands in this group.

The proposed conditional sharp E1/E2 adapter receives an early
mathematical/statement **PASS** against `main.tex` lines 237–242 and
446–451. Comparing the regularized critical center with
$e\log n-(3/2)\log\log n$ must use $n\geq2$; that restriction fully
covers the stated asymptotics. Uniform actual absolute deviation implies
tightness and the corresponding bounded mean error. No distributional
input beyond the actual law is added.

For E2, the faithful stronger interface quantifies every natural $n$ and
every real $k\geq0$. The non-strict lower event must be included in a
strict lower-tail event using the explicit unit shift, with large-$k$
cutoff equal to the mean-center error plus one. The upper event uses
the transfer and mean-center offsets, polynomial absorption, and
$1/2\geq1/(3e)$. The remaining bounded range of $k$ is handled by
probability at most one; in particular the final constant must be at
least one at $k=0$. All sharp exports retain the critical clock upper
premise until the actual first-crossing theorem discharges it.

Read the actual `RRTSharpHeightConditional.lean` body:
mathematical/statement **PASS**. Its explicit source-center comparison
$e\log2+(3/2)\log5$ follows uniformly for $n\geq2$. The absolute
deviation, mean expansion, and tightness exports retain the clock
premise. For E2, the common offset $T=A+B+1$ gives both event
inclusions, including the strict lower event. The exponential-rate
comparison and the fixed prefactor cover every real $k\geq0$ and every
size, including zero threshold and zero-size trees.

Read the actual `FiniteMarkovHistory.lean` body:
mathematical/statement **PASS**. Its state records the current state
and the complete preceding list. The current-coordinate pushforward is
the genuine iterated law. The almost-sure projected-kernel premise on
those current states lifts to the history law, yielding equality of
the entire finite projected history. Explicit discrete measurable
spaces justify the maps; no countability or standard-Borel assertion
is smuggled into the interface.

Read the actual `ReverseDelayedLongerLaw.lean` body:
mathematical/statement **PASS**. The natural/finite position bridge
retains genuine uniform ordered-distinct root sampling. The requested
next-shorter Dirac marginal and its source-phase corollary make C6's
neighbouring-phase relation explicit. The longer projected kernel is
proved conditional on the full current joint state, and the history
export identifies its entire post-initialization joint history. With
the state-invariant iteration, **C3 and C6 are eligible for completion
after this group's clean build/axiom evidence**. C4 remains partial
until the actual incoming tail and both initialization states are
prepended to identify the literal full source history. That missing
last adapter is explicitly acknowledged rather than inferred from
post-initialization equality.

The refined critical-clock first-crossing route receives an early
**PASS** with $c=2/e$, $A_0=30\cdot5/(2e)+1$, and dimension cutoff
thirty. A witnessing finite depth-$d$ path has a first crossing; actual
almost-sure nonnegative clocks and the coarse time-center bound rule
out every crossing below thirty. Only crossing terms with nonnegative
endpoint barrier may be passed to the intensity adapter, before
enlarging by nonnegative envelopes.

The uniform prefix allowance
$a+c\log(\min(j,d-j)+1)$ is valid and avoids the earlier small-prefix
logarithm issue. In the first half, the global logarithmic window at
an earlier prefix is at most its value at $j$; in the second half, the
proved minimum-window product bound supplies the additional local
window. Dropping the nonnegative chord correction is legitimate. The
endpoint-normalized polynomial then contains the logarithm of the
minimum, not a logarithm of the full depth at small $j$.

The proposed `CriticalDepthWeights` simplification also receives
**PASS**: logarithmic concavity in fact yields
$d^{j/d}\leq j+1$ for every $1\leq j\leq d$, so no half split is
needed for the depth-kernel estimate. Thus

$$
\frac{d^{3j/(2d)}}{j\sqrt j\,(\min(j,d-j)+1)^2}
\leq\frac{4}{(\min(j,d-j)+1)^2}.
$$

The reflected logarithmic weight sum is at most eight times the shifted
summable-series constant. The shifted weight at zero is one and retains
the terminal-prefix term $j=d$; the earlier unshifted totalized weight
at zero must not be substituted there. These first-crossing statements
are interface/route checkpoints, not yet a proved clock upper bound.
No compiler was run by this reviewer.

Read the complete actual `PWIT/CriticalDepthWeights.lean` body:
mathematical/statement **PASS**. Its global chord bound, real-power
conversion, and safe factor four hold at every $1\leq j\leq d$.
The shifted series is genuinely summable and nonnegative, and replacing
the inverse-square denominator by the shifted three-halves denominator
has the correct direction. Reflection retains the terminal term with
minimum index zero. The final finite-sum theorem also correctly handles
$d=0$ through an empty sum; its positive-index pointwise lemma is never
used at zero.

For the coordinator's next integrated milestone, the precise proposed
classification is **63 complete, 9 partial, 10 pending, 3 questions**,
conditional on its new build/axiom evidence. Relative to 60/8/14/3,
F2, C2, and C3 become complete; C6 becomes partial for the currently
compiled local and state matching (the neighbouring-phase adapter is
not yet in that closure). C7 also becomes partial because the actual
terminal flag theorem proves the explicitly stated source subclaim
$M_0=1$. Its first-use history/index and the one-component graft relation
remain unresolved. This partial credit does not certify C7 or C4 in full.

The proposed final C4 whole-history wrapper receives an early **PASS**.
It must retain dependence on the actual incoming tail history when
binding on its current forest. In newest-first order, the missing
predecessors of the post-initialization history are the inserted forest,
then the incoming forest, then that tail's previous states. The generic
merge with past list `g.past ++ h.past` is correct when the continuation
starts at the existing current state, so it does not duplicate that
state, even for a zero-length continuation. The exact source sign/index
alignment of insertion, join, and remaining joins is still a required
implementation step. No shortened-tail ID relabelling or C5 premise
is needed for this first-process history identification.

Read the complete actual `FiniteMarkovHistoryConcat.lean` body:
mathematical/statement **PASS**. Splitting after a fixed number of
steps and exposing the first transition both retain the full prior
history in the correct newest-first order. Zero-length continuations
recover the original history without duplicating the common current
state. The implementer retained the original ordered-tail-history
construction for C4, matching `sourceDelayedLaw` directly. A proposed
canonical reordering at the tail boundary was not adopted; although
its graph continuation would agree, it would require an extra explicit
bridge back to the original coupled construction.

The reviewer read the header of
`/private/tmp/freezing-growth-ballot-dynamics-2026-11-01-axioms.log`:
it checks **4055 declarations** and permits only `propext`,
`Classical.choice`, and `Quot.sound`. This agrees with the coordinator's
reported clean **4155-job** integrated build and the scoped inventory
of **63 complete, 9 partial, 10 pending, 3 questions**. Newer working
files outside that closure receive no mechanical credit from this log.

Read the complete actual `PWIT/CriticalBarrierGeometry.lean` and
`PWIT/CriticalFirstCrossing.lean` bodies: mathematical/statement
**PASS**. `Nat.find` chooses the first crossing along one witnessing
finite path and is bounded by its final depth. It does not assume that
a minimum over an infinite generation is attained. Nonnegative clocks
and the fixed offset exclude every prefix below thirty. Endpoint
nonnegativity remains explicit in the crossing event carrier.

The finite prefix address is transported to its actual tuple of
increments; its endpoint sum and all shorter cyclic prefixes equal
the corresponding actual birth times. The unified minimum-window
allowance has the correct sign after subtracting the endpoint chord.
The event carrier contains only this actual path event and its scalar
nonnegative endpoint condition, without a law or conditional estimate
premise. A measurable-event export was suggested for the forthcoming
finite union; countability of the finite natural-coordinate path
carrier and measurability of actual increments supply it.

Read the complete actual `ReverseAlgorithmHistory.lean` and
`ReverseSourceLongerHistory.lean` bodies: mathematical/statement
**PASS**. The reverse time index, horizon hold, actual current-law
identities, and full ordered-to-graph history projection match the
existing Algorithm 2. The incoming tail history remains the original
actual ordered history. After its length $\ell$, phase $k+1$ is reached;
time $\ell$ inserts freeze label $k$, and times $\ell+1+j$, $j<k$,
are exactly the remaining $k$ joins.

The conditional prefix history retains both initialization predecessors
in newest-first order. Binding this continuation on the actual incoming
history preserves all dependence, and the final concatenation identifies
the full labelled-graph history at the source word's full horizon.
The boundary $k=1$ retains both predecessors with zero later delayed
steps. This resolves the previously flagged C4 history gap:
**C4 is eligible for completion after this batch's clean build and
axiom evidence**. C1's common-tail relabelling and C5's comparison
history law are not inferred. No compiler was run by the reviewer.

The proposed `CriticalCrossingWeights` exponential/envelope adapter
receives an early **PASS**. For $c=2/e$ and $a=x/e+A_0$, the exact
exponent is

$$
eB_j-j=\frac{3j}{2d}\log d-x-eA_0
       -2\log(\min(j,d-j)+1).
$$

For nonnegative $A_0,x$, its polynomial is bounded by
$(1+A_0+2/e)^{14}(1+x)^{14}(1+L)^{14}$ with
$L=\log(\min(j,d-j)+1)$. The reflected depth sum contributes
$8S$ and retains $j=d$. There is no missing factor $1/e$ in this
analytic adapter: that factor already belongs to the generation
intensity constant. The actual crossing-event union remains separate.

Read the complete actual `PWIT/CriticalCrossingProbability.lean` body:
mathematical/statement **PASS**. Its almost-sure inclusion uses the
actual positive-clock support. Crossing events with negative endpoints
are empty; the others use precisely the interval $[0,B_j]$. The finite
union bound sums the actual all-rank generation bounds and retains the
full deviation dependence in their exponent. There is no conditioning,
independence, or global-minimum premise.

Read the complete actual `PWIT/CriticalCrossingWeights.lean` body:
mathematical/statement **PASS**. The exact exponential identity,
polynomial envelope, factorization through `criticalDepthWeight`, and
enlargement from depths thirty through $d$ to depths one through $d$
are correct. Every added term is nonnegative. The final positive
constant includes the generation intensity constant, shifted series,
polynomial coefficient, and $e^{-eA_0}$ exactly once. The actual union
bound and this analytic sum have matching domains and constants.
The terminal term $j=d$ is retained, while dimensions below thirty
produce an empty sum without invoking a positive-dimension pointwise
identity. No mathematical gap was found in these assembly interfaces;
the final clock theorem and its compiler evidence remain to be checked.

The proposed `RRTSharpSplitMean.lean` interfaces receive an early
**PASS** against LP2 (`main.tex` lines 465–470) and I6 (line 427).
The actual mean-increment bound with
$\log(n+1)-\log(i+1)$ for $i\leq n$ is exactly the printed positive
log-ratio form; extending it to $n=0$ is sound. The uniform expected
absolute split-height imbalance is for the genuine uniformly split
independent component laws. It can follow from actual critical absolute
deviation and the uniform-size logarithmic-defect mean. That is a valid
alternative proof of I6 and does not discharge L2's separate tail claim.
Both new exports must retain the explicit clock premise until supplied.

Read the actual final `PWIT/CriticalClockUpper.lean` and
`RRTSharpHeight.lean` bodies: mathematical/statement **PASS**. The
nonnegative finite crossing sum justifies its exact `ENNReal.ofReal`
conversion. The resulting time expression agrees with
`CriticalClockUpperBound`, and its coefficient is finite and positive.
Every sharp RRT export actually supplies this proved clock theorem;
none retains an unproved estimate premise. The exact source center,
uniform tightness for $n\geq2$, bounded mean error, and all-size
mean-centered concentration with rate $1/(3e)$ match E1/E2.
**E1/E2 are eligible for completion after the new integrated build
and axiom evidence**, not from this body review alone.

Read the actual `RRTSharpSplitMean.lean` body:
mathematical/statement **PASS**. The critical center is monotone and
its increment is at most $e$ times the logarithmic size increment.
The uniform critical mean error gives one strictly positive LP2
constant, including zero initial sizes, and the ratio export has the
correct sign. Actual uniform split averaging and its logarithmic-defect
sum give the bounded expected imbalance $2(B+e)$. These exports now
use the actual unconditional sharp-height theorem. LP2/I6 are eligible
for completion after the same mechanical checks; L2 remains separate.

The proposed `TwoSeedSharpGap` I7 interfaces receive an early **PASS**
against source lines 428–435. The exact joint decompositions reduce
the error from the positive depth gap to the Lipschitz difference of
two positive parts, the term $\max(1,\Delta)$, and the two nonnegative
remainders. Their absolute bound is precisely
$1+2\mathbb E|\Delta|+\mathbb E Z_++\mathbb E\hat Z_+$.
Actual depth-pair exchangeability gives the expected positive gap equal
to half the expected absolute distinct-pair gap. The full-floor
remainder limits and uniform split bound then give the printed bounded
error. No CLT or independence between two different old trees is needed.

The proposed `RRTSharpSplitTail` LP3/LP4/L2 interfaces receive an early
**PASS** against source lines 361–368 and 465–483. Retaining the actual
size tag and reflecting $i\mapsto n-i$ on its true support gives the
two factors of two in the four-term union bound at threshold $k/4$.
The ratio count must use $i+1$, giving the floor of $r(n+1)$ and
correctly retaining the zero-size component. The intermediate LP4
bound is exactly

$$
2c e^{-k/(12e)}+2e^{1-k/(4C)}.
$$

Choosing $c_2=\min(1/(3e),1/C)>0$ and one shared
$c_1\geq\max(c,e,c_{\mathrm{L1}})$ yields the printed
$4c_1e^{-c_2k/4}$ while preserving L1 with that same witness.
The shared pair must be exported explicitly, rather than leaving
independent existential witnesses. The stronger all-size, nonnegative
real-threshold formulation is valid. No compiler was run by this reviewer.

Read the full actual `TwoSeedSharpGap.lean` body:
mathematical/statement **PASS**. Its absolute-gap integral is the genuine
ordered-distinct pair average from the same original RRT; $m\geq1$
supplies at least two active vertices. The swap law preserves that
same tree and its full maximum. The positive-part identity, actual
word-height marginal integration, pointwise decomposition error, and
full-floor bounded-error conclusion match I7. No independent-old-tree
or CLT premise is present. I7 is eligible for completion after current
build/axiom evidence.

The proposed `HighPopulationSharp` interface receives an early **PASS**.
Uniformly bounded sharp mean error at the corrected
`highPopulationIndex`, followed by the proved deterministic center gap,
supplies the missing H3 fine expansion and threshold comparison.
An explicit eventual log-ratio version was recommended to mirror the
displayed equality directly; it is the same expansion once both indices
are positive. With that evidence, H3 can be complete in the corrected
SF2 form. The literal printed $r_n$ stochastic comparison is not asserted.

The proposed local `ReverseFirstUseGraft` C7 interface receives an early
**PASS**. A distinct initializer pair using the distinguished position
has exactly one zero and a unique positive position $q+1$. A
distinguished receiver replaces the old component root by the new
root in that same slot; a distinguished child preserves the old root
order. The old selected component is respectively grafted below or
above the singleton. Every other old component retains parent, root,
and depth, and the unique added graph edge is between the distinguished
vertex and selected old root. The lift must concern initialization or
a previously unused transition whose next flag is true. Stored indices
must not be treated as valid current positions at arbitrary later used
states, since they are retained while the component count shrinks.

The proposed C8 used-state profile invariant also receives an early
**PASS**. A fresh used initializer changes only one aligned component
and cannot reduce its height. Thereafter the same legal positions apply
the monotone graft operation to both profiles. The unused branch can
re-establish this implication at its next used initialization, without
requiring a prior profile inequality. Terminal use then yields
pathwise maximum-depth domination for the actually sampled terminal
forests. C5 is still required to identify the shorter marginal; this
invariant supplies neither that law nor a first-hit history theorem.

### Critical-height integration and the next split/reverse interfaces

Independent actual-body review of `HighPopulationSharp.lean`: **PASS**.
The eventual sharp mean error uses the actual corrected comparison index
$r_n-1$. The explicit logarithmic-ratio expansion has positive indices before
using the logarithm quotient identity. The bounded mean error and previously
proved diverging deterministic center gap give the claimed uniform margin.
This closes H3 in the recorded SF2 correction; it does not assert the printed
$r_n$ stochastic domination. The typed proof repairs in `TwoSeedSharpGap`
do not change its previously reviewed actual joint-law argument.

Read the successful 4,172-job build output and the header of
`/private/tmp/freezing-growth-critical-2026-11-01-axioms.log`: 4,260
declarations have only `propext`, `Classical.choice`, and `Quot.sound` in
their transitive axiom closures. With the actual-body reviews above, E1,
E2, LP2, I6, I7, H3, C4 and C6 can be marked complete. The inventory arithmetic
is **71 complete, 5 partial, 6 pending, and 3 questions**, retaining all 85
source obligations. The source hash and inventory scope are unchanged.
This is an affected-results milestone, not a claim of whole-paper coverage,
fresh clean-checkout replay, Comparator success, or Palomar verification.

Read `RRTSplitSampling.lean` and the complete `RRTSharpSplitTail.lean`,
including the added intermediate maximum/ratio exports: mathematical and
statement **PASS**. The sampled law is the actual first-edge split of the
$(n+1)$-edge RRT, not a newly stipulated mixture. Its size ranges from zero
through $n$, and its first component has that many edges. The exact mixture,
reflection of the finite size range, and four-term triangle inequality give
the two factors of two at threshold $k/4$. The uniform ratio count uses
$(i+1)/(n+1)$; its proof retains the zero-size component and is valid also
at $n=0$ and ratio threshold zero. The maximum over marginal deviations
and the ratio-event probability are exported before either is bounded.
The exact two-exponential LP4 expression is retained. The final theorem
`paper_height_comparison_and_split_tails` uses one shared pair

$$
c_1=\max(c_{\mathrm{L1}},c,e),
\qquad c_2=\min\left(\frac1{3e},\frac1C\right)>0,
$$

for the existing eventual comparison and the all-size split tail. No estimate
premise remains. The stronger real nonnegative threshold scope preserves the
source natural thresholds. These new files are outside the 4,260-declaration
milestone until the coordinator supplies their integration evidence.

Read the complete `ReverseFirstUseGraft.lean`: mathematical and statement
**PASS**. The original stored pair is either $(0,q+1)$ or $(q+1,0)$, with
the actual old root at position $q$. The full forest equality includes the
unique added edge and the appropriate graft orientation. The distinguished
receiver changes the old component root in precisely its existing list slot;
the distinguished child keeps the list. Parent, root and depth remain
unchanged on every other old component. Its almost-everywhere lifts concern
the actual initializer and an actual previously unused transition becoming
used. They do not misinterpret the retained old indices at later used states.

Read the complete `ReverseDelayedDomination.lean`: mathematical and statement
**PASS**. The exact first-use root-order formulas give an aligned component
height inequality, including both graft orientations. The legal natural
position operation is identified with the actual height-list graft before
monotonicity is used. The unused branch obtains the implication anew from
its actual initialization kernel; the used branch applies the same legal
positions in both forests. Induction through the actual finite delayed law,
followed by its terminal used flag, yields the actual terminal maximum-depth
comparison. No shorter marginal premise or first-hit random index is hidden
in this proof. C8 should record this pathwise part as proved while retaining
the remaining identification of this construction with the source shorter
process in C5. Neither new reverse module was part of the 4,260-declaration
audit cited above; the coordinator reports their separate clean builds.

Early C7 full-history first-hit checkpoint: **PASS**. In the actual
chronological post-initialization history, the terminal true flag supplies
a first true index. The index-zero case uses the actual initializer graft;
a positive first index uses the immediately preceding unused transition
and the graft of `consumeDelayed` there. Keep the entire history and the
explicit reversal $j_1=k-1-r$ to recover the source maximum. Original stored
positions and the selected component slot must remain in the final statement.
This pathwise statement needs no comparison-process marginal assumption.

Early C5 joint-history checkpoint: **PASS** for the proposed mixture of the
entire shorter ordered history and the pending tag. At phase $N=k-t$, the
pending tag, conditional on pending, is uniform on distinct positions in
$\{1,\ldots,N\}$ and independent of that shorter history. The used branch
uses a fresh uniform zero-based pair; the pending branch consumes the old
uniform pair after subtracting one. Both therefore produce the same next
ordinary shorter-history law. The new fresh draw then has used probability
$2/N$ and pending probability $(N-2)/N$, with its pending pair uniform on
$\{1,\ldots,N-1\}$. The initial weights are $2/(k+1)$ and $(k-1)/(k+1)$.
At $k=1$ the pending term has zero mass; its singleton positive-position
pair measure must not be asserted to be a probability. This is independence
from the shorter-process history, not from all joint-process choices.
The eventual literal shortened-word tail/label identification remains a
separate obligation.

Read the actual first C5 module `ReverseDelayedTags.lean`: **PASS**.
`positivePositions` is exactly the positive interval, and `lowerPair` is a
bijection of the actual off-diagonal supports. `freshPendingLaw_eq` comes
from restricting the actual finite-pair sampler to avoidance and its
complement. Its $N=2$ pending term is zero without a false probability
instance on a singleton pair space. The initialization tag and joint
shorter/tag laws are direct actual Fin-sampler pushforwards. This module
does not assume or yet prove the full-history mixture invariant.

No Lean or Lake command was run by this independent reviewer.

Read the complete `FiniteMarkovHistorySupport.lean` and
`ReverseFirstUseHistory.lean`: mathematical and statement **PASS**.
The chronological `states` list is the reverse of the newest-first storage;
each sampled transition appends precisely one chronological state. Adjacent
relations are proved using the actual run-law projections, while the original
initial-state property and exact history length are retained on that same
history. The first-true-index lemma makes no independence assumption.
`FirstUseAt` separates initialization from a positive first index and in the
latter case invokes the actual preceding unused transition. Its `reverse_max`
export is the source's largest used index under the reversal $j=k-1-r$.
The actual source bind retains the incoming forest and yields exactly $k$
post-initialization states, including the $k=1$ boundary. With the existing
terminal-use theorem and the full `FirstUseGraft` relation, these statements
cover C7's first-hit and one-component graft assertions after the coordinator
obtains current build/axiom evidence. They do not assume or prove C5.

Read the complete `ReverseShorterView.lean`: mathematical and statement
**PASS**. The custom discrete carrier retains the entire shorter history and
forgets only the stale delayed pair after use. Both projected update branches
are derived from the actual coupled kernel. Before use, the original positive
pair is lowered and consumed, and the fresh tag uses the actual range-$N$
sampler. After use, the shorter forest takes an ordinary fresh uniform pair.
The positive-pair transport identifies the ordered ordinary join law, and
the successor identity uses actual history-current validity; its horizon
guard ensures $N\geq2$. This proves the exact projection groundwork without
assuming a product law between the history and its pending metadata.

Read-only E4 exploration checkpoint: the proposed rare-reset comparison is
mathematically valid but gives no implementation credit. For two vertices
sampled with replacement in an actual $N$-vertex RRT, put $p=1/(N+1)$.
The two-depth recursion has old/old weight $(1-p)^2$, the two single-new
weights $p(1-p)$, and a diagonal reset of weight $p^2$. Replacing only the
last branch with independent Bernoulli increments changes expectations of
tests bounded by one by at most $2p^2$. Starting at a fixed cutoff $K$,
the accumulated error is at most $2/K$. The source only needs the depth
difference, so it suffices to use a one-dimensional comparator with
independent increments taking $1$ and $-1$ with probability $p(1-p)$ each,
and zero otherwise. Its variance is $2p(1-p)$. The bounded initial difference
vanishes after division by $\sqrt{\log n}$, and switching to distinct sampling
costs at most $2/N$ for the same bounded tests. A nonidentical-increment CLT
or a full characteristic-function limit theorem is still required; none is
assumed proved by this exploration. E4 remains pending.

Scoped re-review of the final `ReverseFirstUseHistory` carrier change:
**PASS**. `FirstUseHistorySample` stores exactly the same incoming forest
and full history with an explicit discrete measurable space; this avoids
identifying a canonical product sigma-algebra with the discrete one. The
new `sourceFirstUseHistoryLaw_current` is the exact bind/map consequence
of the actual history-current law and identifies the terminal marginal with
`sourceDelayedLaw`. Explicit natural values in finite list indices preserve
the first-hit statement. The coordinator reports clean focused builds for
this file and `RRTSharpSplitTail`; final integration evidence is still pending
at this checkpoint. Moving LP3, LP4 and L2 from pending to complete and C7
from partial to complete would give **75 complete, 4 partial, 3 pending,
3 questions**. C8 retains the separate C5 identification limitation.

Read the new integration logs directly: the full build completed with
**4,178 jobs**, and
`/private/tmp/freezing-growth-split-first-hit-2026-11-01-axioms.log`
checks **4,355 declarations** with only the three permitted axioms. This
supports the reviewed **75/4/3/3** milestone, including the shared L1/L2
constants and C7. It does not include later C5 source files under development.

Read the complete `ReverseShorterHistoryLaw.lean`: mathematical and statement
**PASS**. The used and pending branch averages both act on the whole shorter
history through the same actual ordinary ordered join law. The pending branch
averages the original uniform positive pair before drawing fresh metadata;
no independence from full joint-process choices is asserted. The deterministic
weight recursion has sum one at the legal finite horizons. Its normalization
argument uses genuine fresh finite-pair probability laws, so the last singleton
positive-position space is never given a false probability instance.
`projectedShorterHistoryLaw_eq` proves the product invariant on the custom
discrete carrier; `delayedHistoryLaw_shorter_pendingTag` then gives an actual
product on the canonical history/tag product space. The final shorter-history
marginal is the entire ordinary coalescent history in the common label space.
The shortened word's literal tail/label/history identification remains open;
these exports alone do not close all of C5.

Early full-tree graft checkpoint: **PASS** for the proposed master-RRT
construction. From `ValidAt T` with active vertices exactly distinct $u,v$,
an independent master $(n+1)$-edge RRT supplies parents for master labels
$2,\ldots,n+1$. Embed $0$ at $u$, $1$ at $v$, and $j\geq2$ at $T+j-1$;
omit the forced master edge between zero and one. At each replay step the
embedded master prefix is precisely the actual active set, so uniform parent
sampling is the true continuation kernel. The master birth order already
encodes the interleaving; no independent label shuffle is required.
The complete graft characterization must preserve old graph, parents and
freezing data, add only the mapped non-first edges, and use component-relative
heights. For I2, the same master uses seed order $(U,V)$ in the baseline and
$(U',U)$ in the longer word. For II1, the same master is reused in all three
actual frozen-vertex cases, including the retained frozen child. For III1,
$n\geq1$, use the master $(n+1)$-edge tree and its actual $n$-edge prefix;
the shorter continuation has $n-1$ attachments. Generic continuation theorems
do not replace the final joint word and component-law exports.

Early `RRTDepthPairRecurrence` interface checkpoint: **PASS**. The proposed
law samples both vertices independently conditional on the same actual tree.
At $n$ edges, $p=1/(n+2)$ gives the exact signed-difference recursion with
weights $(1-p)^2,p(1-p),p(1-p),p^2$ on the unchanged law, shifts by one and
minus one, and a reset to zero. Every real test is integrable under the actual
finite laws. A state-level average identity requires nonempty active vertices:
the proposed empty-state fallback has integral $f(0)$ whereas the totalized
finite average is zero. The actual all-attachment laws supply nonemptiness.
For $n\geq1$, the with-replacement law is exactly $n/(n+1)$ times the distinct
law plus $1/(n+1)$ times the zero atom; the bounded-test comparison error is
at most $2/(n+1)$. None of these recurrence statements supplies the still-open
Gaussian convergence.

Early C1 shortened-tail relabelling checkpoint: **PASS**. Let
$X=(+1)^k(-1)\,\mathrm{tail}$ and
$Y=(+1)^{k-1}\,\mathrm{tail}$, with $k\geq1$ and $n=|Y|$.
The proposed frozen-label permutation sends $j<2$ to $n+j$, sends
$2\leq j<n+2$ to $j-2$, and fixes later labels. Its inverse sends
$j<n$ to $j+2$, sends $n\leq j<n+2$ to $j-n$, and fixes later labels.
These remain genuine inverses at $n=0$ and $n=1$ with the stated branch
order. Every actual tail insertion has $k+1\leq j\leq n+1$, so its image
is exactly the shortened tail's index $j-2$. Fixing the active-label summand
preserves the initial forest; permuting only the frozen-label summand preserves
the frozen/active distinction. Full forest and ordered-list equivariance,
followed by whole-history transport, is the required characterization.
Concatenate only the $k-1$ shorter joins after that tail history; do not add
the two longer initialization predecessors. This includes $k=1$. The
distinguished vertex is absent from the shorter construction being relabelled.

Read the complete current `RRTDepthPairRecurrence.lean`: mathematical and
statement **PASS**. Its nonempty-state kernel bridge, actual finite support,
and all-real-test integrability are proved before the recursion is used.
The four attachment branches are explicit finite sums; averaging the actual
uniform parent gives the reset recurrence with $p=1/(n+2)$. Both-new sampling
contributes $f(0)$, not an independent-increment expectation. Sign symmetry
is a swap within the same sampled state's double sum. The current file ends
with actual real-test recurrence and symmetry; distinct sampling comparison,
measure/characteristic-function recursions, and Gaussian convergence remain
separate work. No reviewer compilation was performed.

Read the complete `TwoSeedGraftLaw.lean`: mathematical and statement
**PASS**. The embedding is injective under the two old-label bounds and
distinctness. Replay omits the master edge between zero and one, reads the
next master parent at label $n+2$, and adds the actual label $T+n+1$.
The exact active-set image identifies both uniform-parent kernels; induction
through the true master tree law and actual continuation bind proves the
full-state terminal law, including zero continuation steps. The stated law
identity is valid under its weaker hypotheses; `ValidAt T` remains needed
for the intended fresh-label geometric interpretation of arbitrary old data.
No shuffle or component-independence assumption has replaced the actual master
law. For final I2 coverage, the source additionally names coupled finite
process histories. The replay construction supports such a joint law, but
separate terminal marginal identities at each size alone do not certify it;
retain an explicit finite-history or parent-array characterization before
claiming that process assertion. Full graft geometry and word wrappers remain
separate obligations.

Read `ReverseOrderedRelabel.lean`, `ReverseDeletionLabels.lean`, and
`ReverseDeletionTail.lean` in full: mathematical and statement **PASS**.
Relabelling preserves the complete rooted forest and ordered root list.
The ordinary join law is equivariant under the actual uniform distinct-pair
sampler; invalid-pair and duplicate-insertion fallback branches are also
transported. The explicit permutation and inverse preserve the small-size
boundaries. The tail step uses actual backwards insertion time
$|X|-(t+1)$ and maps it to $|Y|-(t+1)$, while the corresponding sign is read
at $|X|-t$ or $|Y|-t$. Initial active-label forests coincide after relabelling.
Consequently `orderedHistoryLaw_deletion_tail` identifies the entire ordered
tail history through exact projected kernels and retains dependence between
all phases. `initializationTailLaw_deletion` is its true current marginal.
Admissibility is unnecessary for these totalized equalities themselves;
the intended source wrappers retain it. Together with the existing validity
and active-profile facts, these statements close the remaining C1 coupling
scope once current build and axiom evidence is supplied.

Read the complete `RRTDepthPairDistinct.lean`: mathematical and statement
**PASS**. Its off-diagonal removes equal vertex IDs, not equal depths; two
different vertices at the same depth remain in the zero atom. Exactly $N$
diagonal terms $f(0)$ are removed from the with-replacement double sum.
The normalizations $N^2$ and $N(N-1)$ therefore give coefficient
$1-1/(n+1)$ in the actual $n$-edge law. Every finite-average identity carries
the needed cardinality bound or $n\geq1$; the degenerate kernel fallback is
not mistaken for that finite average. Actual finite support supplies arbitrary
real-test integrability, and the difference of expectations for tests bounded
by one is at most $2/(n+1)$. The Gaussian limit E4 is still not proved by
these sampling identities. No reviewer compiler command was run.

Read the complete `ReverseSourceShorterHistory.lean`: mathematical and
statement **PASS**. It samples the original actual ordered tail history,
then the actual delayed history, appends only the old tail's `past`, and
applies the explicit label permutation. This avoids duplicating the current
incoming forest and avoids adding the two longer initialization predecessors.
The resulting history has $|Y|+1$ states, including the $k=1$ boundary.
The fixed-incoming-forest C5 history law, coalescent relabelling equivariance,
and C1 full tail-history equality identify the complete shortened-word
ordered Algorithm 2 history. Both current-marginal exports correctly connect
this construction to `sourceDelayedLaw`. A narrow remaining explicit source
independence corollary was requested: at every intermediate phase, export
the complete concatenated shorter history, including its old tail past,
jointly with the pending tag as the ordinary shortened history times
`delayedMetadataLaw`. The fixed-forest product theorem already proves the
substantive independence; this final bind transport will make the source's
entire comparison-past scope explicit.

Read `RRTDepthPairCosine.lean` in full: mathematical and statement **PASS**.
Cosine addition cancels the shifted sine terms exactly and yields the actual
reset recurrence. The ideal factor lies in $[0,1]$ for every frequency because
$0<p_n\leq1/2$. The product error starts at the actual zero-edge law and
is bounded by the finite sum of $p_k^2|1-\phi_k(t)|$. For any frequency
sequence tending to zero, each fixed actual cosine integral tends to one,
and the summable majorant $2p_k^2$ permits dominated convergence of the full
nonnegative series. Bounding the finite error sum by that full series avoids
an unjustified moving-index limit. No comparator probability law is assumed.
The scalar product's Gaussian limit and the complex characteristic-function
identification remain unproved; E4 receives no completion credit here.

Early `TwoSeedGraftHistory` target: **PASS**. One master parent array must
supply all replay prefixes, beginning at the same old state. Its pushforward
from the actual $(n+1)$-edge master law is the genuine $n$-step attachment
history with clock $T+j+1$. The previously checked active-set/parent-kernel
transport is sufficient for this entire-history statement. It addresses
the process-history scope identified for I2 without assuming independence
between terminal couplings at different sizes.

Early `RRTDepthPairProduct` scalar target: **PASS**. Write
$V_n=\sum_{k<n}p_k(1-p_k)=\mu_n-\sum_{k<n}p_k^2$, so
$V_n/\log n\to1$. If $a=2(1-\cos t)\leq1$, then $a\geq0$ and all factors
$1-a p_k(1-p_k)$ are at least $3/4$. The standard logarithm bounds give

$$
-\frac{aV_n}{1-a/4}\leq\log\psi_n(t)\leq-aV_n.
$$

For $t_n=t/\sqrt{\log n}$ and $n\geq2$, the exact identity
$a(t_n)\log n=t^2\operatorname{sinc}(t_n/2)^2$ also handles $t=0$.
It yields $a(t_n)V_n\to t^2$, while $a(t_n)\to0$. Eventual positive factors
justify exponentiating the logarithmic squeeze to obtain
$\psi_n(t_n)\to e^{-t^2}$. No Taylor remainder or complex logarithm
estimate is required by this route. This is an interface checkpoint,
not implementation or E4 completion evidence.

Read `ReverseSourceShorterIndependence.lean` and
`ReverseSourceDeletionCoupling.lean` in full: mathematical and statement
**PASS**. The former supplies the requested intermediate product law for
the entire concatenated and relabelled comparison history, including the
original common tail, at every legal phase. The incoming root count equals
the fixed $k$ almost surely, so the metadata law can be pulled through the
tail-history bind. Its already proved explicit None/positive-pair mixture
gives the corrected conditional uniformity and comparison-past independence.
No independence from all previous joint-process choices is asserted.

The latter identifies both true word-height marginals on the same actual
`sourceDelayedLaw`. Relabelling leaves maximum depth unchanged, and the
proved forward/reverse correspondence supplies each forward height law.
The actual terminal pathwise maximum-depth inequality then yields
`sourceCoupling_heightLE` by event inclusion on that single law. This verifies
the original C8 coupling route, rather than merely invoking the earlier
alternative proof of M3. After fresh integration and axiom evidence, C1,
C5 and C8 can be complete; the resulting inventory is **78 complete,
2 partial, 2 pending, 3 questions**. The retained non-question obligations
are I2, II1, III1 and E4. No reviewer compiler command was run.

Read `RRTDepthPairProduct.lean` in full: mathematical and statement **PASS**.
The actual variance sum is exactly the harmonic mean parameter minus the
summable squared Bernoulli parameters. The lower logarithm estimate uses
the correct denominator order, and factor positivity precedes both the
logarithm-of-product and exponential-of-logarithm steps. The normalized
sinc identity assumes $n\geq2$ for the positive logarithm and includes
frequency zero. Both logarithmic squeeze endpoints tend to $-t^2$, giving
the product limit and then the actual cosine limit $e^{-t^2}$, with variance
two on the source scale. No Taylor estimate or independent-array CLT is
assumed. The complex characteristic-function/weak-convergence identification
and distinct-sampling transfer remain necessary for E4 completion.

Early II1 `TaggedGraftCoupling` interface checkpoint: **PASS**. Conditional
on the actual two-active prefix, the first coordinate of its ordered pair is
the genuine uniform attachment parent. An independent uniform three-case tag
selects the fresh child, old parent or other old vertex for freezing. The
surviving seed orders are respectively $(u,v)$, $(T+1,v)$ and $(T+1,u)$,
exactly matching the three source cases. The same master parent array is
replayed at clock $T+2$ in the longer word and at clock $T$ in the baseline.
The frozen child and its full graph/parent/freezing data remain in case (a).
No extra component shuffle is required. Final full-state/graph wrappers and,
if advertised, the shared actual prefix history still need their explicit
identification.

Read `RRTDepthDifferenceCLT.lean` in full: mathematical and source-statement
**PASS** against `main.tex` line 437. Its $n\geq1$ bind-over-vertices theorem
identifies two distinct uniform vertex IDs of the same actual RRT, including
the root. The uniform bounded-test estimate transfers the cosine limit at
the varying normalized frequency. Actual same-tree sign symmetry gives zero
sine integral, and the complex characteristic function is reconstructed
explicitly before applying Mathlib's Lévy theorem. Mathlib's
`gaussianReal` second parameter is the variance; the value two has
characteristic function $e^{-t^2}$, as the file proves. Both the probability
measure limit and `TendstoInDistribution` export use the exact source
$\sqrt{\log n}$ scale. Totalized $n=0,1$ behavior affects only initial terms.
No Gaussian limit or extra estimate is an assumption. After the entire new
dependency chain has clean build and permitted-axiom evidence, E4 can be
complete by this direct recurrence/characteristic-function proof. This does
not claim to have verified the cited Lodewijks argument. At this review
checkpoint, mechanical compilation remains outstanding.

Read the source-coupling integration logs directly: the full build completed
with **4,187 jobs**, and
`/private/tmp/freezing-growth-source-coupling-2026-11-01-axioms.log`
checks **4,511 declarations** with only the three permitted axioms.
The reviewed C1/C5/C8 upgrades and **78 complete, 2 partial, 2 pending,
3 questions** milestone are therefore supported. Later graft and E4 work
is outside this evidence until its own integration is supplied.

Read the complete current `TwoSeedGraftGeometry`, `TwoSeedGraftComponents`,
`TwoSeedGraftWord`, `TwoSeedGraftHistory`, `TwoSeedGraftSample`,
`TwoSeedGraftCoupling`, and `TwoSeedGraftPrefix` modules: mathematical and
statement **PASS**. The geometric exports preserve old parent, height and
freezing data, describe exactly the new birth labels and parents, and split
the added graph into the actual master's two mapped first-edge components.
Component well-formedness is proved from the actual strictly earlier master
parents, so the forced first edge is genuinely absent. The full history uses
one parent array for every prefix and is identified with the true attachment
history by projected kernels, preserving stage dependence.

The sample retains the actual old state, its ordered distinct active pair,
and an independent actual master tree. Almost-sure support supplies validity,
two distinct seeds, and the genuine master split description. The baseline
full-state marginal and its graft graph are established. The prefix law
freezes the pair's second coordinate and attaches to its first coordinate;
this is the actual two-step transition and matches the child-first longer
embedding. The generic word continuation theorem uses the actual appended
word law. I2 is not complete at this checkpoint: the final longer appended-word
full-state marginal and the source joint history/component wrappers have not
yet been read or certified. No reviewer compiler command was run.

## 2 November 2026: resumed scoped independent review

Reviewer `/root/independent_review` (GPT-6.1 Sol, Medium; read-only, not an
author) read the current Long and Tagged branch/source/coupling proof bodies.
Mathematical source fidelity and proof route PASS for their full terminal-State
and graph/conditional suffix-history claims. This does not complete the missing
common original prefix-history coupling. Concrete proposed merged-history
interfaces have a sound design; formal early PASS awaits elaborated probes.
The E4 adapter remains consistent with the prior independent source/body PASS.
Root subsequently obtained clean focused build and twelve permitted-axiom
outputs in the dated E4 logs. No full integration or publication claim follows
from these focused checks alone.

## 2 November 2026: full-history I2 and II1 completion review

Independent native reviewer `/root/independent_review` (GPT-6.1 Sol, Medium)
read current elaborated interface probes and all new proof bodies. Early
statement-fidelity PASS and final source/body PASS for I2 and II1. Both
constructions retain the literal entire original prefix (proved by dropRecent),
actual inserted intermediate States, exact complete word-history marginals,
and original tree/ordered pair jointly independent of the actual first-edge
split. II1 also retains independent uniform tag against the entire old
history/pair/master and all three full graft graphs, including the frozen child.
The clean standalone build covers 3,796 jobs. Focused axiom and integrated
checks are separate evidence and must finish before the coverage upgrade.

III1 initial exact State/master interfaces passed independent elaborated
statement review. Its compiled marginal proofs passed actual-body review.
The independent Claude Sonnet 5.5 High design review is preserved in
`2026-11-02-claude-iii-design-review.md`; it permits independent prefix sampling
and requires the shared nested master and birth-ordered seeds. Final assembly
and mechanical evidence remain outstanding.

## 2 November 2026: final coverage and comparison-interface review

Independent native reviewer read all III1 proof bodies and actual successful
source-target build: final source/body PASS. Same-master prefix, its exact RRT
law and split identity, birth-ordered seeds, both exact word laws, full graph
grafts and preserved frozen/new data are all supplied on one space.
The source does not impose a cross-prefix joint law; the chosen product is
permissible. Figure mixture assertions are covered by the actual prefix laws
and existing III3/III4 results, not a new missing large enumeration.

An independent whole-source rescan found all 85 inventory IDs, 82 claims and
3 open questions, with no omitted rendered claim. SF1–SF6 and alternate proof
qualifications remain explicit. The current integrated build passed 4,328 jobs;
the current global audit passed 4,978 declarations with only permitted axioms.

The inactive 236-line Challenge template received static source-fidelity PASS
for its 30 exact semantic declarations and eight numbered Introduction main
result signatures. It is not an elaborated-statement or Comparator PASS; the
eight deliberate theorem placeholders await scoped activation authorization.


## 2 November 2026: final five-result candidate interface review

The independent native reviewer reused the unchanged definitions and signatures
from the earlier eight-export draft review and checked the five-result subset.
Source fidelity PASS: the combined Theorem 1.2 retains both conclusions, and
Proposition 1.1(i) retains the same-witness consequence. The compiled candidate
interface build passed with 4,332 jobs and exactly five authorized Challenge
warnings. All 358 library Lean files match the reviewed development source; no
proof module or Solution imports Challenge. The global candidate audit passed
for 4,978 declarations. Generated and implicit dependency identity remains for
official Comparator. The review found documentation-only fixes (relative links,
stale status and confusion between theorem counts and inventory row counts),
which were corrected. The schema explicitly excludes deliberate Challenge
placeholders from sorry_count; the proof-development count remains zero.

The independent reviewer also checked `docs/MAIN_RESULTS.md` against the
reviewed statements: word order, inequality direction, same witnesses,
uniformity, admissibility, terminal extinction and stochastic domination all
match. Prose fidelity PASS; no changes requested.


## 3 November 2026: final publication consistency review

Independent read-only native review PASS. The reviewer inspected the final
README, public verification/interface/status/account documents, metadata,
source-correction and inventory sections, and actual Linux logs. The recorded
4,328-job Linux build, 4,978-declaration audit, NanoDa and Lean kernel
acceptances, and five-export Comparator success support the stated results.
The reviewer independently rehashed all 365 mathematical inputs (zero
mismatches), checked the Comparator configuration against the Linux summary,
and matched current metadata and citation hashes to their 3 November schema
records. The 82 completed claims and three questions are kept distinct from
the five compared exports. No full-Palomar, public-upload or human-review
overclaim was found; no remaining publication-preparation blocker identified.
No mathematical source changed for this review.
