# The five Introduction results

This is the informal account of the five declarations selected in
[`comparator.json`](../comparator.json). The complete inventory and proof
correspondence record are in [`FORMALIZATION_REPORT.md`](../FORMALIZATION_REPORT.md).

Start with one active root. At a $+$ step, choose an active vertex uniformly
and attach a new active child. At a $-$ step, choose an active vertex uniformly
and freeze it. Frozen vertices stay in the tree but cannot receive new children.
A finite word is admissible when there is an active vertex before each step;
extinction at the final step is allowed. Write $H(w)$ for the final tree's
maximum distance from the root, including frozen vertices.

For $m\geq1$, let $p_m=+^m-^{m-1}$. This prefix leaves exactly two active
vertices. Concatenation of words is written by juxtaposition.

## Proposition 1.1(i)

For every real $A>0$, some integers $m\geq1$ and $n\geq0$ satisfy both

$$
\mathbb{E}[H(p_m(-,+)+^n)]+A\leq\mathbb{E}[H(p_m+^n)]
$$

and

$$
\mathbb{E}[H(p_m(-,+)+^n)]+A\leq\mathbb{E}[H(p_m+^{n+1})].
$$

Thus removing a freezing step followed by an attachment can increase expected
height by an arbitrarily large amount. Removing only that freezing step also
has this property, with the same witnesses. All three words are admissible.
The export is `FreezingGrowth.Paper.proposition_1_1_i`.

## Proposition 1.1(ii)

For every real $A>0$, some $m\geq1$ and $n\geq0$ satisfy

$$
\mathbb{E}[H(p_m(+,-)+^n)]+A\leq\mathbb{E}[H(p_m+^n)].
$$

Both words are admissible. Removing an attachment followed immediately by a
freezing step can therefore increase expected height by an arbitrarily large
amount. The export is `FreezingGrowth.Paper.proposition_1_1_ii`.

## Proposition 1.1(iii)

For some integer $n\geq0$,

$$
\mathbb{E}[H((+,+,-)+^n)]<\mathbb{E}[H((+,-)+^n)].
$$

Both words are admissible: removing just one attachment can increase expected
height. The export is `FreezingGrowth.Paper.proposition_1_1_iii`. The proof is
analytic; it does not certify a numerical witness at $n=13$. The library also
proves the stronger eventual reversal asserted later in the paper.

## Theorem 1.2

Let $\mathcal{X}_n$ be all admissible finite words with exactly $n$ attachment
steps. Uniformly over $w\in\mathcal{X}_n$, the probability that

$$
H(w)\geq e\log n-5\log\log n
$$

tends to one as $n\to\infty$. Also, for every sufficiently large $n$ and every
$w\in\mathcal{X}_n$,

$$
\mathbb{E}[H(w)]\geq e\log n-5\log\log n.
$$

The export `FreezingGrowth.Paper.theorem_1_2` contains both conclusions. The
uniform probability statement uses its epsilon formulation; the threshold in
the expectation statement is independent of the choice of word.

## Theorem 1.3

If $k\geq1$ and $w=+^k-\,v$ is admissible, remove the last attachment in its
initial positive run and the first freezing step. The resulting word
$\widehat w=+^{k-1}v$ is admissible and

$$
H(\widehat w)\preceq_{\mathrm{st}}H(w).
$$

Here stochastic domination means that every natural-height upper tail of the
left distribution is at most the corresponding upper tail on the right.
The statement includes $k=1$ and permits terminal extinction. Its export is
`FreezingGrowth.Paper.theorem_1_3`.

## Scope of the comparison

Five Lean exports cover these numbered results and their combined conclusions;
this count is not a count of inventory rows. The other library claims remain
proved and audited but are not separately selected by this Comparator
configuration. The five deliberate Challenge theorem placeholders specify the
statements only. `Solution.lean` imports the actual proofs and has no holes.
