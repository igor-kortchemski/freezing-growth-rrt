# Manuscript recommendations

The initial independent source audit identified the following issues. The
original TeX remains unchanged. Detailed obligations and proof status are in
`FORMALIZATION_REPORT.md`; these findings do not refute the main theorems.

| ID | Location in `main.tex` | Category | Finding and proposed correction |
| --- | --- | --- | --- |
| SF1 | Line 617, event $C_{n+1}$ | Correctness | The height term must be that of the first subtree, not the second. `weightedHeightCore_cases` and `heightMixture_eq_height_add_corrections` prove the corrected scalar identity; `printed_C_case_counterexample` shows failure of the printed scalar expression at heights $3$ and $0$. Probability coupling remains a separate obligation. |
| SF2 | Lines 902–906, high values | Correctness | An active population of $r_n$ guarantees a pure-attachment prefix of length $r_n-1$, not $r_n$, because the walk starts at one. Use the corrected RRT index and verify the same asymptotic estimates. |
| SF3 | Lines 917–919, low values | Correctness | The admissible family permits terminal extinction, so a final active vertex need not exist. If the terminal active count is zero, delete its final freezing step; the preceding count is one and the height law and attachment count are unchanged. On the surviving prefix, reciprocal population parameters may be assigned at every step, with only attachment coordinates summed. |
| SF4 | Line 648 | Correctness | Replace the assertion about convergence to $\log n$ with the precise relative statement $h(U_n)/\log n\to1$ in probability, or the sufficient relative upper-tail bound. |
| SF5 | Line 461 | Correctness | The two sides of the displayed event inclusion must use the same independent-copy superscript. Alternatively state a probability inequality using equality of laws. |
| SF6 | Line 798 | Clarity affecting proof | Specify the comparison-process filtration for the delayed pair's conditional uniformity. A previously sampled pair cannot be independent of the entire joint construction's past. Prove the needed marginal statement. |
| SF7 | Lines 237–242, citation for `eq:H` | Citation precision | PS22 Eq. (1.3) states an upper-tail tightness conclusion in its discussion of random weights; it does not by itself give the displayed mean expansion. Cite AF13 Corollary 1.3 for the mean and centered exponential tails, and PS22 Theorem 1.1 for its tightness statement specialized to unit weights. This does not invalidate `eq:H`; its Lean obligations E1/E2 remain pending. |

SF7 was checked against [PS22 §1.2](https://arxiv.org/pdf/2101.01156) and
[AF13 Corollary 1.3, published version](https://arxiv.org/pdf/1012.2544v3)
during the M2 planning review on 31 October 2026.

Minor corrections: the reference at line 539 should point to item (i); line 763
has an inconsistent forest-time index; line 235 uses a superscript instead of a
subscript for the sequence family. State $n\geq1$ for the star-probability
formulas, which do not hold at $n=0$.
