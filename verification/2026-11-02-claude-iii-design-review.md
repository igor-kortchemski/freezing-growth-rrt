# Independent III1 design review

Claude Sonnet 5.5, High, read-only. No compilation. CLI exit zero; is_error false; no permission denials. Design findings, not final statement/proof certification.

# Design review: full-tree III1 (`main.tex` 557–625)

This is a read-only review and nothing was compiled. I did not read `TwoSeedGraftPrefix.lean`. The target declarations don't exist yet, so this covers design only.

## 1. Does the source need a joint prefix law? No.

Everything the source asserts about the coupling is marginal.

- **Coupling sentence (567–568).** The text says only that T(X) is obtained from T(+1,+1,−1) by grafting T¹ₙ₊₁ and T²ₙ₊₁. It says the same for T(X̂) with T¹ₙ and T²ₙ. It gives no joint law for the two prefixes, and no statement links them.
- **Figure (577, `fig-freezing2.pdf`).** The T(x) column has probabilities 1/6, 1/6, 1/6, 1/3, 1/6 and the T(x̂) column has 1/2, 1/2. Each column sums to 1 separately, so these are per-word marginals. I re-derived them from Algorithm 1:
  - [t,t,f] has parent(2)∈{0,1} with probability 1/2 each, then one of three vertices frozen with probability 1/3 each.
  - The 1/3 cell merges the two atoms "star, leaf frozen".
  - [t,f,t] has probability 1/2 for each frozen vertex.
- **Expectation identities (593–608, 615–621, 627–634).** Each is an expectation over one prefix configuration, independent of its own (T¹,T²). They are combined only linearly.
- **Exchangeability and RRT increment (622–626, 642–649).** These use only the marginals of Rₙ and Rₙ₊₁.

So independent sampling of the two prefixes is faithful. It is also arbitrary: any coupling of the two prefixes with the right marginals, independent of the master, gives the same source content. The report should say that the source specifies no joint law, that the product was chosen, and that no claim depends on the choice.

If it is cheap, state the sample law for an arbitrary coupling π of the prefix laws and take the product as an instance. I would not build anything beyond that.

**Real requirements.**
- The master must be independent of each prefix, which the product structure gives.
- The same master (one parent array) must supply both replays. The source writes Rₙ and Rₙ₊₁ with Tⁱₙ, Tⁱₙ₊₁ and uses `eq:HeightIncrease` (642–646), which presupposes the nested RRT sequence. Independent masters would pass every law-level claim but would lose the nesting. Your shared-master proposal is the right reading.

## 2. Checks on the proposed construction

- **Master indexing.** The long word uses `replay … n` on `treeLaw allAttach (n+1)`. This matches `masterTree_replay_law` (`TwoSeedGraftLaw.lean:115`).
  - The short word uses `replay … (n−1)` with the same master.
  - `word_two_seed_master_law_of_le` (`MasterPrefix.lean:145`) needs `(n−1)+1 ≤ n+1`, which holds with m = n+1.
  - `masterTree_replay_prefix_succ` is correct: `replay_congr` reads only parents 2..n+1, and the new master edge updates parent(m+1).
- **Seeds.** `birthOrderedFirst/SecondSeed` and the two `*_active_card` lemmas exist (`TwoSeedGraftOrderedSeeds.lean:13–94`), so `hseed` follows from `birthOrderedSeed_spec`.
  - `embedding 0 = first = min`, so the root side T¹ goes to the earlier-born seed and T² to the later one. This matches 567–568.
  - **Do not reuse** `Sample`, `stateSampleLaw` or `sampleLaw` (`TwoSeedGraftSample.lean:14–28`). They use `uniformRootPair`, a random orientation. The marginals would still be correct, because `masterTree_replay_law` holds for any ordered pair. But the pathwise coupling would no longer put T¹ on the earlier vertex.
  - The II1 "(new child, first)" orientation does not apply here either.
- **Vertex IDs are birth times.** In [t,f,t] the third vertex has ID 3, so active is {0,3} or {1,3}. In [t,t,f] it has ID 2. Both prefixes have T = 3, so new IDs 4, 5, … coincide across the two trees, and master vertex j ≥ 2 gets ID j+2 in both. Nothing may assume "vertex 2" is the same vertex in both prefixes.
- **Word identification.** The source's X̂ = (+1,−1)(+1)ⁿ equals `[t,f,t] ++ replicate (n−1) true` only for n ≥ 1.
  - At n = 0, ℕ-subtraction would silently produce (+1,−1,+1). The inventory already restricts to n ≥ 1.
  - Parametrize the short word by k with n = k+1, or hypothesise `1 ≤ n`, and prove the list equality for both `toSigns` and `length`.
- **Old and frozen data.** `replay_parent_old`, `replay_height_old`, `replay_frozenAt_old` and `replay_frozenAt_new` (`Geometry.lean:35–84`) are exactly what the full-tree height needs. In `max(2, H(T¹), 1+H(T²))` (601), the frozen old leaf at depth 2 contributes to the height.

## 3. Minimal source-faithful construction

- **Sample space.** A record `⟨long, short, master⟩` with discrete σ-algebra. Define
  `law n := μL.bind (fun a => μS.bind (fun b => (treeLaw allAttach (n+1)).map (⟨a,b,·⟩)))`
  with μL = `treeLaw [t,t,f].toSigns 3` and μS = `treeLaw [t,f,t].toSigns 3`.
- **Replays.** `longTree = replay a 3 (u a) (v a) r.parent n` and `shortTree = replay b 3 (u b) (v b) r.parent (n−1)`.
- **Marginals.** Marginalize the unused coordinate by `Measure.bind_const`, as in `stateSampleLaw_baseline`. Then apply `word_two_seed_master_law_of_le` directly.
- **Histories.** Source III1 (557–625) mentions no history. The full State, including parent, height, `frozenAt`, `graph`, `vertices` and `active`, is the whole tree. The replay-history lemmas already exist if wanted. The prefix-history concatenation in `TwoSeedGraftIndependence.lean` is II1 work and is not needed here. That file now holds definitions only, and the handover is stale on this point.

## 4. Exact missing claims

**M1. Sample law and marginals.**
- Probability instance for the sample law.
- A.e. validity of the sample.
- `map longTree = treeLaw ([t,t,f] ++ rep n)` and `map shortTree = treeLaw ([t,f] ++ rep n)`, with the list rewrite for n ≥ 1.
- Product-form facts for (long, master) and (short, master).

**M2. Prefix configuration table.** This is the figure's content and is not currently stated at full-State level.
- For [t,t,f]: the pushforward by (parent 2, frozen vertex, active pair) has six atoms of mass 1/6.
- For [t,f,t]: two atoms of mass 1/2.
- Each atom carries its active pair in ID order.
- The existing profile tables (`SeededWordLaw.long_prefix_table`, I did not inspect them in detail) are height-level. They do not certify this claim.

**M3. Graph for the short replay.** `replay_graph_split` (`Components.lean:71–83`) requires `Describes n r (split n r)` and `ValidAt (n+1) r` at the same n as the replay count. That does not fit a short replay on a larger master.
- The needed statement is `replay_graph` followed by `graftEdges_eq_components` (`Components.lean:36–38`). That lemma needs only `p j < j` for 2 ≤ j ≤ n+1.
- Add this as a prefix-length corollary: `(replay … r.parent k).graph = s.graph ⊔ (split k r).root.mapped.map emb ⊔ (split k r).child.mapped.map emb`.
- The a.e. `p j < j` follows from `treeLaw_valid`.

**M4. Components of Rₙ and Rₙ₊₁.**
- Rₙ₊₁'s components are `split n r`, with `Describes n r (split n r)` a.e. This is `treeLaw_split_describes`, which exists.
- Rₙ's components must be `split (n−1)` of an actual RRT with n edges. The master has n+1 edges, so its `Describes` is for the wrong index.
- Needed lemma: `(treeLaw (m)).map (split k) = (treeLaw (k+1)).map (split k)` for k+1 ≤ m. It is a clone of `masterTree_replay_prefix_of_le`, since `split` reads only the parent array.
- For a pathwise Rₙ, add `rrtPrefix n r` as the deterministic attach chain from `initial` along `r.parent`, with:
  - `map (rrtPrefix n) (treeLaw (n+1)) = treeLaw n`;
  - `split (n−1) (rrtPrefix n r) = split (n−1) r`;
  - hence `Describes (n−1) (rrtPrefix n r) (split (n−1) r)` a.e.

  Without it, the identification is law-level only. That is probably adequate for the source's expectation arguments, but the pathwise nesting is closer to 564–569.

**M5. Statement assembly.** One theorem collecting:
- marginals;
- seed rule and component assignment (T¹ at `min`, T² at `max`);
- old-data preservation (`replay_*_old`);
- new-vertex parents and `frozenAt = none`;
- graph formulas (M3 and `replay_graph_split`);
- Rₙ and Rₙ₊₁ components (M4).

Record n ≥ 1 and the product choice.

## 5. Not required, and risks

- The prefix–prefix joint law.
- Histories, which are II1 only.
- Random orientation.
- Re-deriving III3–III7 at full-tree level. The existing height proofs cover them, but they do not close III1.
- Check the import closure: `TwoSeedGraftOrderedSeeds.lean` imports `MainStatements`, and the new modules lie outside the root closure.

## 6. Source ambiguities to record

- 564 says "couple T(X̂), T(X) and Rₙ", while T(X) uses Rₙ₊₁. Nesting is implied by 642–646, not stated.
- The 1/3 cell merges two atoms.
- Line 539 refers to (ii) where it means (i). This is already noted in the audit, and it is outside III1.