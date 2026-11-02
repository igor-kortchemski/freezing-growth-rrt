# Scaling-limit adaptation provenance

This local adaptation is a candidate for E9 in the freezing-growth manuscript.
The original scaling modules are from the sibling `freezing2`; its README
stated that a repository license for its new code had not yet been selected
when the source was inspected. On 29 October 2026, the user explicitly
authorized Apache-2.0 for the reused `freezing2` scaling proof code in this
project. This authorization covers this local adaptation; it does not change
or assert a global license for the sibling repository. The local adaptation
is distributed under this project's Apache-2.0 license.

The selected companion analytic fragments are from the Apache-2.0 `freezing1`
project, copyright 2026 Igor Kortchemski; its retained notices are already
recorded in this repository's NOTICE. No manuscript text is copied.

## Transformations and model identity

The seventeen adapted scaling modules preserve their proof bodies except for exact
namespace/import substitutions: `Freezing2` becomes `FreezingGrowth.Scaling`,
local imports use the listed `Scaling*.lean` filenames, and companion model
references `Freezing1` use this project's existing `FreezingGrowth` declarations.
The companion maximum-limit invocation uses `FreezingGrowth.Scaling`'s proved
limit theorem. Module comments identify the current E9 obligation and the existing
forward model. No second State/tree law is defined. Fresh normalized source
comparisons found the six common Path/Extinction/ForwardTree/ForwardLaw/
ForwardHeight/HeightScale bodies identical after import/namespace/comment
normalization. The two projects have matching Lean4.35.0/dependency revisions.

Two companion analytic modules are assembled from the exact fragments below.
They reuse existing maximum definitions, finite upper/lower tails, concentration,
and rate definitions rather than duplicating the tree model or broad limit
closure. These transformations require new local build and axiom evidence;
none is inferred from sibling artifacts.

`ScalingVertices.lean` is newly authored in this project. It proves the
almost-everywhere identification with the actual state's vertex count, the
limit $|T_n|/n \to 1/2$, and transports the operation-index height theorem to
the actual vertex denominator. The limiting constant is multiplied by
$2^{1-\alpha}$. It uses the existing tree-count theorem and the adapted
reciprocal-profile population estimate; no source proof is copied into this
wrapper.

## Source identities and exact reused scope

| Original source | Destination | Original SHA-256 | Reused scope |
| --- | --- | --- | --- |
| `local sibling checkout: freezing2/Freezing2/Analysis/HarmonicAsymptotics.lean` | `ScalingHarmonicAsymptotics.lean` | `e1da42225343d70a3aa2c29519737a07129b81baef0fdf439e76005c2d11a6df` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/HarmonicConclusions.lean` | `ScalingHarmonicConclusions.lean` | `c217ab439ef10c5efc35f23f17f5bbaeb004078a681d6ba609b9cf29fb18f3c8` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/HeightNormalization.lean` | `ScalingHeightNormalization.lean` | `f3a4a2b50256d72abf0399b94c84a51e661b98e88629cba69f871894713622d4` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/LocalL1.lean` | `ScalingLocalL1.lean` | `bcddf79dc929f839ff67638f1389d3f1ffdee41cfa7327ce88748e34b6e2d2c7` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/LpScaling.lean` | `ScalingLpScaling.lean` | `ac439fac409f266de9b5b78f5f66f95803943fc2630f4615037da39994166315` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/PopulationProfile.lean` | `ScalingPopulationProfile.lean` | `4a9d2a932040c3a9fb7dfc16ee7cdb1c1b845606e01b690be67a3e2c23e4c4bd` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/ProfileCorrection.lean` | `ScalingProfileCorrection.lean` | `a6229ce999378b1e3cf968b9a2e45f7feaa195880397b268088207c89ba61961` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/ProfileIntegrals.lean` | `ScalingProfileIntegrals.lean` | `2b97666b65ae5e6adf5b38e0c8c9a7928e03e30b5f30beb0f46087b9d313a2e0` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/ReciprocalCorrection.lean` | `ScalingReciprocalCorrection.lean` | `4d509ce7d469545063f995cfbaeaed4de90ee7e3e9e9e2276eac0cc44421397f` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/SourceHypotheses.lean` | `ScalingSourceHypotheses.lean` | `b0d61563a8719a128e06de98a9d38855ac5b52f63a2bc2c4cea40e350c7683ad` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/StepProfile.lean` | `ScalingStepProfile.lean` | `e27fc1255faa5268d2d1d5ae869d70d4d6fdec31206c63435c6b195a1a9f03b8` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Analysis/SublinearPopulation.lean` | `ScalingSublinearPopulation.lean` | `af7ea290bc0a13f539c6d3986c6f0ed45b40b5d4c3b60bbdb144bbcf9da319d9` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Discrete/Estimates.lean` | `ScalingEstimates.lean` | `2731eec6501e150f60ae7592c7d88d57e95638365c74e9287f6990b0f1f752e2` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Discrete/Walk.lean` | `ScalingWalk.lean` | `5bbc02bb258cf9a0370bbe6a50c3e34323cea6f485720d713cf195b899b33d74` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Discrete/WeightedWalk.lean` | `ScalingWeightedWalk.lean` | `5c442fb7c3bbc24f7bf8b38a2b305b9166b4669075b555c8b894eaa20a3ea4a9` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/MainResults/Height.lean` | `ScalingHeight.lean` | `13ffe644aa2e923f746c2b17c7a867ae052e6666e23894df63725c2cb4b17904` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing2/Freezing2/Probability/CompanionModel.lean` | `ScalingModel.lean` | `7486b154f49225ad5a29f6147355a5833ca6a500358839663122236d966df70e` | Whole module; only imports/namespaces/model references and provenance comment changed. |
| `local sibling checkout: freezing1/Freezing1/BernoulliArrayLimits.lean` | `ScalingMomentLimits.lean` | `df99d39f04f8d229ff13ee2c939cff77a36100cb44629bd08196bf608fdc9ec8` | eLpNorm_le_cutoff_add_tail; tendsto_eLpNorm_of_tail_and_higher_moment |
| `local sibling checkout: freezing1/Freezing1/MGFLimits.lean` | `ScalingMomentLimits.lean` | `d032302835691d582a427ae5bb8dae286fda760fdb0db7a6b363c3a4f9344c92` | normalized_exp_integrable |
| `local sibling checkout: freezing1/Freezing1/MaximumMGFLimits.lean` | `ScalingMomentLimits.lean` | `bbe5f0e5d7eda88bd46acf2e633d591c23d2f9b69277565941b7e6933ff811e8` | normalized_exp_integral_le_of_exp_bound through normalized_tendsto_Lp_of_eventual_exp_bound |
| `local sibling checkout: freezing1/Freezing1/RateFunction.lean` | `ScalingMaximumLimits.lean` | `d4117c3fc3bd6f269d9c5de7c7a3a4b5be58deab2ccc002ec10e13ea171282c1` | heightRate/continuous/derivative/monotonicity helpers; Bennett relation and monotonicity only |
| `local sibling checkout: freezing1/Freezing1/HeightAsymptotics.lean` | `ScalingMaximumLimits.lean` | `ae2f8c0d617bee6db785852c16bc6730b94362c0508c6b2ac6b0957368c40a98` | all five logarithmic-prefactor lemmas |
| `local sibling checkout: freezing1/Freezing1/ForwardMaximum.lean` | `ScalingMaximumLimits.lean` | `9475945570b7d97ab8709acec6f824cee652106e1a12ed346ed7f0c89f4d04c1` | treeHeight_mgf_one_le only |
| `local sibling checkout: freezing1/Freezing1/MainMaximum.lean` | `ScalingMaximumLimits.lean` | `acb4d8811b54abb1fea6ec04a55500eaaaa71c9eb964f6460a1ce52ae841e1c1` | normalized lower/upper tails; lower/upper probability limits; deviation limit; Lp limit; excludes universal-e window |
