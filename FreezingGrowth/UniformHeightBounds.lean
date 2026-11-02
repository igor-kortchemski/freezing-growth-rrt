module

public import FreezingGrowth.PWIT.GlobalSecondMoment
public import FreezingGrowth.HighPopulationAssembly

/-! Unconditional uniform height bounds. The actual clock success estimate
is transported to the actual RRT laws, then combined with both population
branches. The corrected high-population index and extinction endpoints are
retained by the existing assembly. -/

@[expose] public section
namespace FreezingGrowth

theorem uniformHeightClaims : UniformHeightProbabilityClaim ∧ UniformHeightExpectationClaim :=
  uniformHeightClaims_of_seed (RRT.constantSuccessSeed_of_clockLowerSeed PWIT.clockLowerSeed)

theorem uniformHeightProbabilityClaim : UniformHeightProbabilityClaim := uniformHeightClaims.1

theorem uniformHeightExpectationClaim : UniformHeightExpectationClaim := uniformHeightClaims.2

end FreezingGrowth
