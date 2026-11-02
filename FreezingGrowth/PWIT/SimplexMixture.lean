module

public import FreezingGrowth.PWIT.RankDensity
public import FreezingGrowth.PWIT.SimplexRadial
public import FreezingGrowth.PWIT.SimplexGrouped

/-!
# The common simplex bridge for every excess-rank class

The actual unnormalized rank mixture has a radial density on the nonnegative
orthant. Its normalized increments therefore have the iid exponential simplex
law, independently of their endpoint, for every excess rank `k`. The endpoint
has Gamma shape `d + k`; the class cardinality carries the entire mixture mass.

The probability measure below samples a rank tuple uniformly and then samples
its actual independent Gamma increments. No conditioning on a singleton
endpoint is used. These identities forget the rank tag and do not prove a
rank-barrier estimate.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal Classical

theorem rankIncrementMeasure_eq_radialSpacingMeasure (d k : ℕ) :
    rankIncrementMeasure d k = radialSpacingMeasure d
      (fun s => ENNReal.ofReal (Real.exp (-s) * s ^ k / k.factorial)) := by
  rw [rankIncrementMeasure_eq_withDensity]
  rfl

/-- The common bridge holds for all excess ranks, without a restriction `k ≤ d`. -/
theorem rankIncrementMeasure_normalized_joint_law (d k : ℕ) [NeZero d] :
    (rankIncrementMeasure d k).map (fun x => (normalizedSpacings x, totalWait x)) =
      (simplexLaw d).prod ((rankIncrementMeasure d k).map totalWait) := by
  rw [rankIncrementMeasure_eq_radialSpacingMeasure]
  exact radialSpacingMeasure_joint_law d (by fun_prop)

theorem rankWaitCount_eq_of_mem_antidiagonal {d k : ℕ} {r : Fin d → ℕ}
    (hr : r ∈ Finset.Nat.antidiagonalTuple d k) : rankWaitCount r = d + k := by
  have hs := Finset.Nat.mem_antidiagonalTuple.mp hr
  simp only [rankWaitCount, Finset.sum_add_distrib, hs, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, Nat.add_comm]

theorem map_incrementLaw_totalWait_gamma {d : ℕ} [NeZero d] (r : Fin d → ℕ) :
    (incrementLaw r).map totalWait = gammaMeasure (rankWaitCount r : ℝ) 1 := by
  have : IsProbabilityMeasure (gammaMeasure (rankWaitCount r : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (rankWaitCount_pos r)) (by norm_num)
  have h := congrArg (fun μ => μ.map Prod.snd) (incrementLaw_normalized_joint_law r)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
    measure_univ, one_smul] at h
  exact h

theorem rankIncrementMeasure_totalWait_gamma (d k : ℕ) [NeZero d] :
    (rankIncrementMeasure d k).map totalWait =
      ((Finset.Nat.antidiagonalTuple d k).card : ℝ≥0∞) • gammaMeasure ((d + k : ℕ) : ℝ) 1 := by
  have hm := measurable_totalWait d
  simp only [rankIncrementMeasure, ← Measure.mapₗ_apply_of_measurable hm, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hm, map_incrementLaw_totalWait_gamma]
  rw [Finset.sum_congr rfl (fun r hr => by rw [rankWaitCount_eq_of_mem_antidiagonal hr])]
  rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]

theorem rankIncrementMeasure_normalized_joint_gamma (d k : ℕ) [NeZero d] :
    (rankIncrementMeasure d k).map (fun x => (normalizedSpacings x, totalWait x)) =
      ((Finset.Nat.antidiagonalTuple d k).card : ℝ≥0∞) •
        ((simplexLaw d).prod (gammaMeasure ((d + k : ℕ) : ℝ) 1)) := by
  have : IsProbabilityMeasure (gammaMeasure ((d + k : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (by have hd := NeZero.pos d; omega)) (by norm_num)
  rw [rankIncrementMeasure_normalized_joint_law, rankIncrementMeasure_totalWait_gamma,
    Measure.prod_smul_right]

theorem antidiagonalTuple_card_pos (d k : ℕ) [NeZero d] :
    0 < (Finset.Nat.antidiagonalTuple d k).card := by
  apply Finset.card_pos.mpr
  refine ⟨fun i : Fin d => if i = 0 then k else 0, ?_⟩
  rw [Finset.Nat.mem_antidiagonalTuple]
  simp

theorem rankIncrementMeasure_univ (d k : ℕ) :
    rankIncrementMeasure d k univ = (Finset.Nat.antidiagonalTuple d k).card := by
  simp only [rankIncrementMeasure, Measure.finsetSum_apply, measure_univ,
    Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Uniformly choose a rank tuple from the finite excess-rank class, then
sample the actual path increments with that tuple. -/
noncomputable def uniformRankIncrementLaw (d k : ℕ) : Measure (Fin d → ℝ) :=
  ((Finset.Nat.antidiagonalTuple d k).card : ℝ≥0∞)⁻¹ • rankIncrementMeasure d k

instance uniformRankIncrementLaw_isProbabilityMeasure (d k : ℕ) [NeZero d] :
    IsProbabilityMeasure (uniformRankIncrementLaw d k) where
  measure_univ := by
    rw [uniformRankIncrementLaw, Measure.smul_apply, rankIncrementMeasure_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast (antidiagonalTuple_card_pos d k).ne')
      (by finiteness)

/-- The actual uniform rank mixture has the same normalized bridge for every
excess rank, and its independent endpoint is Gamma `(d + k, 1)`. -/
theorem uniformRankIncrementLaw_normalized_joint_law (d k : ℕ) [NeZero d] :
    (uniformRankIncrementLaw d k).map (fun x => (normalizedSpacings x, totalWait x)) =
      (simplexLaw d).prod (gammaMeasure ((d + k : ℕ) : ℝ) 1) := by
  rw [uniformRankIncrementLaw, Measure.map_smul _ (by fun_prop),
    rankIncrementMeasure_normalized_joint_gamma, smul_smul,
    ENNReal.inv_mul_cancel (by exact_mod_cast (antidiagonalTuple_card_pos d k).ne')
      (by finiteness), one_smul]

theorem uniformRankIncrementLaw_map_normalizedSpacings (d k : ℕ) [NeZero d] :
    (uniformRankIncrementLaw d k).map normalizedSpacings = simplexLaw d := by
  have : IsProbabilityMeasure (gammaMeasure ((d + k : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (by have hd := NeZero.pos d; omega)) (by norm_num)
  have h := congrArg (fun μ => μ.map Prod.fst) (uniformRankIncrementLaw_normalized_joint_law d k)
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod,
    measure_univ, one_smul] at h
  exact h

theorem uniformRankIncrementLaw_map_totalWait (d k : ℕ) [NeZero d] :
    (uniformRankIncrementLaw d k).map totalWait = gammaMeasure ((d + k : ℕ) : ℝ) 1 := by
  have : IsProbabilityMeasure (gammaMeasure ((d + k : ℕ) : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (by have hd := NeZero.pos d; omega)) (by norm_num)
  have h := congrArg (fun μ => μ.map Prod.snd) (uniformRankIncrementLaw_normalized_joint_law d k)
  rw [Measure.map_map measurable_snd (by fun_prop), Measure.map_snd_prod,
    measure_univ, one_smul] at h
  exact h

theorem uniformRankIncrementLaw_normalized_independent_total (d k : ℕ) [NeZero d] :
    IndepFun (@normalizedSpacings d) totalWait (uniformRankIncrementLaw d k) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_normalizedSpacings d).aemeasurable
    (measurable_totalWait d).aemeasurable).mpr
  rw [uniformRankIncrementLaw_map_normalizedSpacings, uniformRankIncrementLaw_map_totalWait]
  exact uniformRankIncrementLaw_normalized_joint_law d k

end FreezingGrowth.PWIT
