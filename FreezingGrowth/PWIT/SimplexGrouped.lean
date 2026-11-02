module

public import FreezingGrowth.PWIT.SimplexLinear
public import FreezingGrowth.PWIT.SampledPath

/-!
# The normalized bridge of a fixed child-rank tuple

Each child delay groups `r i + 1` actual exponential waits. Regrouping the
finite independent clocks gives the product Gamma increment law, and the
sum-preserving linear bridge gives independence from the common endpoint.
The angular measure depends on the rank tuple; it is not the uniform simplex
law in the number of edges.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def rankWaitCount {d : ℕ} (r : Fin d → ℕ) : ℕ := ∑ i, (r i + 1)

abbrev RankWaitIndex {d : ℕ} (r : Fin d → ℕ) := (i : Fin d) × Fin (r i + 1)

noncomputable def rankWaitEquiv {d : ℕ} (r : Fin d → ℕ) :
    RankWaitIndex r ≃ Fin (rankWaitCount r) :=
  Fintype.equivFinOfCardEq (by simp [rankWaitCount, RankWaitIndex])

theorem rankWaitCount_pos {d : ℕ} [NeZero d] (r : Fin d → ℕ) : 0 < rankWaitCount r :=
  Finset.sum_pos (fun i _ => Nat.succ_pos (r i)) Finset.univ_nonempty

noncomputable def groupRankWaits {d : ℕ} (r : Fin d → ℕ) :
    (Fin (rankWaitCount r) → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun x i := ∑ j : Fin (r i + 1), x (rankWaitEquiv r ⟨i, j⟩)
  map_add' x y := by ext i; simp [Finset.sum_add_distrib]
  map_smul' c x := by ext i; simp [Finset.mul_sum]

theorem totalWait_groupRankWaits {d : ℕ} (r : Fin d → ℕ) (x : Fin (rankWaitCount r) → ℝ) :
    totalWait (groupRankWaits r x) = totalWait x := by
  change (∑ i, ∑ j : Fin (r i + 1), x (rankWaitEquiv r ⟨i, j⟩)) = ∑ a, x a
  calc
    _ = ∑ p : RankWaitIndex r, x (rankWaitEquiv r p) :=
      (Fintype.sum_sigma (fun p : RankWaitIndex r => x (rankWaitEquiv r p))).symm
    _ = _ := (rankWaitEquiv r).sum_comp x

theorem map_rankWaitRows {d : ℕ} (r : Fin d → ℕ) :
    (finiteClockLaw (rankWaitCount r)).map
      (fun x (i : Fin d) (j : Fin (r i + 1)) => x (rankWaitEquiv r ⟨i, j⟩)) =
        Measure.pi (fun i => finiteClockLaw (r i + 1)) := by
  have hi : (finiteClockLaw (rankWaitCount r)).map
      (fun x (p : RankWaitIndex r) => x (rankWaitEquiv r p)) =
        Measure.pi (fun _ : RankWaitIndex r => clockLaw) := by
    simpa only [finiteClockLaw, Measure.infinitePi_eq_pi] using
      (Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : Fin (rankWaitCount r) => clockLaw)
        (rankWaitEquiv r).injective)
  have hc := Measure.infinitePi_map_piCurry (fun (i : Fin d) (_ : Fin (r i + 1)) => clockLaw)
  simp only [Measure.infinitePi_eq_pi] at hc
  rw [← hi, Measure.map_map (by fun_prop) (by fun_prop)] at hc
  exact hc

theorem map_groupRankWaits {d : ℕ} (r : Fin d → ℕ) :
    (finiteClockLaw (rankWaitCount r)).map (groupRankWaits r) = incrementLaw r := by
  let rows : (Fin (rankWaitCount r) → ℝ) → (i : Fin d) → Fin (r i + 1) → ℝ :=
    fun x i j => x (rankWaitEquiv r ⟨i, j⟩)
  let sums : ((i : Fin d) → Fin (r i + 1) → ℝ) → Fin d → ℝ :=
    fun x i => totalWait (x i)
  have he : (groupRankWaits r : (Fin (rankWaitCount r) → ℝ) → Fin d → ℝ) = sums ∘ rows := rfl
  rw [he, ← Measure.map_map (by unfold sums; fun_prop) (by unfold rows; fun_prop),
    map_rankWaitRows r]
  rw [Measure.pi_map_pi (f := fun i => @totalWait (r i + 1))
    (fun i => (measurable_totalWait (r i + 1)).aemeasurable)]
  simp only [map_totalWait_gamma, incrementLaw, Nat.cast_add, Nat.cast_one]

/-- The actual normalized Gamma-increment bridge for this fixed rank tuple. -/
noncomputable def rankSimplexLaw {d : ℕ} (r : Fin d → ℕ) : Measure (Fin d → ℝ) :=
  (simplexLaw (rankWaitCount r)).map (groupRankWaits r)

instance rankSimplexLaw_isProbabilityMeasure {d : ℕ} (r : Fin d → ℕ) :
    IsProbabilityMeasure (rankSimplexLaw r) := by
  unfold rankSimplexLaw
  infer_instance

theorem incrementLaw_normalized_joint_law {d : ℕ} [NeZero d] (r : Fin d → ℕ) :
    (incrementLaw r).map (fun x => (normalizedSpacings x, totalWait x)) =
      (rankSimplexLaw r).prod (gammaMeasure (rankWaitCount r : ℝ) 1) := by
  have : NeZero (rankWaitCount r) := ⟨(rankWaitCount_pos r).ne'⟩
  rw [← map_groupRankWaits r,
    Measure.map_map (by fun_prop) (groupRankWaits r).continuous_of_finiteDimensional.measurable]
  have he : (fun x => (normalizedSpacings x, totalWait x)) ∘ groupRankWaits r =
      (fun x => (normalizedSpacings (groupRankWaits r x), totalWait x)) := by
    funext x
    simp only [Function.comp_apply, totalWait_groupRankWaits]
  rw [he]
  exact normalizedSpacings_linear_joint_law (rankWaitCount r) d
    (groupRankWaits r) (totalWait_groupRankWaits r)

/-- Normalizing independent Gamma block totals is an exact sampling
representation of the grouped simplex bridge. -/
theorem rankSimplexLaw_eq_normalized_incrementLaw {d : ℕ} [NeZero d] (r : Fin d → ℕ) :
    rankSimplexLaw r = (incrementLaw r).map normalizedSpacings := by
  have : IsProbabilityMeasure (gammaMeasure (rankWaitCount r : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (rankWaitCount_pos r)) (by norm_num)
  have h := congrArg (fun ν => ν.map Prod.fst) (incrementLaw_normalized_joint_law r)
  rw [Measure.map_map measurable_fst (by fun_prop), Measure.map_fst_prod,
    measure_univ, one_smul] at h
  exact h.symm

theorem tupleIncrement_normalized_joint_law {d : ℕ} [NeZero d] (r : Fin d → ℕ) :
    law.map (fun ω => (normalizedSpacings (tupleIncrement r ω), totalWait (tupleIncrement r ω))) =
      (rankSimplexLaw r).prod (gammaMeasure (rankWaitCount r : ℝ) 1) := by
  rw [← incrementLaw_normalized_joint_law r, ← map_tupleIncrement r,
    Measure.map_map (by fun_prop) (measurable_tupleIncrement r)]
  rfl

end FreezingGrowth.PWIT
