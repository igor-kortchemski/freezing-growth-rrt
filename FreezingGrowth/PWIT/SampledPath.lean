module

public import FreezingGrowth.PWIT.Increments
public import FreezingGrowth.PWIT.RankCounts

/-!
# The finite rank-class mixture of actual path increments

We retain the unnormalized sum of path laws. Its mass is the number of paths,
so division-free identities immediately translate to the uniform sampled
path. Permutation invariance holds only after summing the whole rank class.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def tupleIncrement {d : ℕ} (r : Fin d → ℕ) (ω : Sample) (i : Fin d) : ℝ :=
  childDelay ω ((List.ofFn r).take i) (r i)

@[fun_prop] theorem measurable_tupleIncrement {d : ℕ} (r : Fin d → ℕ) :
    Measurable (tupleIncrement r) :=
  Measurable.of_eval fun _ => measurable_childDelay _ _

theorem birth_ofFn_eq_sum_tupleIncrement {d : ℕ} (r : Fin d → ℕ) (ω : Sample) :
    birth ω (List.ofFn r) = ∑ i, tupleIncrement r ω i := by
  rw [birth_eq_sum_pathIncrement]
  apply Fintype.sum_equiv (finCongr List.length_ofFn)
  intro i
  simp [pathIncrement, tupleIncrement]
  apply congrArg (childDelay ω ((List.ofFn r).take i))
  apply congrArg r
  exact Fin.ext rfl

noncomputable def incrementLaw {d : ℕ} (r : Fin d → ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => gammaMeasure ((r i : ℝ) + 1) 1

instance incrementLaw_isProbabilityMeasure {d : ℕ} (r : Fin d → ℕ) :
    IsProbabilityMeasure (incrementLaw r) := by
  let (i : Fin d) : IsProbabilityMeasure (gammaMeasure ((r i : ℝ) + 1) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  unfold incrementLaw
  infer_instance

theorem map_tupleIncrement {d : ℕ} (r : Fin d → ℕ) :
    law.map (tupleIncrement r) = incrementLaw r := by
  let sums : (Fin d → ℕ → ℝ) → Fin d → ℝ :=
    fun rows i => ∑ j ∈ Finset.range (r i + 1), rows i j
  have hs : Measurable sums := by unfold sums; fun_prop
  have he : tupleIncrement r =
      sums ∘ (fun (ω : Sample) (i : Fin d) j => ω ((List.ofFn r).take i, j)) := rfl
  rw [he, ← Measure.map_map hs (by fun_prop),
    map_pathRows_of_length (List.ofFn r) d List.length_ofFn]
  dsimp only [sums]
  rw [Measure.infinitePi_map_pi (μ := fun _ : Fin d => rowLaw)
    (f := fun i (x : ℕ → ℝ) => ∑ j ∈ Finset.range (r i + 1), x j)
    (by intro i; fun_prop)]
  rw [Measure.infinitePi_eq_pi]
  simp only [map_row_sum, incrementLaw]

def permuteIncrements {d : ℕ} (e : Fin d ≃ Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => x (e i)

@[fun_prop] theorem measurable_permuteIncrements {d : ℕ} (e : Fin d ≃ Fin d) :
    Measurable (permuteIncrements e) :=
  Measurable.of_eval fun i => measurable_pi_apply (e i)

theorem map_incrementLaw_permute {d : ℕ} (r : Fin d → ℕ) (e : Fin d ≃ Fin d) :
    (incrementLaw r).map (permuteIncrements e) = incrementLaw (r ∘ e) := by
  let (i : Fin d) : IsProbabilityMeasure (gammaMeasure ((r (e i) : ℝ) + 1) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  change (Measure.pi (fun i => gammaMeasure ((r i : ℝ) + 1) 1)).map
    (fun x i => x (e i)) = Measure.pi (fun i => gammaMeasure ((r (e i) : ℝ) + 1) 1)
  simpa [MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft, Equiv.piCongrLeft', Function.comp_def] using
    Measure.pi_map_piCongrLeft e.symm
      (fun i => gammaMeasure ((r (e i) : ℝ) + 1) 1)

noncomputable def rankIncrementMeasure (d k : ℕ) : Measure (Fin d → ℝ) :=
  ∑ r ∈ Finset.Nat.antidiagonalTuple d k, incrementLaw r

instance rankIncrementMeasure_isFiniteMeasure (d k : ℕ) :
    IsFiniteMeasure (rankIncrementMeasure d k) := by
  unfold rankIncrementMeasure
  infer_instance

theorem rankIncrementMeasure_eq_sum_actual (d k : ℕ) :
    rankIncrementMeasure d k =
      ∑ r ∈ Finset.Nat.antidiagonalTuple d k, law.map (tupleIncrement r) := by
  simp only [map_tupleIncrement, rankIncrementMeasure]

theorem rankIncrementMeasure_permutation (d k : ℕ) (e : Fin d ≃ Fin d) :
    (rankIncrementMeasure d k).map (permuteIncrements e) = rankIncrementMeasure d k := by
  classical
  have hm := measurable_permuteIncrements e
  simp only [rankIncrementMeasure, ← Measure.mapₗ_apply_of_measurable hm, map_sum]
  simp only [Measure.mapₗ_apply_of_measurable hm, map_incrementLaw_permute]
  apply Finset.sum_bij (fun r _ => r ∘ e)
  · intro r hr
    rw [Finset.Nat.mem_antidiagonalTuple] at hr ⊢
    simpa only [Function.comp_def, Equiv.sum_comp] using hr
  · intro r _ s _ hrs
    funext i
    have h := congrFun hrs (e.symm i)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h
  · intro s hs
    refine ⟨s ∘ e.symm, ?_, ?_⟩
    · rw [Finset.Nat.mem_antidiagonalTuple] at hs ⊢
      simpa only [Function.comp_def, Equiv.sum_comp] using hs
    · funext i
      simp
  · intro r _
    rfl

theorem sum_permuteIncrements {d : ℕ} (e : Fin d ≃ Fin d) (x : Fin d → ℝ) :
    (∑ i, permuteIncrements e x i) = ∑ i, x i := by
  exact e.sum_comp x

end FreezingGrowth.PWIT
