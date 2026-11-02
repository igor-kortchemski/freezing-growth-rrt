module

public import FreezingGrowth.BernoulliOrder
public import FreezingGrowth.FiniteActiveHeight

/-!
# Stochastic lower bounds from a uniform active vertex

A uniform active vertex is no higher than its tree maximum. Together with the
proved Bernoulli representation, this transports parameter comparisons to the
actual maximum-height law. Sampling is restricted to surviving prefixes.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Forward

theorem activeMean_le_heightTest {s : State} (hs : s.active.Nonempty)
    (hsub : s.active ⊆ s.vertices) (f : ℕ → ℝ) (hf : Monotone f) :
    activeMean s f ≤ f (treeHeight s) := by
  have hc : (0 : ℝ) < s.active.card := Nat.cast_pos.mpr hs.card_pos
  unfold activeMean activeSum
  apply (div_le_iff₀ hc).mpr
  calc
    _ ≤ ∑ _v ∈ s.active, f (treeHeight s) :=
      Finset.sum_le_sum fun v hv => hf (height_le_treeHeight (hsub hv))
    _ = _ := by simp; ring

/-- An increasing test function at a uniform active depth is bounded by the
same test function of the actual tree maximum. -/
theorem integral_uniformActiveHeightLaw_le_heightLaw (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) (hf : Monotone f) :
    (∫ k, f k ∂uniformActiveHeightLaw x n) ≤ ∫ k, f k ∂heightLaw x n := by
  rw [uniformActiveHeightLaw_integral x n hτ, heightLaw_integral]
  apply integral_mono_ae (treeLaw_integrable_activeMean x n f)
    (treeLaw_integrable_heightTest x n f)
  filter_upwards [treeLaw_active_nonempty x n hτ, treeLaw_valid x n] with s hs hv
  exact activeMean_le_heightTest hs hv.active_subset f hf

/-- Stochastic domination expressed by all natural upper tails. -/
theorem uniformActiveHeightLaw_real_tail_le (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (h : ℕ) :
    (uniformActiveHeightLaw x n).real {k | h ≤ k} ≤ (heightLaw x n).real {k | h ≤ k} := by
  let f : ℕ → ℝ := {k | h ≤ k}.indicator (fun _ => 1)
  have hf : Monotone f := by
    intro a b hab
    by_cases ha : h ≤ a
    · have hh := ha.trans hab
      simp [f, ha, hh]
    · by_cases hh : h ≤ b <;> simp [f, ha, hh]
  have hh := integral_uniformActiveHeightLaw_le_heightLaw x n hτ f hf
  simpa only [f, integral_indicator_const (1 : ℝ)
    (show MeasurableSet {k : ℕ | h ≤ k} from by trivial), smul_eq_mul, mul_one] using hh

/-- Smaller independent Bernoulli parameters give a stochastic lower bound
for the maximum. The exact product law and active-height representation are
proved elsewhere; neither is an additional hypothesis here. -/
theorem bernoulliPartialSumLaw_real_tail_le_heightLaw (x : SignSequence) (n : ℕ)
    (hn : PositiveThrough x n) (p : Fin n → unitInterval)
    (hp : ∀ i : Fin n, x (i.val + 1) = true →
      p i ≤ populationBernoulliParameter x n hn i) (h : ℕ) :
    (bernoulliPartialSumLaw p
      (Finset.univ.filter fun i : Fin n => x (i.val + 1) = true)).real {k | h ≤ k} ≤
        (heightLaw x n).real {k | h ≤ k} := by
  calc
    _ ≤ (bernoulliPartialSumLaw (populationBernoulliParameter x n hn)
        (Finset.univ.filter fun i : Fin n => x (i.val + 1) = true)).real {k | h ≤ k} :=
      bernoulliPartialSumLaw_real_tail_mono _ _ _
        (fun i hi => hp i (Finset.mem_filter.mp hi).2) h
    _ = (uniformActiveHeightLaw x n).real {k | h ≤ k} := by
      rw [uniformActiveHeightLaw_eq_bernoulliSum x n hn]
    _ ≤ _ := uniformActiveHeightLaw_real_tail_le x n
      ((lt_extinctionTime_iff x n).mpr hn) h

end Forward
end FreezingGrowth
