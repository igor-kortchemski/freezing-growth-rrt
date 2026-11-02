module

public import FreezingGrowth.LowProfile

/-!
# Direct finite upper bound for the maximum height

Extracted from the Apache-2.0 freezing1 companion's ForwardMaximum.lean;
source SHA-256 9475945570b7d97ab8709acec6f824cee652106e1a12ed346ed7f0c89f4d04c1.
See NOTICE. The existing true graph-distance maximum and lower bound are reused.
Attachment adds a child's exponential weight; freezing retains every vertex.
-/

@[expose] public section

namespace FreezingGrowth.Forward

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

def vertexSum (s : State) (f : ℕ → ℝ) : ℝ := ∑ v ∈ s.vertices, f (s.height v)

theorem vertexSum_attach {n : ℕ} {s : State} (h : ValidAt n s) (v : ℕ) (f : ℕ → ℝ) :
    vertexSum (attach s (n + 1) v) f = vertexSum s f + f (s.height v + 1) := by
  have hfresh : n + 1 ∉ s.vertices := by intro ht; have := h.vertices_le _ ht; omega
  unfold vertexSum
  simp only [attach]
  rw [Finset.sum_insert hfresh]
  simp only [Function.update_self]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro w hw
  have hwne : w ≠ n + 1 := by intro he; exact hfresh (he ▸ hw)
  simp [hwne]

theorem vertexSum_freeze (s : State) (t v : ℕ) (f : ℕ → ℝ) :
    vertexSum (freeze s t v) f = vertexSum s f := rfl

theorem transitionLaw_vertexSum_attach {n : ℕ} {s : State} (h : ValidAt n s)
    (hs : s.active.Nonempty) (f : ℕ → ℝ) :
    (∫ s', vertexSum s' f ∂transitionLaw s (n + 1) true) =
      vertexSum s f + activeMean s (fun k => f (k + 1)) := by
  rw [transitionLaw_integral s _ _ hs]
  have heq : ∀ v ∈ s.active, vertexSum (step s (n + 1) true v) f =
      vertexSum s f + f (s.height v + 1) := by
    intro v hv
    simpa [Forward.step, hv] using vertexSum_attach h v f
  rw [Finset.sum_congr rfl heq, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  unfold activeMean activeSum
  have hc : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  field_simp

theorem transitionLaw_vertexSum_freeze (s : State) (t : ℕ)
    (hs : s.active.Nonempty) (f : ℕ → ℝ) :
    (∫ s', vertexSum s' f ∂transitionLaw s t false) = vertexSum s f := by
  rw [transitionLaw_integral s _ _ hs]
  have heq : ∀ v ∈ s.active, vertexSum (step s t false v) f = vertexSum s f := by
    intro v hv
    simp [Forward.step, hv, vertexSum_freeze]
  rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
  have hc : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  field_simp

theorem ValidAt.vertexSum_bound {n : ℕ} {s : State} (hs : ValidAt n s) (f : ℕ → ℝ) :
    |vertexSum s f| ≤ (n + 1) * ∑ k ∈ Finset.range (n + 1), |f k| := by
  let C : ℝ := ∑ k ∈ Finset.range (n + 1), |f k|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hc : s.vertices.card ≤ n + 1 := by
    apply le_trans (Finset.card_le_card (t := Finset.range (n + 1)) ?_)
      (by simp)
    intro v hv
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hs.vertices_le v hv))
  calc
    |vertexSum s f| ≤ ∑ v ∈ s.vertices, |f (s.height v)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _v ∈ s.vertices, C := by
      apply Finset.sum_le_sum
      intro v hv
      have hh := (hs.height_le_id v hv).trans (hs.vertices_le v hv)
      exact Finset.single_le_sum (f := fun k => |f k|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.mpr (show s.height v < n + 1 by omega))
    _ = (s.vertices.card : ℝ) * C := by simp
    _ ≤ (n + 1) * C := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hC

theorem treeLaw_integrable_vertexSum (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    Integrable (fun s => vertexSum s f) (treeLaw x n) := by
  apply (integrable_const ((n + 1 : ℝ) * ∑ k ∈ Finset.range (n + 1), |f k|)).mono'
    measurable_from_top.aestronglyMeasurable
  filter_upwards [treeLaw_valid x n] with s hs
  simpa only [Real.norm_eq_abs] using hs.vertexSum_bound f

theorem integral_treeLaw_vertexSum_succ (x : SignSequence) (n : ℕ) (f : ℕ → ℝ) :
    (∫ s', vertexSum s' f ∂treeLaw x (n + 1)) =
      ∫ s, (∫ s', vertexSum s' f ∂transitionLaw s (n + 1) (x (n + 1))) ∂treeLaw x n := by
  let K : Kernel State State := ⟨fun s => transitionLaw s (n + 1) (x (n + 1)), measurable_from_top⟩
  have hi := treeLaw_integrable_vertexSum x (n + 1) f
  rw [treeLaw] at hi
  have hi' : Integrable (fun s => vertexSum s f)
      ((K ∘ₖ Kernel.const Unit (treeLaw x n)) ()) := by
    simpa only [K, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hi
  have hh := Kernel.integral_comp hi'
  simpa only [K, treeLaw, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] using hh

theorem treeLaw_vertexSum_succ (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) (f : ℕ → ℝ) :
    (∫ s, vertexSum s f ∂treeLaw x (n + 1)) =
      (∫ s, vertexSum s f ∂treeLaw x n) +
        if x (n + 1) then (∫ s, activeMean s (fun k => f (k + 1)) ∂treeLaw x n) else 0 := by
  rw [integral_treeLaw_vertexSum_succ]
  cases hx : x (n + 1)
  · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    apply integral_congr_ae
    filter_upwards [treeLaw_active_nonempty x n hτ] with s hs
    exact transitionLaw_vertexSum_freeze s _ hs f
  · simp only [↓reduceIte]
    rw [← integral_add (treeLaw_integrable_vertexSum x n f)
      (treeLaw_integrable_activeMean x n (fun k => f (k + 1)))]
    apply integral_congr_ae
    filter_upwards [treeLaw_valid x n, treeLaw_active_nonempty x n hτ] with s hs hne
    exact transitionLaw_vertexSum_attach hs hne f

/-- Expected total exponential height weight, from the actual forward dynamics. -/
theorem treeLaw_vertexSum_exp_le (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ s, vertexSum s (fun k => Real.exp (θ * (k : ℝ))) ∂treeLaw x n) ≤
      (n + 1) * Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1)) := by
  induction n with
  | zero =>
    simp only [treeLaw, integral_dirac, vertexSum, initial, Finset.sum_singleton,
      Nat.cast_zero, mul_zero, Real.exp_zero, heightScale_zero, zero_add, one_mul]
    simpa using Real.one_le_exp hθ
  | succ n ih =>
    have hnτ : (n : ℕ∞) < extinctionTime x :=
      lt_trans (by exact_mod_cast Nat.lt_succ_self n) hτ
    have ih := ih hnτ
    have he : 0 ≤ Real.exp θ - 1 := sub_nonneg.mpr (Real.one_le_exp hθ)
    have hm : heightScale x n ≤ heightScale x (n + 1) := by
      rw [heightScale_succ]
      split_ifs
      · have hs := ((lt_extinctionTime_iff x (n + 1)).mp hτ) (n + 1) le_rfl
        have hsR : (0 : ℝ) < activeCount x (n + 1) := by exact_mod_cast hs
        have : 0 ≤ 1 / (activeCount x (n + 1) : ℝ) := by positivity
        linarith
      · simp
    have hMon : Real.exp (heightScale x n * (Real.exp θ - 1)) ≤
        Real.exp (heightScale x (n + 1) * (Real.exp θ - 1)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hm he)
    have hinc : (if x (n + 1) then
        (∫ s, activeMean s (fun k => Real.exp (θ * ((k + 1 : ℕ) : ℝ))) ∂treeLaw x n) else 0) ≤
        Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1)) := by
      split_ifs
      · rw [← uniformActiveHeightLaw_integral x n hnτ]
        simp_rw [Nat.cast_add, Nat.cast_one, mul_add, mul_one, Real.exp_add,
          mul_comm _ (Real.exp θ)]
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left (uniformActiveHeightLaw_mgf_le x n hnτ θ) (Real.exp_pos θ).le
      · positivity
    rw [treeLaw_vertexSum_succ x n hnτ]
    calc
      _ ≤ (n + 1) * Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1)) +
          Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1)) := add_le_add ih hinc
      _ = ((n + 1 : ℕ) + 1) * Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1)) := by
        push_cast; ring
      _ ≤ ((n + 1 : ℕ) + 1) * Real.exp θ * Real.exp (heightScale x (n + 1) * (Real.exp θ - 1)) :=
        mul_le_mul_of_nonneg_left hMon (by positivity)

theorem ValidAt.exp_treeHeight_le_vertexSum {n : ℕ} {s : State} (hs : ValidAt n s) (θ : ℝ) :
    Real.exp (θ * (treeHeight s : ℝ)) ≤ vertexSum s (fun k => Real.exp (θ * (k : ℝ))) := by
  obtain ⟨v, hv, hmax⟩ := Finset.exists_mem_eq_sup s.vertices ⟨0, hs.root_mem⟩ s.height
  rw [treeHeight, hmax]
  exact Finset.single_le_sum (f := fun w => Real.exp (θ * (s.height w : ℝ)))
    (fun _ _ => (Real.exp_pos _).le) hv

/-- Maximum-height MGF upper bound. The factor `exp θ` is the child's extra edge. -/
theorem treeHeight_mgf_upper (x : SignSequence) (n : ℕ)
    (hτ : (n : ℕ∞) < extinctionTime x) {θ : ℝ} (hθ : 0 ≤ θ) :
    mgf (fun s => (treeHeight s : ℝ)) (treeLaw x n) θ ≤
      (n + 1) * Real.exp θ * Real.exp (heightScale x n * (Real.exp θ - 1)) := by
  apply le_trans (integral_mono_ae (treeLaw_integrable_exp_treeHeight x n θ)
    (treeLaw_integrable_vertexSum x n (fun k => Real.exp (θ * (k : ℝ)))) ?_)
    (treeLaw_vertexSum_exp_le x n hτ hθ)
  exact (treeLaw_valid x n).mono (fun s hs => hs.exp_treeHeight_le_vertexSum θ)

/-- Correct finite upper tail obtained directly from forward dynamics.
The extra unit in the threshold records the edge from a parent to its new child. -/
theorem treeHeight_upper_tail (x : SignSequence) (n : ℕ) (hn : 1 ≤ n)
    (hτ : (n : ℕ∞) < extinctionTime x) {t : ℝ} (ht : 0 < t) :
    (treeLaw x n).real {s | heightScale x n + 1 + t < (treeHeight s : ℝ)} ≤
      (n + 1) * Real.exp (-heightScale x n * bennettRate (t / heightScale x n)) := by
  let m := heightScale x n
  have hm : 0 < m := heightScale_pos hn ((lt_extinctionTime_iff x n).mp hτ)
  let θ := Real.log (1 + t / m)
  have hθ : 0 ≤ θ := Real.log_nonneg (by have := div_pos ht hm; linarith)
  calc
    (treeLaw x n).real {s | m + 1 + t < (treeHeight s : ℝ)} ≤
        (treeLaw x n).real {s | m + 1 + t ≤ (treeHeight s : ℝ)} :=
      measureReal_mono (by
        intro s hs
        change m + 1 + t < (treeHeight s : ℝ) at hs
        change m + 1 + t ≤ (treeHeight s : ℝ)
        exact hs.le) (measure_ne_top _ _)
    _ ≤ Real.exp (-θ * (m + 1 + t)) * mgf (fun s => (treeHeight s : ℝ)) (treeLaw x n) θ :=
      measure_ge_le_exp_mul_mgf _ hθ (treeLaw_integrable_exp_treeHeight x n θ)
    _ ≤ Real.exp (-θ * (m + 1 + t)) *
        ((n + 1) * Real.exp θ * Real.exp (m * (Real.exp θ - 1))) :=
      mul_le_mul_of_nonneg_left (treeHeight_mgf_upper x n hτ hθ) (Real.exp_pos _).le
    _ = (n + 1) * (Real.exp (-θ * (m + 1 + t)) * Real.exp θ *
        Real.exp (m * (Real.exp θ - 1))) := by ring
    _ = (n + 1) * Real.exp (-θ * (m + t) + m * (Real.exp θ - 1)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ = (n + 1) * Real.exp (-m * bennettRate (t / m)) := by
      rw [bennett_exponent_identity hm ht]

end FreezingGrowth.Forward
