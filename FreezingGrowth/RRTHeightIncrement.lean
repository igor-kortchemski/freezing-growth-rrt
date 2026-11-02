module

public import FreezingGrowth.RRTWeakLowerTail

/-! Actual attachment increments and the conditional deepest-parent probability. -/

@[expose] public section
namespace FreezingGrowth.RRT

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

noncomputable def deepestFraction (s : Forward.State) : ℝ :=
  Forward.activeMean s (fun h => if h = Forward.treeHeight s then 1 else 0)

theorem deepestFraction_nonneg (s : Forward.State) : 0 ≤ deepestFraction s := by
  unfold deepestFraction Forward.activeMean Forward.activeSum
  apply div_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (Nat.cast_nonneg _)

theorem deepestFraction_abs_le_one (s : Forward.State) : |deepestFraction s| ≤ 1 := by
  apply Forward.activeMean_bound (by norm_num)
  intro v _
  split_ifs <;> norm_num

theorem deepestFraction_integrable (n : ℕ) :
    Integrable deepestFraction (Forward.treeLaw allAttach n) := by
  apply (integrable_const (1 : ℝ)).mono' measurable_from_top.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => by
    simpa only [Real.norm_eq_abs] using deepestFraction_abs_le_one s)

theorem transition_mean_height {n : ℕ} {s : Forward.State}
    (hs : Forward.ValidAt n s) (ha : s.active.Nonempty) :
    (∫ t, (Forward.treeHeight t : ℝ) ∂Forward.transitionLaw s (n + 1) true) =
      (Forward.treeHeight s : ℝ) + deepestFraction s := by
  rw [Forward.transitionLaw_integral s _ _ ha]
  have hvalue : ∀ v ∈ s.active,
      (Forward.treeHeight (Forward.step s (n + 1) true v) : ℝ) =
        (Forward.treeHeight s : ℝ) + (if s.height v = Forward.treeHeight s then 1 else 0) := by
    intro v hv
    have hfresh : n + 1 ∉ s.vertices := by
      intro h
      have := hs.vertices_le _ h
      omega
    rw [Forward.step, ite_eq_left hv, ite_eq_left rfl,
      Forward.treeHeight_attach s _ _ hfresh]
    have hh := Forward.height_le_treeHeight (hs.active_subset hv)
    by_cases he : s.height v = Forward.treeHeight s
    · simp [he, Nat.cast_add]
    · have hl : s.height v + 1 ≤ Forward.treeHeight s := by omega
      rw [max_eq_left hl]
      simp [he]
  rw [Finset.sum_congr rfl hvalue, Finset.sum_add_distrib,
    Finset.sum_const, nsmul_eq_mul]
  have hc : (s.active.card : ℝ) ≠ 0 := by exact_mod_cast ha.card_pos.ne'
  unfold deepestFraction Forward.activeMean Forward.activeSum
  field_simp

theorem meanHeight_increment_eq_integral (n : ℕ) :
    meanHeight (n + 1) - meanHeight n =
      ∫ s, deepestFraction s ∂Forward.treeLaw allAttach n := by
  let K : Kernel Forward.State Forward.State :=
    ⟨fun s => Forward.transitionLaw s (n + 1) true, measurable_from_top⟩
  have hi := Forward.treeLaw_integrable_heightTest allAttach (n + 1) (fun k => (k : ℝ))
  rw [Forward.treeLaw] at hi
  have hi' : Integrable (fun s => (Forward.treeHeight s : ℝ))
      ((K ∘ₖ Kernel.const Unit (Forward.treeLaw allAttach n)) ()) := by
    simpa only [K, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply, allAttach] using hi
  have hrec := Kernel.integral_comp hi'
  simp only [K, Kernel.coe_mk, Kernel.comp_apply, Kernel.const_apply] at hrec
  have he : meanHeight (n + 1) = ∫ s, (Forward.treeHeight s : ℝ) + deepestFraction s
      ∂Forward.treeLaw allAttach n := by
    change (∫ s, (Forward.treeHeight s : ℝ)
      ∂(Forward.treeLaw allAttach n).bind (fun s => Forward.transitionLaw s (n + 1) true)) = _
    rw [hrec]
    apply integral_congr_ae
    filter_upwards [Forward.treeLaw_valid allAttach n,
      Forward.treeLaw_active_nonempty allAttach n (before_extinction n)] with s hs ha
    exact transition_mean_height hs ha
  rw [integral_add (Forward.treeLaw_integrable_heightTest allAttach n (fun k => (k : ℝ)))
    (deepestFraction_integrable n)] at he
  change meanHeight (n + 1) = meanHeight n + _ at he
  linarith

theorem deepestFraction_le_split (s : Forward.State) (r : ℝ) :
    deepestFraction s ≤ (if (Forward.treeHeight s : ℝ) ≤ r then 1 else 0) +
      Forward.activeMean s (fun h => if r ≤ (h : ℝ) then 1 else 0) := by
  have htail : 0 ≤ Forward.activeMean s (fun h => if r ≤ (h : ℝ) then (1 : ℝ) else 0) := by
    unfold Forward.activeMean Forward.activeSum
    apply div_nonneg (Finset.sum_nonneg (fun _ _ => by positivity)) (Nat.cast_nonneg _)
  split_ifs with hs
  · linarith [deepestFraction_abs_le_one s, le_abs_self (deepestFraction s)]
  · rw [zero_add]
    unfold deepestFraction Forward.activeMean Forward.activeSum
    apply div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro v _
    by_cases he : s.height v = Forward.treeHeight s
    · have hr : r ≤ (Forward.treeHeight s : ℝ) := by linarith
      simp [he, hr]
    · simp only [he, ↓reduceIte]
      split_ifs <;> norm_num

theorem meanHeight_increment_tendsto_zero :
    Tendsto (fun n : ℕ => meanHeight (n + 1) - meanHeight n) atTop (𝓝 0) := by
  have hu := uniformVertexDepthLaw_upper_tail_tendsto_zero (c := (11 / 10 : ℝ)) (by norm_num)
  have hl := height_lower_tail_tendsto_zero
  have hsum := hl.add hu
  simp only [add_zero] at hsum
  have hnonneg (n : ℕ) : 0 ≤ meanHeight (n + 1) - meanHeight n := by
    rw [meanHeight_increment_eq_integral]
    exact integral_nonneg deepestFraction_nonneg
  apply squeeze_zero hnonneg ?_ hsum
  intro n
  rw [meanHeight_increment_eq_integral]
  let r := (11 / 10 : ℝ) * Real.log (n : ℝ)
  have hi := Forward.treeLaw_integrable_activeMean allAttach n
    (fun h => if r ≤ (h : ℝ) then (1 : ℝ) else 0)
  have hle := integral_mono (deepestFraction_integrable n)
    (((integrable_const (1 : ℝ)).indicator (show MeasurableSet
      {s : Forward.State | (Forward.treeHeight s : ℝ) ≤ r} from by trivial)).add hi)
    (fun s => deepestFraction_le_split s r)
  change (∫ s, deepestFraction s ∂Forward.treeLaw allAttach n) ≤ _
  convert hle using 1
  simp only [Pi.add_apply]
  rw [integral_add ((integrable_const (1 : ℝ)).indicator (by trivial)) hi,
    ← Forward.uniformActiveHeightLaw_integral allAttach n (before_extinction n)]
  rw [Forward.heightLaw, map_measureReal_apply measurable_from_top (by trivial)]
  congr 1
  · exact (integral_indicator_one (by trivial)).symm
  · symm
    exact integral_indicator_one (by trivial)

end FreezingGrowth.RRT
