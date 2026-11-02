module

public import FreezingGrowth.RRTSplitSupport
public import FreezingGrowth.RRTSplitMixture
public import FreezingGrowth.ReverseIndexedKernel

/-!
# Uniform global parent choice gives the component growth kernel

The partition of actual birth identifiers is used to split the uniform parent
choice. Within each component, the increasing-label bijection gives precisely
the existing local forward transition. This connects the abstract two-factor
calculation to the actual recursive tree without a distributional premise.
-/

@[expose] public section

namespace FreezingGrowth.RRTSplit

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

theorem uniform_ae_mem (s : Finset ℕ) :
    ∀ᵐ v ∂Measure.uniformOfFinset s, v ∈ s := by
  rw [ae_iff, Measure.uniformOfFinset, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro a ha
  rw [Measure.smul_apply, Measure.dirac_apply' _ (by trivial)]
  simp [ha]

private theorem ratio_mul_inverse (a d : ℕ) (ha : 0 < a) :
    ((a : ℝ≥0∞) / d) * (a : ℝ≥0∞)⁻¹ = (d : ℝ≥0∞)⁻¹ := by
  rw [div_eq_mul_inv]
  calc
    _ = (d : ℝ≥0∞)⁻¹ * ((a : ℝ≥0∞) * (a : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (by exact_mod_cast ha.ne') (ENNReal.natCast_ne_top _),
        mul_one]

/-- Uniform sampling from two disjoint nonempty finite sets splits with the
exact population proportions. -/
theorem uniform_union (s t : Finset ℕ) (hd : Disjoint s t)
    (hs : s.Nonempty) (ht : t.Nonempty) :
    Measure.uniformOfFinset (s ∪ t) =
      ((s.card : ℝ≥0∞) / (s.card + t.card : ℕ)) • Measure.uniformOfFinset s +
      ((t.card : ℝ≥0∞) / (s.card + t.card : ℕ)) • Measure.uniformOfFinset t := by
  apply Measure.ext_of_singleton
  intro v
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  by_cases hvs : v ∈ s
  · have hvt : v ∉ t := fun h => Finset.disjoint_left.mp hd hvs h
    rw [Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_union_left _ hvs),
      Measure.uniformOfFinset_apply_singleton_of_mem hvs,
      Measure.uniformOfFinset_apply_singleton_of_notMem hvt,
      mul_zero, add_zero, Finset.card_union_of_disjoint hd]
    simpa only [one_div] using (ratio_mul_inverse s.card (s.card + t.card) hs.card_pos).symm
  · by_cases hvt : v ∈ t
    · rw [Measure.uniformOfFinset_apply_singleton_of_mem (Finset.mem_union_right _ hvt),
        Measure.uniformOfFinset_apply_singleton_of_notMem hvs,
        Measure.uniformOfFinset_apply_singleton_of_mem hvt,
        mul_zero, zero_add, Finset.card_union_of_disjoint hd]
      simpa only [one_div] using (ratio_mul_inverse t.card (s.card + t.card) ht.card_pos).symm
    · have hv : v ∉ s ∪ t := by simp [hvs, hvt]
      simp [Measure.uniformOfFinset_apply_singleton_of_notMem hv,
        Measure.uniformOfFinset_apply_singleton_of_notMem hvs,
        Measure.uniformOfFinset_apply_singleton_of_notMem hvt]

namespace Component

theorem label_image (c : Component) :
    (Finset.range c.labels.length).image c.label = c.labels.toFinset := by
  ext v
  constructor
  · rintro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact List.mem_toFinset.mpr (c.label_mem (Finset.mem_range.mp hi))
  · intro hv
    have hv' := List.mem_toFinset.mp hv
    exact Finset.mem_image.mpr ⟨c.labels.idxOf v,
      Finset.mem_range.mpr (List.idxOf_lt_length_of_mem hv'), label_idxOf hv'⟩

theorem WellFormed.idxOf_label {r : ℕ} {c : Component} (hc : WellFormed r c)
    {i : ℕ} (hi : i < c.labels.length) : c.labels.idxOf (c.label i) = i := by
  have hm := c.label_mem hi
  exact hc.label_injective
    (Finset.mem_range.mpr (List.idxOf_lt_length_of_mem hm))
    (Finset.mem_range.mpr hi) (label_idxOf hm)

theorem WellFormed.uniform_labels {r : ℕ} {c : Component} (hc : WellFormed r c) :
    Measure.uniformOfFinset c.labels.toFinset =
      (Measure.uniformOfFinset (Finset.range c.labels.length)).map c.label := by
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _) hc.label_injective,
    label_image]

/-- Relabelling a uniform original parent is exactly uniform local attachment. -/
theorem WellFormed.attachLaw {r : ℕ} {c : Component} (hc : WellFormed r c) :
    (Measure.uniformOfFinset c.labels.toFinset).map
        (fun v => Forward.attach c.tree c.labels.length (c.labels.idxOf v)) =
      Forward.transitionLaw c.tree c.labels.length true := by
  have hne : c.tree.active.Nonempty := by
    rw [hc.active]
    exact ⟨0, Finset.mem_range.mpr hc.length_pos⟩
  rw [hc.uniform_labels, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _), Forward.transitionLaw, ite_eq_left hne, hc.active]
  apply Measure.map_congr
  filter_upwards [uniform_ae_mem (Finset.range c.labels.length)] with i hi
  have hi' := Finset.mem_range.mp hi
  have hm : i ∈ c.tree.active := by rwa [hc.active]
  simp only [Function.comp_def, hc.idxOf_label hi', Forward.step, ite_eq_left hm, ite_true]

end Component

theorem map_root_grow {n : ℕ} {p : Parts} (hp : WellFormed n p) (t : ℕ) :
    (Measure.uniformOfFinset p.rootSide.labels.toFinset).map
        (fun v => observable (grow p t v)) =
      leftKernel (p.rootSide.labels.length - 1) (p.rootSide.tree, p.childSide.tree) := by
  have hlen : p.rootSide.labels.length - 1 + 1 = p.rootSide.labels.length := by
    have := hp.root.length_pos
    omega
  rw [leftKernel, Kernel.map_apply _ measurable_prodMk_left,
    Kernel.parallelComp_apply, Kernel.id_apply, attachmentKernel, Kernel.coe_mk,
    Measure.prod_dirac, Measure.map_map measurable_prodMk_left measurable_prodMk_right,
    hlen, ← hp.root.attachLaw,
    Measure.map_map (measurable_prodMk_left.comp measurable_prodMk_right)
      (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [uniform_ae_mem p.rootSide.labels.toFinset] with v hv
  have hv' := List.mem_toFinset.mp hv
  simp [grow, hv', observable, Component.attach, Function.comp_def]

theorem map_child_grow {n : ℕ} {p : Parts} (hp : WellFormed n p) (t : ℕ) :
    (Measure.uniformOfFinset p.childSide.labels.toFinset).map
        (fun v => observable (grow p t v)) =
      rightKernel (p.rootSide.labels.length - 1) (p.childSide.labels.length - 1)
        (p.rootSide.tree, p.childSide.tree) := by
  have hlen : p.childSide.labels.length - 1 + 1 = p.childSide.labels.length := by
    have := hp.child.length_pos
    omega
  rw [rightKernel, Kernel.map_apply _ measurable_prodMk_left,
    Kernel.parallelComp_apply, Kernel.id_apply, attachmentKernel, Kernel.coe_mk,
    Measure.dirac_prod, Measure.map_map measurable_prodMk_left measurable_prodMk_left,
    hlen, ← hp.child.attachLaw,
    Measure.map_map (measurable_prodMk_left.comp measurable_prodMk_left)
      (measurable_of_countable _)]
  apply Measure.map_congr
  filter_upwards [uniform_ae_mem p.childSide.labels.toFinset] with v hv
  have hv' := List.mem_toFinset.mp hv
  have hn : v ∉ p.rootSide.labels := fun h => hp.disjoint h hv'
  simp [grow, hn, observable, Component.attach, Function.comp_def]

/-- The observable kernel is obtained from the actual uniform global parent,
not postulated as a coupling or distributional equivalence. -/
theorem map_uniform_grow {n : ℕ} {p : Parts} (hp : WellFormed n p) (t : ℕ) :
    (Measure.uniformOfFinset (Finset.range (n + 2))).map
        (fun v => observable (grow p t v)) = growthKernel n (observable p) := by
  have hd : Disjoint p.rootSide.labels.toFinset p.childSide.labels.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact hp.disjoint (List.mem_toFinset.mp hv) (List.mem_toFinset.mp hw)
  have hr : p.rootSide.labels.toFinset.Nonempty := by
    obtain ⟨tail, he⟩ := hp.root.rooted
    exact ⟨0, by simp [he]⟩
  have hc : p.childSide.labels.toFinset.Nonempty := by
    obtain ⟨tail, he⟩ := hp.child.rooted
    exact ⟨1, by simp [he]⟩
  have hroot : p.rootSide.labels.length - 1 + 1 = p.rootSide.labels.length := by
    have := hp.root.length_pos
    omega
  have hchild : p.childSide.labels.length - 1 + 1 = p.childSide.labels.length := by
    have := hp.child.length_pos
    omega
  have hrest : n - (p.rootSide.labels.length - 1) = p.childSide.labels.length - 1 := by
    have := hp.edges_sum
    omega
  rw [← hp.cover, uniform_union _ _ hd hr hc,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    map_root_grow hp, map_child_grow hp]
  simp only [growthKernel, Kernel.coe_mk, observable, hrest, sizeKernel,
    List.toFinset_card_of_nodup hp.root.nodup,
    List.toFinset_card_of_nodup hp.child.nodup, hroot, hchild]
  have hden : p.rootSide.labels.length - 1 + (p.childSide.labels.length - 1) + 2 =
      p.rootSide.labels.length + p.childSide.labels.length := by
    omega
  rw [hden]

theorem map_transition_split {n : ℕ} {s : Forward.State}
    (hs : Describes n s (split n s)) :
    (Forward.transitionLaw s (n + 2) true).map (firstEdgeSplit (n + 1)) =
      growthKernel n (firstEdgeSplit n s) := by
  have hne : s.active.Nonempty := by rw [hs.active]; exact ⟨0, by simp⟩
  rw [Forward.transitionLaw, ite_eq_left hne, Measure.map_map measurable_from_top
    (measurable_of_countable _), hs.active]
  calc
    _ = (Measure.uniformOfFinset (Finset.range (n + 2))).map
        (fun v => observable (grow (split n s) (n + 2) v)) := by
      apply Measure.map_congr
      filter_upwards [uniform_ae_mem (Finset.range (n + 2))] with v hv
      have hv' : v ∈ s.active := by rwa [hs.active]
      simp only [Function.comp_def, Forward.step, ite_eq_left hv', ite_true, firstEdgeSplit,
        split_attach]
    _ = _ := map_uniform_grow hs.formed (n + 2)

end FreezingGrowth.RRTSplit
