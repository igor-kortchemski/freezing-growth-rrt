module

public import FreezingGrowth.PWIT.CenteredPath
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Absolute continuity and absence of centered-prefix ties -/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem finitePi_absolutelyContinuous_volume {d : ℕ} (μ : Fin d → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (hμ : ∀ i, μ i ≪ volume) : Measure.pi μ ≪ volume := by
  induction d with
  | zero =>
    have he : μ = fun _ : Fin 0 => (volume : Measure ℝ) := by
      funext i
      exact i.elim0
    rw [he]
    exact Measure.AbsolutelyContinuous.rfl
  | succ d ih =>
    have hp : (μ 0).prod (Measure.pi fun i => μ (Fin.succ i)) ≪
        (volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ)) :=
      (hμ 0).prod (ih (fun i => μ (Fin.succ i)) (fun i => hμ (Fin.succ i)))
    have he := hp.map (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm.measurable
    have hv : ((volume : Measure ℝ).prod (volume : Measure (Fin d → ℝ))).map
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm = volume := by
      exact (measurePreserving_piFinSuccAbove
        (fun _ : Fin (d + 1) => (volume : Measure ℝ)) 0).symm.map_eq
    rw [hv] at he
    simpa only [← Fin.zero_succAbove,
      (measurePreserving_piFinSuccAbove μ 0).symm.map_eq] using he

theorem incrementLaw_absolutelyContinuous_volume {d : ℕ} (r : Fin d → ℕ) :
    incrementLaw r ≪ volume := by
  let (i : Fin d) : IsProbabilityMeasure (gammaMeasure ((r i : ℝ) + 1) 1) :=
    isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)
  exact finitePi_absolutelyContinuous_volume _ fun _ => withDensity_absolutelyContinuous _ _

theorem rankIncrementMeasure_absolutelyContinuous_volume (d k : ℕ) :
    rankIncrementMeasure d k ≪ volume := by
  classical
  unfold rankIncrementMeasure
  apply Finset.sum_induction (fun r => incrementLaw r) (fun μ => μ ≪ volume)
  · exact fun _ _ h₁ h₂ => h₁.add_left h₂
  · exact Measure.AbsolutelyContinuous.zero _
  · exact fun r _ => incrementLaw_absolutelyContinuous_volume r

section PositiveDepth

variable {d : ℕ} [NeZero d]

noncomputable def centeredBridgeLinear (i : Fin d) : (Fin d → ℝ) →ₗ[ℝ] ℝ where
  toFun x := centeredBridge x i
  map_add' x y := by
    simp only [centeredBridge, centeredPrefix, cyclicPrefix, Pi.add_apply,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    simp only [centeredBridge, centeredPrefix, cyclicPrefix, Pi.smul_apply, smul_eq_mul,
      ← Finset.mul_sum, RingHom.id_apply]
    ring

private theorem cyclicPrefix_spike (n : ℕ) (hn : n ≤ d) :
    cyclicPrefix (fun i : Fin d => if i = 0 then (1 : ℝ) else 0) n =
      if n = 0 then 0 else 1 := by
  classical
  unfold cyclicPrefix
  have he (j : ℕ) (hj : j ∈ Finset.range n) :
      (Fin.ofNat d j = 0) ↔ j = 0 := by
    have hjd : j < d := lt_of_lt_of_le (Finset.mem_range.mp hj) hn
    constructor
    · intro h
      have hh := congrArg Fin.val h
      simpa only [Fin.val_ofNat, Fin.val_zero, Nat.mod_eq_of_lt hjd] using hh
    · rintro rfl
      rfl
  calc
    _ = ∑ j ∈ Finset.range n, if j = 0 then (1 : ℝ) else 0 := by
      exact Finset.sum_congr rfl fun j hj => if_congr (he j hj) rfl rfl
    _ = _ := by
      by_cases hn0 : n = 0
      · simp [hn0]
      · simp [hn0, Nat.pos_of_ne_zero hn0]

private theorem centeredBridge_spike (i : Fin d) :
    centeredBridge (fun j : Fin d => if j = 0 then (1 : ℝ) else 0) i =
      if i = 0 then 0 else 1 - (i : ℝ) / d := by
  classical
  simp only [centeredBridge, centeredPrefix, cyclicPrefix_spike i i.isLt.le,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hi : i = 0
  · simp [hi]
  · have hi' : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp [hi, hi']

theorem centeredBridge_spike_injective :
    Function.Injective (centeredBridge (fun i : Fin d => if i = 0 then (1 : ℝ) else 0)) := by
  intro i j hij
  have hd : 0 < (d : ℝ) := Nat.cast_pos.mpr (NeZero.pos d)
  have hi : (i : ℝ) < d := by exact_mod_cast i.isLt
  have hj : (j : ℝ) < d := by exact_mod_cast j.isLt
  simp only [centeredBridge_spike] at hij
  split_ifs at hij with hi0 hj0 hj0
  · exact hi0.trans hj0.symm
  · have hpos : 0 < 1 - (j : ℝ) / d := sub_pos.mpr ((div_lt_one hd).mpr hj)
    linarith
  · have hpos : 0 < 1 - (i : ℝ) / d := sub_pos.mpr ((div_lt_one hd).mpr hi)
    linarith
  · apply Fin.ext
    have hdiv : (i : ℝ) / d = (j : ℝ) / d := by linarith
    have hval : (i : ℝ) = (j : ℝ) := (div_left_inj' hd.ne').mp hdiv
    exact_mod_cast hval

theorem ae_centeredBridge_injective_volume :
    ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), Function.Injective (centeredBridge x) := by
  change ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)), ∀ i j,
    centeredBridge x i = centeredBridge x j → i = j
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun _ _ => hij
  · have hlinear : centeredBridgeLinear i - centeredBridgeLinear j ≠ 0 := by
      intro h
      have he := congrArg (fun L : (Fin d → ℝ) →ₗ[ℝ] ℝ =>
        L (fun r : Fin d => if r = 0 then (1 : ℝ) else 0)) h
      have he' : centeredBridge (fun r : Fin d => if r = 0 then (1 : ℝ) else 0) i =
          centeredBridge (fun r : Fin d => if r = 0 then (1 : ℝ) else 0) j := by
        simpa only [LinearMap.sub_apply, centeredBridgeLinear, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.zero_apply, sub_eq_zero] using he
      exact hij (centeredBridge_spike_injective he')
    have hnull := Measure.addHaar_submodule (volume : Measure (Fin d → ℝ))
      (LinearMap.ker (centeredBridgeLinear i - centeredBridgeLinear j))
      (by intro hker; exact hlinear (LinearMap.ker_eq_top.mp hker))
    have hae : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)),
        x ∉ LinearMap.ker (centeredBridgeLinear i - centeredBridgeLinear j) := by
      apply ae_iff.mpr
      convert hnull using 1
      congr 1
      ext x
      simp
    filter_upwards [hae] with x hx he
    exfalso
    apply hx
    change centeredBridge x i - centeredBridge x j = 0
    exact sub_eq_zero.mpr he

theorem ae_centeredBridge_injective (k : ℕ) :
    ∀ᵐ x ∂rankIncrementMeasure d k, Function.Injective (centeredBridge x) :=
  (rankIncrementMeasure_absolutelyContinuous_volume d k).ae_le
    ae_centeredBridge_injective_volume

end PositiveDepth

end FreezingGrowth.PWIT
