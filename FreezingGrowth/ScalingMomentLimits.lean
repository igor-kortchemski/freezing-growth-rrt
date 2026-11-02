module

public import FreezingGrowth.AlternatingHeightBounds
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Generic maximum-moment limits

Selected Apache-2.0 companion fragments; see SCALING_PROVENANCE.md.
No duplicate tree state or assumed concentration theorem is introduced.
-/

@[expose] public section

namespace FreezingGrowth.Scaling

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

/-- Cut an `Lp` norm into a bounded part and a higher-moment tail. -/
theorem eLpNorm_le_cutoff_add_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : Measurable f) {p q ε : ℝ}
    (hp : 1 ≤ p) (hpq : p < q) (hε : 0 ≤ ε) :
    eLpNorm f (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε +
      eLpNorm f (ENNReal.ofReal q) μ * μ {ω | ε ≤ ‖f ω‖} ^ (1 / p - 1 / q) := by
  let s : Set Ω := {ω | ε ≤ ‖f ω‖}
  have hs : MeasurableSet s := measurableSet_le measurable_const hf.norm
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := hp0.trans hpq
  have hsplit : f = sᶜ.indicator f + s.indicator f := by
    funext ω
    by_cases hω : ω ∈ s <;> simp [hω]
  have hlo : eLpNorm (sᶜ.indicator f) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal ε := by
    have hb : ∀ᵐ ω ∂μ, ‖sᶜ.indicator f ω‖ ≤ ε := by
      apply ae_of_all
      intro ω
      by_cases hω : ω ∈ s
      · simp [hω, hε]
      · have : ‖f ω‖ < ε := lt_of_not_ge hω
        simpa [hω] using this.le
    simpa using eLpNorm_le_of_ae_bound (hf.aestronglyMeasurable.indicator hs.compl) hb
  have hhi : eLpNorm (s.indicator f) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal q) μ * μ s ^ (1 / p - 1 / q) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet]
    calc
      eLpNorm f (ENNReal.ofReal p) (μ.restrict s) ≤
          eLpNorm f (ENNReal.ofReal q) (μ.restrict s) * μ s ^ (1 / p - 1 / q) := by
        simpa only [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal hq0.le,
          Measure.restrict_apply_univ] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
            (ENNReal.ofReal_le_ofReal hpq.le) hf.aestronglyMeasurable.restrict
      _ ≤ eLpNorm f (ENNReal.ofReal q) μ * μ s ^ (1 / p - 1 / q) :=
        mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl
  calc
    eLpNorm f (ENNReal.ofReal p) μ =
        eLpNorm (sᶜ.indicator f + s.indicator f) (ENNReal.ofReal p) μ :=
      congrArg (fun g : Ω → ℝ ↦ eLpNorm g (ENNReal.ofReal p) μ) hsplit
    _ ≤ eLpNorm (sᶜ.indicator f) (ENNReal.ofReal p) μ +
        eLpNorm (s.indicator f) (ENNReal.ofReal p) μ :=
      eLpNorm_add_le (by simpa using ENNReal.ofReal_le_ofReal hp)
    _ ≤ _ := add_le_add hlo hhi

section VaryingMeasures

variable {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
  {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]

/-- Convergence in probability and an eventual bounded higher moment imply
`Lp` convergence even when the sample spaces and measures vary with `n`. -/
theorem tendsto_eLpNorm_of_tail_and_higher_moment
    {f : ∀ n, Ξ n → ℝ} (hf : ∀ n, Measurable (f n))
    {p q : ℝ} (hp : 1 ≤ p) (hpq : p < q)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ᶠ n in atTop, eLpNorm (f n) (ENNReal.ofReal q) (ν n) ≤ C)
    (htail : ∀ ε > 0, Tendsto (fun n ↦ ν n {ω | ε ≤ ‖f n ω‖}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ eLpNorm (f n) (ENNReal.ofReal p) (ν n)) atTop (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hr : 0 < 1 / p - 1 / q :=
    sub_pos.mpr (one_div_lt_one_div_of_lt hp0 hpq)
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  obtain ⟨ε, hε, hεδ⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := (2 : ℝ≥0∞)) (by norm_num) hδ.ne'
  have hεreal : (0 : ℝ) < ε := hε
  have hεenn : (0 : ℝ≥0∞) < ε := by exact_mod_cast hε
  have hsmall : Tendsto (fun n ↦ C * ν n {ω | (ε : ℝ) ≤ ‖f n ω‖} ^
      (1 / p - 1 / q)) atTop (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC hr).comp (htail ε hεreal)
  filter_upwards [hbound, ENNReal.tendsto_nhds_zero.mp hsmall ε hεenn] with n hn hsmalln
  calc
    eLpNorm (f n) (ENNReal.ofReal p) (ν n) ≤ ENNReal.ofReal ε +
        eLpNorm (f n) (ENNReal.ofReal q) (ν n) *
          ν n {ω | (ε : ℝ) ≤ ‖f n ω‖} ^ (1 / p - 1 / q) :=
      eLpNorm_le_cutoff_add_tail (hf n) hp hpq hεreal.le
    _ ≤ (ε : ℝ≥0∞) + ε := by
      simp only [ENNReal.ofReal_coe_nnreal]
      exact add_le_add le_rfl ((mul_le_mul' hn le_rfl).trans hsmalln)
    _ ≤ δ := by
      have heq : (ε : ℝ≥0∞) + ε = ε * 2 := by rw [mul_two]
      exact heq ▸ hεδ.le

end VaryingMeasures

section Normalization
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {X : Ω → ℝ} {m : ℝ}

/-- Normalizing preserves exponential integrability at every parameter. -/
theorem normalized_exp_integrable
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ) (θ : ℝ) :
    Integrable (fun ω ↦ Real.exp (θ * (X ω / m))) μ := by
  simpa only [div_mul_eq_mul_div, mul_div_assoc] using h_int (θ / m)

end Normalization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {m B : ℝ}

/-- Jensen removes the growing exponent from the exponential moment. -/
theorem normalized_exp_integral_le_of_exp_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hm : 1 ≤ m) (hbound : mgf X μ 1 ≤ Real.exp (B * m)) :
    (∫ ω, Real.exp (X ω / m) ∂μ) ≤ Real.exp B := by
  have hmpos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmi0 : 0 ≤ m⁻¹ := inv_nonneg.mpr hmpos.le
  have hmi1 : m⁻¹ ≤ 1 := (inv_le_one₀ hmpos).mpr hm
  have hp : Integrable (fun ω ↦ Real.exp (X ω)) μ := by simpa using h_int 1
  have hpNorm : Integrable (fun ω ↦ (Real.exp (X ω)) ^ m⁻¹) μ := by
    simpa only [← Real.exp_mul, one_mul, div_eq_mul_inv] using
      normalized_exp_integrable h_int (m := m) 1
  have hj := (Real.concaveOn_rpow hmi0 hmi1).le_map_integral
    (Real.continuous_rpow_const hmi0).continuousOn isClosed_Ici
    (ae_of_all μ (fun ω ↦ (Real.exp_pos (X ω)).le)) hp hpNorm
  calc
    (∫ ω, Real.exp (X ω / m) ∂μ) = ∫ ω, (Real.exp (X ω)) ^ m⁻¹ ∂μ := by
      simp only [← Real.exp_mul, div_eq_mul_inv]
    _ ≤ (∫ ω, Real.exp (X ω) ∂μ) ^ m⁻¹ := hj
    _ ≤ (Real.exp (B * m)) ^ m⁻¹ := by
      apply Real.rpow_le_rpow (integral_nonneg fun ω ↦ (Real.exp_pos (X ω)).le) ?_ hmi0
      simpa only [mgf, one_mul] using hbound
    _ = Real.exp B := by
      rw [← Real.exp_mul]
      congr 1
      field_simp

/-- Nonnegativity supplies the opposite exponential moment bound. -/
theorem normalized_neg_exp_integral_le_one
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω) (hm : 0 < m) :
    (∫ ω, Real.exp (-(X ω / m)) ∂μ) ≤ 1 := by
  have hi : Integrable (fun ω ↦ Real.exp (-(X ω / m))) μ := by
    simpa only [neg_one_mul] using normalized_exp_integrable h_int (m := m) (-1)
  have hb : ∀ᵐ ω ∂μ, Real.exp (-(X ω / m)) ≤ (1 : ℝ) := by
    filter_upwards [hX] with ω hω
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (div_nonneg hω hm.le))
  simpa using integral_mono_ae hi (integrable_const (1 : ℝ)) hb

/-- Every nonnegative real moment is bounded uniformly from the exponential bound. -/
theorem normalized_moment_le_of_exp_bound
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hm : 1 ≤ m) (hbound : mgf X μ 1 ≤ Real.exp (B * m))
    {q : ℝ} (hq : 0 ≤ q) :
    (∫ ω, |X ω / m| ^ q ∂μ) ≤ q ^ q * (Real.exp B + 1) := by
  have hpos : Integrable (fun ω ↦ Real.exp (X ω / m)) μ := by
    simpa only [one_mul] using normalized_exp_integrable h_int (m := m) 1
  have hneg : Integrable (fun ω ↦ Real.exp (-(X ω / m))) μ := by
    simpa only [neg_one_mul] using normalized_exp_integrable h_int (m := m) (-1)
  have hrpow : Integrable (fun ω ↦ |X ω / m| ^ q) μ := by
    apply integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero ?_ ?_ hq
    · simpa only [one_mul] using hpos
    · simpa only [neg_one_mul] using hneg
  have hpoint : ∀ ω, |X ω / m| ^ q ≤ q ^ q *
      (Real.exp (X ω / m) + Real.exp (-(X ω / m))) := by
    intro ω
    have hb := rpow_abs_le_mul_max_exp_of_pos (X ω / m) hq (t := 1) zero_lt_one
    simp only [div_one, one_mul, neg_one_mul] at hb
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hq _))
    exact max_le (le_add_of_nonneg_right (Real.exp_pos _).le)
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  have hup := normalized_exp_integral_le_of_exp_bound h_int hm hbound
  have hdown := normalized_neg_exp_integral_le_one h_int hX (lt_of_lt_of_le zero_lt_one hm)
  calc
    (∫ ω, |X ω / m| ^ q ∂μ) ≤ ∫ ω, q ^ q *
        (Real.exp (X ω / m) + Real.exp (-(X ω / m))) ∂μ :=
      integral_mono hrpow ((hpos.add hneg).const_mul _) hpoint
    _ = q ^ q * ((∫ ω, Real.exp (X ω / m) ∂μ) + ∫ ω, Real.exp (-(X ω / m)) ∂μ) := by
      rw [integral_const_mul, integral_add hpos hneg]
    _ ≤ q ^ q * (Real.exp B + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hup hdown) (Real.rpow_nonneg hq _)

/-- The corresponding uniform bound for finite positive `Lq` norms. -/
theorem normalized_eLpNorm_le_of_exp_bound
    (h_meas : Measurable X)
    (h_int : ∀ θ, Integrable (fun ω ↦ Real.exp (θ * X ω)) μ)
    (hX : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (hm : 1 ≤ m) (hbound : mgf X μ 1 ≤ Real.exp (B * m))
    {q : ℝ} (hq : 0 < q) :
    eLpNorm (fun ω ↦ X ω / m) (ENNReal.ofReal q) μ ≤
      ENNReal.ofReal ((q ^ q * (Real.exp B + 1)) ^ q⁻¹) := by
  have hZ : AEStronglyMeasurable (fun ω ↦ X ω / m) μ := by fun_prop
  have hrpow : Integrable (fun ω ↦ |X ω / m| ^ q) μ := by
    apply integrable_rpow_abs_of_integrable_exp_mul (t := 1) one_ne_zero ?_ ?_ hq.le
    · exact normalized_exp_integrable h_int 1
    · exact normalized_exp_integrable h_int (-1)
  have hq0 : ENNReal.ofReal q ≠ 0 := (ENNReal.ofReal_pos.mpr hq).ne'
  have hMem : MemLp (fun ω ↦ X ω / m) (ENNReal.ofReal q) μ :=
    (integrable_norm_rpow_iff hZ hq0 ENNReal.ofReal_ne_top).mp (by
      simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le] using hrpow)
  rw [hMem.eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top]
  simp only [Real.norm_eq_abs, ENNReal.toReal_ofReal hq.le]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow (integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (normalized_moment_le_of_exp_bound h_int hX hm hbound hq.le) (inv_nonneg.mpr hq.le)

/-- Exponential moments upgrade the already proved probability convergence of
nonnegative normalized variables to every finite real `Lp` convergence. -/
theorem normalized_tendsto_Lp_of_eventual_exp_bound
    {Ξ : ℕ → Type*} [∀ n, MeasurableSpace (Ξ n)]
    {ν : ∀ n, Measure (Ξ n)} [∀ n, IsProbabilityMeasure (ν n)]
    {Z : ∀ n, Ξ n → ℝ} {a : ℕ → ℝ} {B : ℝ}
    (hZ : ∀ n, Measurable (Z n))
    (h_int : ∀ n θ, Integrable (fun ω ↦ Real.exp (θ * Z n ω)) (ν n))
    (h_nonneg : ∀ n, ∀ᵐ ω ∂ν n, 0 ≤ Z n ω)
    (h_exp : ∀ᶠ n in atTop, mgf (Z n) (ν n) 1 ≤ Real.exp (B * a n))
    (ha : Tendsto a atTop atTop)
    (h_tail : ∀ ε > 0, Tendsto (fun n ↦ ν n {ω | ε ≤ |Z n ω / a n - 1|})
      atTop (𝓝 0)) {r : ℝ} (hr : 1 ≤ r) :
    Tendsto (fun n ↦ eLpNorm (fun ω ↦ Z n ω / a n - 1)
      (ENNReal.ofReal r) (ν n)) atTop (𝓝 0) := by
  let K : ℝ≥0∞ := ENNReal.ofReal (((r + 1) ^ (r + 1) *
    (Real.exp B + 1)) ^ (r + 1)⁻¹)
  have hq : 0 < r + 1 := by linarith
  apply tendsto_eLpNorm_of_tail_and_higher_moment (fun n ↦ by fun_prop)
    hr (lt_add_one r) (C := K + 1) (by finiteness)
  · filter_upwards [ha.eventually_ge_atTop 1, h_exp] with n hn hexp
    have hconst : eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) = 1 := by
      rw [eLpNorm_const' _ (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top]
      simp
    calc
      _ ≤ eLpNorm (fun ω ↦ Z n ω / a n) (ENNReal.ofReal (r + 1)) (ν n) +
          eLpNorm (fun _ : Ξ n ↦ (1 : ℝ)) (ENNReal.ofReal (r + 1)) (ν n) :=
        eLpNorm_sub_le (by simpa using ENNReal.ofReal_le_ofReal (show 1 ≤ r + 1 by linarith))
      _ ≤ K + 1 := by
        rw [hconst]
        exact add_le_add (normalized_eLpNorm_le_of_exp_bound
          (hZ n) (h_int n) (h_nonneg n) hn hexp hq) le_rfl
  · intro ε hε
    simpa only [Real.norm_eq_abs] using h_tail ε hε

end FreezingGrowth.Scaling
