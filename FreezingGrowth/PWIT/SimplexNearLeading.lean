module

public import FreezingGrowth.PWIT.SimplexPadding
public import FreezingGrowth.PWIT.SimplexConcatenation
public import FreezingGrowth.PWIT.SimplexLeading

/-!
# A uniform near-leading bound for the canonical simplex bridge

Independent Gamma windows and two exact cyclic leading factors pad the
middle bridge to a leading path. All laws are ordinary product measures;
there is no conditioning on a prescribed zero-probability endpoint.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

def simplexSupport (d : ℕ) : Set (Fin d → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ totalWait p = 1}

theorem measurableSet_simplexSupport (d : ℕ) : MeasurableSet (simplexSupport d) := by
  unfold simplexSupport
  have h : MeasurableSet {p : Fin d → ℝ | ∀ i, 0 ≤ p i} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)
  exact h.inter (measurableSet_eq_fun (measurable_totalWait d) measurable_const)

theorem simplexLaw_real_inter_support (d : ℕ) [NeZero d] (E : Set (Fin d → ℝ)) :
    (simplexLaw d).real (E ∩ simplexSupport d) = (simplexLaw d).real E := by
  apply measureReal_congr
  filter_upwards [simplexLaw_ae_nonnegative_sum_one d] with p hp
  have hp' : p ∈ simplexSupport d := hp
  simp only [Set.mem_inter_iff, hp', and_true]

abbrev PaddingBridgeSample (m n : ℕ) :=
  ((Fin m → ℝ) × ℝ) × (((Fin m → ℝ) × ℝ) × ((Fin n → ℝ) × ℝ))

noncomputable def paddingBridgeLaw (m n : ℕ) : Measure (PaddingBridgeSample m n) :=
  ((simplexLaw m).prod (gammaMeasure (m : ℝ) 1)).prod
    (((simplexLaw m).prod (gammaMeasure (m : ℝ) 1)).prod
      ((simplexLaw n).prod (gammaMeasure (n : ℝ) 1)))

instance paddingBridgeLaw_isProbabilityMeasure (m n : ℕ) [NeZero m] [NeZero n] :
    IsProbabilityMeasure (paddingBridgeLaw m n) := by
  have : IsProbabilityMeasure (gammaMeasure (m : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos m)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (n : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos n)) (by norm_num)
  unfold paddingBridgeLaw
  infer_instance

noncomputable def paddingReconstruction {m n : ℕ} (z : PaddingBridgeSample m n) :
    Fin (m + (n + m)) → ℝ :=
  Fin.append (z.1.2 • z.1.1) (Fin.append (z.2.2.2 • z.2.2.1) (z.2.1.2 • z.2.1.1))

@[fun_prop] theorem measurable_paddingReconstruction (m n : ℕ) :
    Measurable (@paddingReconstruction m n) := by
  unfold paddingReconstruction
  have h₁ : Measurable (fun z : PaddingBridgeSample m n => z.1.2 • z.1.1) := by fun_prop
  have h₂ : Measurable (fun z : PaddingBridgeSample m n =>
      (z.2.2.2 • z.2.2.1, z.2.1.2 • z.2.1.1)) := by fun_prop
  exact (measurable_append m (n + m)).comp
    (h₁.prodMk ((measurable_append n m).comp h₂))

theorem map_paddingReconstruction (m n : ℕ) [NeZero m] [NeZero n] :
    (paddingBridgeLaw m n).map paddingReconstruction = finiteClockLaw (m + (n + m)) := by
  have : IsProbabilityMeasure (gammaMeasure (m : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos m)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (n : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos n)) (by norm_num)
  let blocks : PaddingBridgeSample m n → (Fin m → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) :=
    fun z => (z.1.2 • z.1.1, (z.2.1.2 • z.2.1.1, z.2.2.2 • z.2.2.1))
  have hb : Measurable blocks := by unfold blocks; fun_prop
  have hblocks : (paddingBridgeLaw m n).map blocks =
      (finiteClockLaw m).prod ((finiteClockLaw m).prod (finiteClockLaw n)) := by
    rw [finiteClockLaw_eq_scaled_simplex_gamma m, finiteClockLaw_eq_scaled_simplex_gamma n]
    unfold paddingBridgeLaw
    rw [Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
      Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
    rfl
  have he : (@paddingReconstruction m n) =
      (fun z : (Fin m → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
        Fin.append z.1 (Fin.append z.2.2 z.2.1)) ∘ blocks := rfl
  have hcat : Measurable (fun z : (Fin m → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
      Fin.append z.1 (Fin.append z.2.2 z.2.1)) :=
    (measurable_append m (n + m)).comp
      (measurable_fst.prodMk ((measurable_append n m).comp
        (measurable_snd.snd.prodMk measurable_snd.fst)))
  rw [he, ← Measure.map_map hcat hb,
    hblocks, map_append_three_finiteClockLaw]

theorem smul_append_vector {m n : ℕ} (c : ℝ) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    c • Fin.append x y = Fin.append (c • x) (c • y) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Pi.smul_apply, Fin.append_left, Fin.append_right]

/-- Pointwise embedding on the canonical product sample. The Gamma windows
are used before normalizing their sum. -/
theorem paddingReconstruction_leading {m n : ℕ} {a : ℝ} (ha : 10 ≤ a)
    (hm : a ^ 2 ≤ (m : ℝ)) (hm' : (m : ℝ) ≤ a ^ 2 + 1) (hn : a ^ 6 ≤ (n : ℝ))
    (z : PaddingBridgeSample m n)
    (hp₁ : z.1.1 ∈ simplexSupport m) (hp₂ : z.2.1.1 ∈ simplexSupport m)
    (hp₃ : z.2.2.1 ∈ simplexSupport n)
    (hL₁ : vectorLeading 0 z.1.1) (hL₂ : vectorLeading 0 z.2.1.1)
    (hL₃ : vectorLeading a ((n : ℝ) • z.2.2.1))
    (hw₁ : z.1.2 ∈ Icc ((m : ℝ) + 4 * a / 3) ((m : ℝ) + 5 * a / 3))
    (hw₂ : z.2.1.2 ∈ Icc ((m : ℝ) - 8 * a / 3) ((m : ℝ) - 7 * a / 3))
    (hw₃ : z.2.2.2 ∈ Icc ((n : ℝ) - Real.sqrt n) ((n : ℝ) + Real.sqrt n)) :
    vectorLeading 0 (paddingReconstruction z) := by
  have hmp : (0 : ℝ) < m := by nlinarith
  have hnp := (padding_scale_bounds ha hn).1
  have hm0 : 0 < m := Nat.cast_pos.mp hmp
  have hn0 : 0 < n := Nat.cast_pos.mp hnp
  obtain ⟨hT, hU, hV⟩ := simplex_padding_rectangle ha hm hm' hn hw₁ hw₂ hw₃
  let c : ℝ := ((n : ℝ) + 2 * m) / (z.1.2 + z.2.1.2 + z.2.2.2)
  change c * z.1.2 ∈ Icc ((m : ℝ) + a) ((m : ℝ) + 2 * a) at hU
  change c * z.2.1.2 ∈ Icc ((m : ℝ) - 3 * a) ((m : ℝ) - 2 * a) at hV
  have hc : 0 < c := div_pos (by positivity) hT
  have he : c * z.1.2 + c * z.2.2.2 + c * z.2.1.2 = (m + (n + m) : ℕ) := by
    dsimp [c]
    push_cast
    field_simp
    ring
  have hM : (n : ℝ) ≤ c * z.2.2.2 := by
    have he' := he
    push_cast at he'
    linarith [hU.2, hV.2]
  have hL := vectorLeading_simplex_padding hm0 hn0 (show 0 ≤ a by linarith)
    hU.1 (show c * z.2.1.2 ≤ (m : ℝ) by linarith [hV.2]) hM he
    hp₁.1 hp₂.1 hp₃.1 hp₁.2 hp₂.2 hp₃.2 hL₁ hL₂ hL₃
  have hscaled : c • paddingReconstruction z =
      Fin.append ((c * z.1.2) • z.1.1)
        (Fin.append ((c * z.2.2.2) • z.2.2.1) ((c * z.2.1.2) • z.2.1.1)) := by
    simp only [paddingReconstruction, smul_append_vector, smul_smul]
  rw [← hscaled, vectorLeading_smul_iff hc, zero_div] at hL
  exact hL

def simplexNearLeadingEvent (d : ℕ) (a : ℝ) : Set (Fin d → ℝ) :=
  {p | vectorLeading a ((d : ℝ) • p)}

theorem measurableSet_simplexNearLeadingEvent (d : ℕ) (a : ℝ) :
    MeasurableSet (simplexNearLeadingEvent d a) :=
  (measurableSet_vectorLeading d a).preimage (by fun_prop)

noncomputable def paddingLeadingEvent (m n : ℕ) (a : ℝ) : Set (PaddingBridgeSample m n) :=
  (({p | vectorLeading 0 p} ∩ simplexSupport m) ×ˢ
      Icc ((m : ℝ) + 4 * a / 3) ((m : ℝ) + 5 * a / 3)) ×ˢ
    ((({p | vectorLeading 0 p} ∩ simplexSupport m) ×ˢ
        Icc ((m : ℝ) - 8 * a / 3) ((m : ℝ) - 7 * a / 3)) ×ˢ
      ((simplexNearLeadingEvent n a ∩ simplexSupport n) ×ˢ
        Icc ((n : ℝ) - Real.sqrt n) ((n : ℝ) + Real.sqrt n)))

theorem measurableSet_paddingLeadingEvent (m n : ℕ) (a : ℝ) :
    MeasurableSet (paddingLeadingEvent m n a) := by
  exact ((measurableSet_vectorLeading m 0).inter
      (measurableSet_simplexSupport m)).prod measurableSet_Icc |>.prod
    (((measurableSet_vectorLeading m 0).inter
        (measurableSet_simplexSupport m)).prod measurableSet_Icc |>.prod
      (((measurableSet_simplexNearLeadingEvent n a).inter
        (measurableSet_simplexSupport n)).prod measurableSet_Icc))

theorem paddingLeadingEvent_probability (m n : ℕ) [NeZero m] [NeZero n] (a : ℝ) :
    (paddingBridgeLaw m n).real (paddingLeadingEvent m n a) =
      (1 / (m : ℝ)) ^ 2 * (simplexLaw n).real (simplexNearLeadingEvent n a) *
        ((gammaMeasure (m : ℝ) 1).prod
          ((gammaMeasure (m : ℝ) 1).prod (gammaMeasure (n : ℝ) 1))).real
            (Icc ((m : ℝ) + 4 * a / 3) ((m : ℝ) + 5 * a / 3) ×ˢ
              (Icc ((m : ℝ) - 8 * a / 3) ((m : ℝ) - 7 * a / 3) ×ˢ
                Icc ((n : ℝ) - Real.sqrt n) ((n : ℝ) + Real.sqrt n))) := by
  have : IsProbabilityMeasure (gammaMeasure (m : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos m)) (by norm_num)
  have : IsProbabilityMeasure (gammaMeasure (n : ℝ) 1) :=
    isProbabilityMeasure_gammaMeasure (Nat.cast_pos.mpr (NeZero.pos n)) (by norm_num)
  simp only [paddingBridgeLaw, paddingLeadingEvent, measureReal_prod_prod,
    simplexLaw_real_inter_support, simplexLaw_leading_zero_probability]
  ring

/-- The quantitative padding inequality. It contains two short-block cycle
factors, the actual positive Gamma-window mass, and the middle bridge event. -/
theorem simplex_nearLeading_padding_inequality {m n : ℕ} {a : ℝ} (ha : 10 ≤ a)
    (hm : a ^ 2 ≤ (m : ℝ)) (hm' : (m : ℝ) ≤ a ^ 2 + 1) (hn : a ^ 6 ≤ (n : ℝ)) :
    paddingWindowConstant * (1 / (m : ℝ)) ^ 2 *
        (simplexLaw n).real (simplexNearLeadingEvent n a) ≤
      1 / (m + (n + m) : ℕ) := by
  have hmp : (0 : ℝ) < m := by nlinarith
  have hnp := (padding_scale_bounds ha hn).1
  have : NeZero m := ⟨(Nat.cast_pos.mp hmp).ne'⟩
  have : NeZero n := ⟨(Nat.cast_pos.mp hnp).ne'⟩
  have : NeZero (m + (n + m)) := ⟨by have := NeZero.pos m; omega⟩
  have hn17 : 17 ≤ n := by
    have hpow : (10 : ℝ) ^ 6 ≤ a ^ 6 := pow_le_pow_left₀ (by norm_num) ha 6
    exact_mod_cast (show (17 : ℝ) ≤ n by norm_num at hpow; linarith)
  have hsub : paddingLeadingEvent m n a ⊆
      paddingReconstruction ⁻¹' {x | vectorLeading 0 x} := by
    intro z hz
    exact paddingReconstruction_leading ha hm hm' hn z
      hz.1.1.2 hz.2.1.1.2 hz.2.2.1.2 hz.1.1.1 hz.2.1.1.1 hz.2.2.1.1
      hz.1.2 hz.2.1.2 hz.2.2.2
  have hupper : (paddingBridgeLaw m n).real (paddingLeadingEvent m n a) ≤
      1 / (m + (n + m) : ℕ) := by
    calc
      _ ≤ (paddingBridgeLaw m n).real
          (paddingReconstruction ⁻¹' {x | vectorLeading 0 x}) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ = ((paddingBridgeLaw m n).map paddingReconstruction).real
          {x | vectorLeading 0 x} :=
        (map_measureReal_apply (measurable_paddingReconstruction m n)
          (measurableSet_vectorLeading (m + (n + m)) 0)).symm
      _ = _ := by rw [map_paddingReconstruction, finiteClockLaw_leading_zero_probability]
  rw [paddingLeadingEvent_probability] at hupper
  have hlower := mul_le_mul_of_nonneg_left (gamma_three_padding_windows ha hm hm' hn17)
    (show 0 ≤ (1 / (m : ℝ)) ^ 2 * (simplexLaw n).real (simplexNearLeadingEvent n a) by positivity)
  apply le_trans _ hupper
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hlower

theorem simplex_nearLeading_large_allowance {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 10 ≤ a) :
    (simplexLaw n).real (simplexNearLeadingEvent n a) ≤
      (4 / paddingWindowConstant + 1) * a ^ 6 / n := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hc := paddingWindowConstant_pos
  have ha0 : 0 ≤ a := by linarith
  have ha2 : 1 ≤ a ^ 2 := by nlinarith
  have hfactor : 1 ≤ 4 / paddingWindowConstant + 1 := by
    have hh : 0 ≤ 4 / paddingWindowConstant := div_nonneg (by norm_num) hc.le
    linarith
  apply (le_div_iff₀ hnp).mpr
  by_cases hlarge : a ^ 6 ≤ (n : ℝ)
  · let m : ℕ := ⌈a ^ 2⌉₊
    have hm : a ^ 2 ≤ (m : ℝ) := Nat.le_ceil _
    have hm' : (m : ℝ) ≤ a ^ 2 + 1 := (Nat.ceil_lt_add_one (sq_nonneg a)).le
    have hmp : (0 : ℝ) < m := by linarith
    have hN : (0 : ℝ) < (m + (n + m) : ℕ) := by positivity
    have hNn : (n : ℝ) ≤ (m + (n + m) : ℕ) := by push_cast; linarith
    have hpad := simplex_nearLeading_padding_inequality ha hm hm' hlarge
    have hscaled := mul_le_mul_of_nonneg_right hpad
      (show 0 ≤ (m : ℝ) ^ 2 * (m + (n + m) : ℕ) by positivity)
    have he₁ : paddingWindowConstant * (1 / (m : ℝ)) ^ 2 *
        (simplexLaw n).real (simplexNearLeadingEvent n a) *
        ((m : ℝ) ^ 2 * (m + (n + m) : ℕ)) =
          paddingWindowConstant * (simplexLaw n).real (simplexNearLeadingEvent n a) *
            (m + (n + m) : ℕ) := by field_simp
    have he₂ : 1 / (m + (n + m) : ℕ) *
        ((m : ℝ) ^ 2 * (m + (n + m) : ℕ)) = (m : ℝ) ^ 2 := by field_simp
    rw [he₁, he₂] at hscaled
    have hm2 : (m : ℝ) ^ 2 ≤ 4 * a ^ 6 := by
      have hm2a : (m : ℝ) ≤ 2 * a ^ 2 := by linarith
      have hsquare := pow_le_pow_left₀ hmp.le hm2a 2
      have ha46 := mul_nonneg (pow_nonneg ha0 4) (show 0 ≤ a ^ 2 - 1 by linarith)
      nlinarith
    have hPn := mul_le_mul_of_nonneg_left hNn
      (show 0 ≤ paddingWindowConstant * (simplexLaw n).real (simplexNearLeadingEvent n a) by positivity)
    apply (mul_le_mul_iff_right₀ hc).mp
    have he : paddingWindowConstant * ((4 / paddingWindowConstant + 1) * a ^ 6) =
        4 * a ^ 6 + paddingWindowConstant * a ^ 6 := by field_simp
    rw [he]
    have hnonneg : 0 ≤ paddingWindowConstant * a ^ 6 := by positivity
    nlinarith
  · have hprob : (simplexLaw n).real (simplexNearLeadingEvent n a) ≤ 1 := measureReal_le_one
    have hmul := mul_le_mul_of_nonneg_right hprob hnp.le
    have ha6 : (n : ℝ) ≤ a ^ 6 := (not_le.mp hlarge).le
    have hfac := mul_le_mul_of_nonneg_right hfactor (pow_nonneg ha0 6)
    linarith

noncomputable def simplexNearLeadingConstant : ℝ :=
  (4 / paddingWindowConstant + 1) * 10 ^ 6

theorem simplexNearLeadingConstant_pos : 0 < simplexNearLeadingConstant := by
  unfold simplexNearLeadingConstant
  have hc := paddingWindowConstant_pos
  positivity

/-- The canonical endpoint equals the number of increments. This statement
includes every positive dimension and every nonnegative allowance. -/
theorem simplex_nearLeading_canonical_bound {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a) :
    (simplexLaw n).real (simplexNearLeadingEvent n a) ≤
      simplexNearLeadingConstant * (1 + a ^ 6) / n := by
  let b : ℝ := max 10 a
  have hb : 10 ≤ b := le_max_left _ _
  have hab : a ≤ b := le_max_right _ _
  have hmono : (simplexLaw n).real (simplexNearLeadingEvent n a) ≤
      (simplexLaw n).real (simplexNearLeadingEvent n b) := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro p hp
    exact vectorLeading_mono hab hp
  have hb6 : b ^ 6 ≤ 10 ^ 6 * (1 + a ^ 6) := by
    have ha6 : 0 ≤ a ^ 6 := pow_nonneg ha 6
    by_cases hba : 10 ≤ a
    · dsimp [b]
      rw [max_eq_right hba]
      nlinarith
    · dsimp [b]
      rw [max_eq_left (not_le.mp hba).le]
      nlinarith
  apply hmono.trans ((simplex_nearLeading_large_allowance hn hb).trans _)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  unfold simplexNearLeadingConstant
  have hcp := paddingWindowConstant_pos
  have hc : 0 ≤ 4 / paddingWindowConstant + 1 := by positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb6 hc

/-- A uniform ballot bound for every strictly positive prescribed endpoint.
The endpoint is a deterministic scaling of the canonical simplex law. -/
theorem simplex_nearLeading_bound {n : ℕ} (hn : 0 < n) {a S : ℝ}
    (ha : 0 ≤ a) (hS : 0 < S) :
    (simplexLaw n).real {p | vectorLeading a (S • p)} ≤
      simplexNearLeadingConstant * (1 + (a * n / S) ^ 6) / n := by
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hset : {p : Fin n → ℝ | vectorLeading a (S • p)} =
      simplexNearLeadingEvent n (a * n / S) := by
    ext p
    simp only [Set.mem_ofPred_eq, simplexNearLeadingEvent,
      vectorLeading_smul_iff hS, vectorLeading_smul_iff hnp]
    have he : (a * n / S) / n = a / S := by field_simp
    rw [he]
  rw [hset]
  exact simplex_nearLeading_canonical_bound hn (by positivity)

theorem exists_simplex_nearLeading_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 0 < n → ∀ (a S : ℝ), 0 ≤ a → 0 < S →
      (simplexLaw n).real {p | vectorLeading a (S • p)} ≤
        C * (1 + (a * n / S) ^ 6) / n :=
  ⟨simplexNearLeadingConstant, simplexNearLeadingConstant_pos,
    fun _ hn _ _ ha hS => simplex_nearLeading_bound hn ha hS⟩

end FreezingGrowth.PWIT
