module

public import FreezingGrowth.ForwardHeight
public import FreezingGrowth.MGFConcentration
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The normalized depth of a uniform recursive-tree vertex

For the all-attachment schedule every vertex is active. We first identify the
existing active-height law with uniform sampling from all vertices, including
the root. Its scale is `harmonic (n + 1) - 1`, and the already proved forward
MGF bound gives convergence of depth divided by `log n` to one in probability.

This proves the normalized reading of the claim at `main.tex`, line 648,
directly. It does not assume the cited depth theorem or any asymptotic result
about the maximum height. The manuscript omits the normalization in that
sentence; its proof only needs the upper-tail corollary below.
-/

@[expose] public section

namespace FreezingGrowth.RRT

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

/-- The recursive tree with `n` edges is the forward tree after `n` attachments. -/
def allAttach : SignSequence := fun _ => true

@[simp]
theorem activeCount_allAttach (n : ℕ) : activeCount allAttach n = (n : ℤ) + 1 := by
  simp [activeCount, allAttach, add_comm]

theorem positive_allAttach (n : ℕ) : PositiveThrough allAttach n := by
  intro k _
  rw [activeCount_allAttach]
  omega

theorem before_extinction (n : ℕ) : (n : ℕ∞) < extinctionTime allAttach :=
  (lt_extinctionTime_iff allAttach n).mpr (positive_allAttach n)

/-- Under pure attachment the active and full vertex sets coincide almost surely. -/
theorem active_eq_vertices (n : ℕ) :
    ∀ᵐ s ∂Forward.treeLaw allAttach n, s.active = s.vertices := by
  apply Forward.treeLaw_ae_induction allAttach (fun _ s => s.active = s.vertices)
  · rfl
  · intro _ _ hs _
    exact hs
  · intro k s hs v hv
    rw [Forward.step, ite_eq_left hv]
    simp [allAttach, Forward.attach, hs]

/-- Depth of a vertex chosen conditionally uniformly from the whole recursive tree. -/
noncomputable def uniformVertexDepthLaw (n : ℕ) : Measure ℕ :=
  Forward.uniformActiveHeightLaw allAttach n

instance uniformVertexDepthLaw_probability (n : ℕ) :
    IsProbabilityMeasure (uniformVertexDepthLaw n) :=
  Forward.uniformActiveHeightLaw_probability allAttach n

/-- The sampling definition uses every vertex, including the root, of the actual tree. -/
theorem uniformVertexDepthLaw_eq_bind_vertices (n : ℕ) :
    uniformVertexDepthLaw n = (Forward.treeLaw allAttach n).bind
      (fun s => (Measure.uniformOfFinset s.vertices).map s.height) := by
  unfold uniformVertexDepthLaw Forward.uniformActiveHeightLaw
  apply Measure.bind_congr_right
  filter_upwards [active_eq_vertices n, Forward.treeLaw_valid allAttach n] with s hs hv
  have hne : s.active.Nonempty := by
    rw [hs]
    exact ⟨0, hv.root_mem⟩
  change (if s.active.Nonempty then (Measure.uniformOfFinset s.active).map s.height
    else Measure.dirac 0) = _
  rw [ite_eq_left hne, hs]

theorem heightScale_eq_shiftedHarmonic (n : ℕ) :
    heightScale allAttach n = shiftedHarmonic n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [heightScale_succ, shiftedHarmonic_succ, ih, activeCount_allAttach]
    simp only [allAttach, ↓reduceIte, Int.cast_add, Int.cast_natCast,
      Int.cast_one, Nat.cast_add, Nat.cast_one]
    congr 2; ring

theorem shiftedHarmonic_eq_harmonic (n : ℕ) :
    shiftedHarmonic n = (harmonic (n + 1) : ℝ) - 1 := by
  induction n with
  | zero => norm_num [harmonic_succ]
  | succ n ih =>
    rw [shiftedHarmonic_succ, ih, harmonic_succ (n + 1)]
    push_cast
    ring

/-- The deterministic mean scale has the logarithmic normalization required by E5. -/
theorem heightScale_div_log_tendsto_one :
    Tendsto (fun n : ℕ => heightScale allAttach n / Real.log (n : ℝ)) atTop (𝓝 1) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hn
  have hrecip : Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (hn.comp (tendsto_add_atTop_nat 1))
  have hdiff : Tendsto (fun n : ℕ => heightScale allAttach n - Real.log (n : ℝ))
      atTop (𝓝 (Real.eulerMascheroniConstant - 1)) := by
    have h := (Real.tendsto_harmonic_sub_log.add hrecip).sub
      (tendsto_const_nhds (x := (1 : ℝ)))
    simp only [add_zero] at h
    convert h using 1
    funext n
    rw [heightScale_eq_shiftedHarmonic, shiftedHarmonic_eq_harmonic, harmonic_succ]
    push_cast
    ring
  have hh := (hdiff.div_atTop hlog).add (tendsto_const_nhds (x := (1 : ℝ)))
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  field_simp [hn.ne']
  ring

/-- Finite two-sided concentration comes from the actual uniform-vertex MGF. -/
theorem uniformVertexDepthLaw_bennett {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 < t) :
    (uniformVertexDepthLaw n).real {k | heightScale allAttach n + t < (k : ℝ)} ≤
        Real.exp (-heightScale allAttach n * bennettRate (t / heightScale allAttach n)) ∧
    (uniformVertexDepthLaw n).real {k | (k : ℝ) < heightScale allAttach n - t} ≤
        Real.exp (-heightScale allAttach n * bennettRate (t / heightScale allAttach n)) :=
  bennett_tails_of_mgf_bound
    (Forward.uniformActiveHeightLaw_integrable_exp allAttach n)
    (Forward.uniformActiveHeightLaw_mgf_le allAttach n (before_extinction n))
    (heightScale_pos hn (positive_allAttach n)) ht

/-- Corrected E5: uniform recursive-tree vertex depth divided by `log n`
converges in probability to one. There is no asymptotic hypothesis. -/
theorem uniformVertexDepthLaw_deviation_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (uniformVertexDepthLaw n).real
      {k : ℕ | ε ≤ |(k : ℝ) / Real.log (n : ℝ) - 1|}) atTop (𝓝 0) := by
  let m : ℕ → ℝ := fun n => heightScale allAttach n
  let α : ℝ := ε / 2
  have hα : 0 < α := half_pos hε
  have hm : Tendsto m atTop atTop :=
    tendsto_heightScale_atTop (fun _ => allAttach) positive_allAttach
  have hscale : Tendsto (fun n : ℕ => m n / Real.log (n : ℝ)) atTop (𝓝 1) :=
    heightScale_div_log_tendsto_one
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hu : Tendsto (fun n : ℕ => (m n + α * m n) / Real.log (n : ℝ))
      atTop (𝓝 (1 + α)) := by
    convert hscale.add (hscale.const_mul α) using 1
    · funext n
      ring
    · simp
  have hl : Tendsto (fun n : ℕ => (m n - α * m n) / Real.log (n : ℝ))
      atTop (𝓝 (1 - α)) := by
    convert hscale.sub (hscale.const_mul α) using 1
    · funext n
      ring
    · simp
  have hrate : 0 < bennettRate α := by
    have hh := Real.self_sub_one_lt_mul_log (x := 1 + α) (by linarith) (by linarith)
    unfold bennettRate
    linarith
  have he : Tendsto (fun n : ℕ => Real.exp (-m n * bennettRate α)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul] using
      Real.tendsto_exp_atBot.comp
        (tendsto_neg_atTop_atBot.comp (hm.atTop_mul_const hrate))
  have he2 : Tendsto (fun n : ℕ => 2 * Real.exp (-m n * bennettRate α))
      atTop (𝓝 0) := by simpa using he.const_mul 2
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ he2
  filter_upwards [eventually_ge_atTop 1, hlog.eventually_gt_atTop 0,
    hu.eventually (gt_mem_nhds (show 1 + α < 1 + ε by dsimp [α]; linarith)),
    hl.eventually (lt_mem_nhds (show 1 - ε < 1 - α by dsimp [α]; linarith))]
    with n hn hln hun hln'
  have hmn : 0 < m n := heightScale_pos hn (positive_allAttach n)
  obtain ⟨hup, hlow⟩ := uniformVertexDepthLaw_bennett hn (mul_pos hα hmn)
  have hratio : α * m n / m n = α := by field_simp [hmn.ne']
  change (uniformVertexDepthLaw n).real {k | m n + α * m n < (k : ℝ)} ≤
    Real.exp (-m n * bennettRate (α * m n / m n)) at hup
  change (uniformVertexDepthLaw n).real {k | (k : ℝ) < m n - α * m n} ≤
    Real.exp (-m n * bennettRate (α * m n / m n)) at hlow
  rw [hratio] at hup hlow
  have hsub : {k : ℕ | ε ≤ |(k : ℝ) / Real.log (n : ℝ) - 1|} ⊆
      {k : ℕ | m n + α * m n < (k : ℝ)} ∪
        {k : ℕ | (k : ℝ) < m n - α * m n} := by
    intro k hk
    change ε ≤ |(k : ℝ) / Real.log (n : ℝ) - 1| at hk
    change m n + α * m n < (k : ℝ) ∨ (k : ℝ) < m n - α * m n
    rcases le_abs.mp hk with hk | hk
    · left
      have hrat : 1 + ε ≤ (k : ℝ) / Real.log (n : ℝ) := by linarith
      exact (div_lt_div_iff_of_pos_right hln).mp (hun.trans_le hrat)
    · right
      have hrat : (k : ℝ) / Real.log (n : ℝ) ≤ 1 - ε := by linarith
      exact (div_lt_div_iff_of_pos_right hln).mp (hrat.trans_lt hln')
  calc
    _ ≤ (uniformVertexDepthLaw n).real
        ({k : ℕ | m n + α * m n < (k : ℝ)} ∪
          {k : ℕ | (k : ℝ) < m n - α * m n}) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (uniformVertexDepthLaw n).real {k : ℕ | m n + α * m n < (k : ℝ)} +
        (uniformVertexDepthLaw n).real {k : ℕ | (k : ℝ) < m n - α * m n} :=
      measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-m n * bennettRate α) := by linarith

/-- In particular the depth tail at `1.1 log n`, used in the height-increment
argument, tends to zero. The statement holds for every constant greater than one. -/
theorem uniformVertexDepthLaw_upper_tail_tendsto_zero {c : ℝ} (hc : 1 < c) :
    Tendsto (fun n : ℕ => (uniformVertexDepthLaw n).real
      {k : ℕ | c * Real.log (n : ℝ) ≤ (k : ℝ)}) atTop (𝓝 0) := by
  have hdev := uniformVertexDepthLaw_deviation_tendsto_zero (sub_pos.mpr hc)
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_ hdev
  filter_upwards [hlog.eventually_gt_atTop 0] with n hn
  apply measureReal_mono _ (measure_ne_top _ _)
  intro k hk
  change c * Real.log (n : ℝ) ≤ (k : ℝ) at hk
  change c - 1 ≤ |(k : ℝ) / Real.log (n : ℝ) - 1|
  have hd : c ≤ (k : ℝ) / Real.log (n : ℝ) := (le_div_iff₀ hn).mpr hk
  exact (show c - 1 ≤ (k : ℝ) / Real.log (n : ℝ) - 1 by linarith).trans (le_abs_self _)

end FreezingGrowth.RRT
