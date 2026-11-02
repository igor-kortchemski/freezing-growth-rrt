module

public import FreezingGrowth.PWIT.FirstBirth
import Mathlib.MeasureTheory.Integral.Prod

/-! Height distribution functions and the first-birth integral identity. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped Classical

noncomputable def heightCDF (h : ℕ) (t : ℝ) : ℝ :=
  law.real (reaches (h + 1) t)ᶜ

theorem heightCDF_nonneg (h : ℕ) (t : ℝ) : 0 ≤ heightCDF h t := measureReal_nonneg

theorem heightCDF_le_one (h : ℕ) (t : ℝ) : heightCDF h t ≤ 1 := measureReal_le_one

theorem heightCDF_antitone (h : ℕ) : Antitone (heightCDF h) := by
  intro s t hst
  exact measureReal_mono (Set.compl_subset_compl.mpr (reaches_mono_time hst))

@[fun_prop] theorem measurable_heightCDF (h : ℕ) : Measurable (heightCDF h) :=
  (heightCDF_antitone h).measurable

theorem heightCDF_eq_one_of_nonpos (h : ℕ) {t : ℝ} (ht : t ≤ 0) : heightCDF h t = 1 := by
  have he : (reaches (h + 1) t)ᶜ =ᵐ[law] Set.univ := by
    filter_upwards [ae_all_birth_pos] with ω hω
    simp only [Set.mem_compl_iff, Set.mem_univ, eq_iff_iff, iff_true]
    rintro ⟨v, hv, hb⟩
    have hv' : v ≠ [] := by intro hh; simp [hh] at hv
    have := hω v hv'
    linarith
  exact (measureReal_congr he).trans probReal_univ

/-- The birth-event family is jointly measurable in the residual-time shift. -/
theorem measurableSet_shifted_reaches (d : ℕ) (t : ℝ) :
    MeasurableSet {p : ℝ × Sample | p.2 ∈ reaches d (t - p.1)} := by
  have he : {p : ℝ × Sample | p.2 ∈ reaches d (t - p.1)} =
      ⋃ v : {v : Vertex // v.length = d}, {p | birth p.2 v.1 ≤ t - p.1} := by
    ext p
    simp [reaches]
  rw [he]
  exact MeasurableSet.iUnion fun v => measurableSet_le
    ((measurable_birth v.1).comp measurable_snd) (measurable_const.sub measurable_fst)

/-- The integral equation before separating the exponential tail above time t. -/
theorem heightCDF_firstBirth_integral (h : ℕ) (t : ℝ) :
    heightCDF (h + 1) t =
      ∫ s : ℝ, heightCDF (h + 1) (t - s) * heightCDF h (t - s) ∂clockLaw := by
  let S : Set (ℝ × (Sample × Sample)) :=
    {p | p.2.1 ∉ reaches (h + 2) (t - p.1) ∧ p.2.2 ∉ reaches (h + 1) (t - p.1)}
  have hS : MeasurableSet S := by
    have h1 : MeasurableSet {p : ℝ × (Sample × Sample) |
        p.2.1 ∉ reaches (h + 2) (t - p.1)} :=
      (measurableSet_shifted_reaches (h + 2) t).compl.preimage
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h2 : MeasurableSet {p : ℝ × (Sample × Sample) |
        p.2.2 ∉ reaches (h + 1) (t - p.1)} :=
      (measurableSet_shifted_reaches (h + 1) t).compl.preimage
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
    exact h1.inter h2
  have he : law.real (reaches (h + 1 + 1) t)ᶜ =
      (clockLaw.prod (law.prod law)).real S := by
    rw [← firstBirth_joint_law, map_measureReal_apply
      (measurable_firstClock.prodMk (measurable_leftSample.prodMk measurable_rightSample)) hS]
    apply measureReal_congr
    filter_upwards [] with ω
    change (ω ∉ reaches (h + 1 + 1) t) =
      (leftSample ω ∉ reaches (h + 1 + 1) (t - firstClock ω) ∧
        rightSample ω ∉ reaches (h + 1) (t - firstClock ω))
    apply propext
    simpa only [not_or] using not_congr (reaches_succ_firstBirth ω (h + 1) t)
  change law.real (reaches (h + 1 + 1) t)ᶜ = _
  rw [he]
  have hint : Integrable (S.indicator (fun _ => (1 : ℝ))) (clockLaw.prod (law.prod law)) := by
    exact (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS]
  change (∫ p, S.indicator (fun _ => (1 : ℝ)) p ∂clockLaw.prod (law.prod law)) = _
  rw [integral_prod _ hint]
  apply integral_congr_ae
  filter_upwards [] with s
  have hrect : (fun p : Sample × Sample => S.indicator (fun _ => (1 : ℝ)) (s, p)) =
      (((reaches (h + 2) (t - s))ᶜ) ×ˢ ((reaches (h + 1) (t - s))ᶜ)).indicator (fun _ => 1) := rfl
  rw [hrect]
  calc
    _ = (law.prod law).real (((reaches (h + 2) (t - s))ᶜ) ×ˢ
        ((reaches (h + 1) (t - s))ᶜ)) := integral_indicator_one
          ((measurableSet_reaches (h + 2) (t - s)).compl.prod
            (measurableSet_reaches (h + 1) (t - s)).compl)
    _ = _ := measureReal_prod_prod _ _

end FreezingGrowth.PWIT
