module

public import FreezingGrowth.AlternatingHeightBounds
public import FreezingGrowth.LowPopulationAsymptotic
public import FreezingGrowth.FirstPeakDeletion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The alternating tree has height asymptotic to half its edge count

This is the alternating-tree claim at main.tex 330–339 (E8). The finite word
has n attachments and n freezes. Its deterministic height scale is n/2.
The direct forward maximum upper tail and active-vertex lower tail prove the
limit without importing an unproved asymptotic statement from the citation.
-/

@[expose] public section

namespace FreezingGrowth

open MeasureTheory Filter
open scoped Topology

/-- The source word `(+,−)^n`, with exactly `2*n` operations. -/
def alternatingWord (n : ℕ) : Word := (List.replicate n [true, false]).flatten

/-- An infinite extension used only at the finite alternating horizon. -/
def alternatingSigns : SignSequence := fun i => decide (i % 2 = 1)

@[simp] theorem alternatingWord_zero : alternatingWord 0 = [] := rfl

theorem alternatingWord_succ (n : ℕ) :
    alternatingWord (n + 1) = alternatingWord n ++ [true, false] := by
  simp [alternatingWord, List.replicate_add, List.flatten_append]

@[simp] theorem alternatingWord_length (n : ℕ) : (alternatingWord n).length = 2 * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [alternatingWord_succ, List.length_append, ih]; simp; omega

/-- The finite word and infinite schedule agree at every operation read. -/
theorem alternatingWord_toSigns (n : ℕ) :
    ∀ i < 2 * n, (alternatingWord n).toSigns (i + 1) = alternatingSigns (i + 1) := by
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    rw [alternatingWord_succ]
    by_cases h : i < 2 * n
    · rw [Word.toSigns_append_left _ _ (by simpa using h)]
      exact ih i h
    · have hcases : i = 2 * n ∨ i = 2 * n + 1 := by omega
      rcases hcases with rfl | rfl
      · simp [alternatingWord_length, Word.toSigns, alternatingSigns, Nat.add_mod]
      · simp [alternatingWord_length, Word.toSigns, alternatingSigns, Nat.add_assoc]

/-- The population alternates between one and two and never becomes extinct. -/
theorem alternating_activeCount (n : ℕ) :
    activeCount alternatingSigns n = if n % 2 = 0 then 1 else 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [activeCount_succ, ih]
    by_cases he : n % 2 = 0
    · have ho : (n + 1) % 2 = 1 := by omega
      simp [alternatingSigns, he, ho]
    · have ho : n % 2 = 1 := by omega
      have hn : (n + 1) % 2 = 0 := by omega
      simp [alternatingSigns, ho, hn]

theorem alternating_positiveThrough (n : ℕ) : PositiveThrough alternatingSigns n := by
  intro k _
  rw [alternating_activeCount]
  split_ifs <;> norm_num

theorem alternating_before_extinction (n : ℕ) : (n : ℕ∞) < extinctionTime alternatingSigns :=
  (lt_extinctionTime_iff alternatingSigns n).mpr (alternating_positiveThrough n)

theorem alternatingWord_admissible (n : ℕ) : (alternatingWord n).admissible := by
  intro j hj
  have hj' : j < 2 * n := by simpa using hj
  rw [Word.activeCount_congr (fun i hi => alternatingWord_toSigns n i (by omega))]
  exact alternating_positiveThrough (2 * n) j hj'.le

@[simp] theorem alternatingWord_attachments (n : ℕ) : (alternatingWord n).attachments = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [alternatingWord_succ, Word.attachments_append, ih]
    have hpair : Word.attachments [true, false] = 1 := by decide +kernel
    rw [hpair]

theorem alternatingWord_inFamily (n : ℕ) : Word.InFamily n (alternatingWord n) :=
  ⟨alternatingWord_admissible n, alternatingWord_attachments n⟩

theorem alternating_heightScale (n : ℕ) : heightScale alternatingSigns (2 * n) = (n : ℝ) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
      heightScale_succ, heightScale_succ, ih]
    simp [alternatingSigns, alternating_activeCount, Nat.add_mod]
    ring

/-- Exact finite-word bridge to the actual forward tree at its `2*n` horizon. -/
theorem alternatingWord_heightLaw (n : ℕ) :
    (alternatingWord n).heightLaw = Forward.heightLaw alternatingSigns (2 * n) := by
  unfold Word.heightLaw
  rw [alternatingWord_length]
  exact Forward.heightLaw_congr (alternatingWord_toSigns n)

theorem alternatingWord_heightLaw_real (n : ℕ) (E : Set ℕ) :
    (alternatingWord n).heightLaw.real E =
      (Forward.treeLaw alternatingSigns (2 * n)).real {s | Forward.treeHeight s ∈ E} := by
  rw [alternatingWord_heightLaw]
  unfold Forward.heightLaw Measure.real
  rw [Measure.map_apply measurable_from_top (by trivial)]
  rfl

/-- Both strict deviation tails have an explicit exponentially vanishing bound. -/
theorem alternating_height_deviation_bound (n : ℕ) (hn : 1 ≤ n) {ε : ℝ}
    (hε : 0 < ε) (hmargin : 1 ≤ ε * (n : ℝ) / 2) :
    (alternatingWord n).heightLaw.real {h : ℕ | ε < |(h : ℝ) / n - 1 / 2|} ≤
      (2 * (n : ℝ) + 2) * Real.exp (-(n : ℝ) / 2 * bennettRate ε) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ht : 0 < ε * (n : ℝ) / 2 := by positivity
  have hlow := Forward.treeHeight_lower_tail alternatingSigns (2 * n) (by omega)
    (alternating_before_extinction _) ht
  have hupp := Forward.treeHeight_upper_tail alternatingSigns (2 * n) (by omega)
    (alternating_before_extinction _) ht
  rw [alternating_heightScale] at hlow hupp
  have hratio : (ε * (n : ℝ) / 2) / ((n : ℝ) / 2) = ε := by field_simp
  rw [hratio] at hlow hupp
  rw [alternatingWord_heightLaw_real]
  let lower : Set Forward.State := {s | (Forward.treeHeight s : ℝ) <
    (n : ℝ) / 2 - ε * (n : ℝ) / 2}
  let upper : Set Forward.State := {s | (n : ℝ) / 2 + 1 + ε * (n : ℝ) / 2 <
    (Forward.treeHeight s : ℝ)}
  have hsub : {s : Forward.State | ε < |(Forward.treeHeight s : ℝ) / n - 1 / 2|}
      ⊆ lower ∪ upper := by
    intro s hs
    change ε < |(Forward.treeHeight s : ℝ) / n - 1 / 2| at hs
    rcases lt_abs.mp hs with hs | hs
    · right
      dsimp [upper]
      have hh : (1 / 2 + ε) * n < (Forward.treeHeight s : ℝ) :=
        (lt_div_iff₀ hnR).mp (by linarith : 1 / 2 + ε < (Forward.treeHeight s : ℝ) / n)
      nlinarith
    · left
      dsimp [lower]
      have hh : (Forward.treeHeight s : ℝ) < (1 / 2 - ε) * n :=
        (div_lt_iff₀ hnR).mp (by linarith : (Forward.treeHeight s : ℝ) / n < 1 / 2 - ε)
      nlinarith
  calc
    _ ≤ (Forward.treeLaw alternatingSigns (2 * n)).real (lower ∪ upper) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (Forward.treeLaw alternatingSigns (2 * n)).real lower +
        (Forward.treeLaw alternatingSigns (2 * n)).real upper := measureReal_union_le _ _
    _ ≤ Real.exp (-(n : ℝ) / 2 * bennettRate ε) +
        ((2 * n : ℕ) + 1) * Real.exp (-(n : ℝ) / 2 * bennettRate ε) := by
          simpa only [lower, upper, neg_div] using add_le_add hlow hupp
    _ = _ := by push_cast; ring

/-- A linear prefactor is negligible against the positive Bennett exponent. -/
theorem alternating_error_tendsto_zero {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (2 * (n : ℝ) + 2) *
      Real.exp (-(n : ℝ) / 2 * bennettRate ε)) atTop (𝓝 0) := by
  let b : ℝ := bennettRate ε / 2
  have hb : 0 < b := half_pos (bennettRate_pos hε)
  have hpoly : Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-b * n)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hexp : Tendsto (fun n : ℕ => Real.exp (-b * n)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := tendsto_neg_atTop_atBot.comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hb)
    simpa only [Function.comp_def, neg_mul] using hh
  have hh := (hpoly.const_mul 2).add (hexp.const_mul 2)
  convert hh using 1
  · funext n
    have heq : -(n : ℝ) / 2 * bennettRate ε = -b * n := by dsimp [b]; ring
    rw [heq]
    ring
  · norm_num

/-- E8: the height of the actual alternating tree, divided by its number of
edges, converges in probability to one half. No asymptotic premise is assumed. -/
theorem alternating_height_tendsto_half {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (alternatingWord n).heightLaw.real
      {h : ℕ | ε < |(h : ℝ) / (n : ℝ) - 1 / 2|}) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (alternating_error_tendsto_zero hε)
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 / ε)] with n hn hlarge
  apply alternating_height_deviation_bound n hn hε
  have hh := (div_le_iff₀ hε).mp hlarge
  nlinarith

end FreezingGrowth
