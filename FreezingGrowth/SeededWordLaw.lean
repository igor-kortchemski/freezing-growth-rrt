module

public import FreezingGrowth.SeededHeightLaw

/-! Finite-word continuations and the small prefixes in Proposition 1.1(iii). -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped Classical ENNReal

noncomputable def wordLaw (xs : Word) : Measure HeightProfile := law xs.toSigns xs.length

theorem wordLaw_append_replicate (xs : Word) (n : ℕ) :
    wordLaw (xs ++ List.replicate n true) =
      (wordLaw xs).bind (fun p => grow p n) := by
  induction n with
  | zero => simp [wordLaw, grow, Measure.bind_dirac]
  | succ n ih =>
    rw [List.replicate_succ', ← List.append_assoc,
      show wordLaw ((xs ++ List.replicate n true) ++ [true]) =
        (wordLaw (xs ++ List.replicate n true)).bind (fun p => transitionLaw p true) from
          ProfileCompute.profile_law_append_singleton _ _, ih,
      Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    rfl

theorem short_prefix_table : ProfileCompute.run [true, false] =
    [(⟨[0], 1⟩, 1), (⟨[1], 1⟩, 1)] := by decide +kernel

theorem long_prefix_table : ProfileCompute.run [true, true, false] =
    [(⟨[0, 1], 1⟩, 2), (⟨[0, 1], 2⟩, 1), (⟨[0, 2], 2⟩, 1),
      (⟨[1, 1], 1⟩, 1), (⟨[1, 2], 2⟩, 1)] := by decide +kernel

theorem short_word_law (n : ℕ) :
    wordLaw ([true, false] ++ List.replicate n true) =
      (2 : ℝ≥0∞)⁻¹ • (grow ⟨{0}, 1⟩ n + grow ⟨{1}, 1⟩ n) := by
  rw [wordLaw_append_replicate, wordLaw, ProfileCompute.run_normalized_law,
    short_prefix_table]
  simp only [ProfileCompute.totalWeight, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, one_add_one_eq_two,
    ProfileCompute.tableMeasure_cons, ProfileCompute.tableMeasure_nil, one_smul, add_zero,
    ProfileCode.decode]
  rw [Measure.bind_smul _ _ measurable_from_top.aemeasurable,
    ProfileCompute.bind_add_measurable _ _ _ measurable_from_top,
    Measure.dirac_bind measurable_from_top, Measure.dirac_bind measurable_from_top]
  norm_num

theorem long_word_law (n : ℕ) :
    wordLaw ([true, true, false] ++ List.replicate n true) =
      (6 : ℝ≥0∞)⁻¹ •
        (2 • grow ⟨{0, 1}, 1⟩ n + grow ⟨{0, 1}, 2⟩ n + grow ⟨{0, 2}, 2⟩ n +
          grow ⟨{1, 1}, 1⟩ n + grow ⟨{1, 2}, 2⟩ n) := by
  rw [wordLaw_append_replicate, wordLaw, ProfileCompute.run_normalized_law,
    long_prefix_table]
  norm_num only [ProfileCompute.totalWeight, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.cast_ofNat, ProfileCompute.tableMeasure_cons,
    ProfileCompute.tableMeasure_nil, one_smul, add_zero, ProfileCode.decode]
  rw [Measure.bind_smul _ _ measurable_from_top.aemeasurable]
  simp only [ProfileCompute.bind_add_measurable _ _ _ measurable_from_top,
    Measure.bind_smul _ _ measurable_from_top.aemeasurable,
    Measure.dirac_bind measurable_from_top]
  congr 1
  ac_rfl

end FreezingGrowth.HeightProfile
