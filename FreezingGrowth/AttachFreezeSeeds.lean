module

public import FreezingGrowth.SeededPrefixExpectations

/-! The exact six equally weighted branches of attachment followed by freezing
from a two-active-vertex height profile. Repeated depths retain their
multiplicities, and freezing the new child retains its contribution to the
maximum over all vertices. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped Classical ENNReal

theorem transitionLaw_triple (a b c M : ℕ) (sign : Bool) :
    transitionLaw ⟨{a, b, c}, M⟩ sign = (3 : ℝ≥0∞)⁻¹ •
      (Measure.dirac (step ⟨{a, b, c}, M⟩ sign a) +
        Measure.dirac (step ⟨{a, b, c}, M⟩ sign b) +
          Measure.dirac (step ⟨{a, b, c}, M⟩ sign c)) := by
  rw [transitionLaw, ite_eq_right (by simp), ProfileCompute.ofMultiset_eq_inverse_smul,
    Measure.map_smul _ measurable_from_top.aemeasurable]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.sum_cons, Multiset.sum_singleton]
  norm_num only [Multiset.card_cons, Multiset.card_singleton]
  rw [Measure.map_add _ _ measurable_from_top, Measure.map_dirac' measurable_from_top,
    Measure.map_add _ _ measurable_from_top, Measure.map_dirac' measurable_from_top,
    Measure.map_dirac' measurable_from_top]
  rw [add_assoc]

theorem freeze_triple_first (a b c M : ℕ) :
    freeze ⟨{a, b, c}, M⟩ a = ⟨{b, c}, M⟩ := by
  simp [freeze, Multiset.insert_eq_cons]

theorem freeze_triple_second (a b c M : ℕ) :
    freeze ⟨{a, b, c}, M⟩ b = ⟨{a, c}, M⟩ := by
  apply HeightProfile.ext
  · change (a ::ₘ b ::ₘ {c}).erase b = a ::ₘ {c}
    rw [Multiset.erase_cons_tail_of_mem (by simp), Multiset.erase_cons_head]
  · rfl

theorem freeze_triple_third (a b c M : ℕ) :
    freeze ⟨{a, b, c}, M⟩ c = ⟨{a, b}, M⟩ := by
  apply HeightProfile.ext
  · change (a ::ₘ b ::ₘ {c}).erase c = a ::ₘ {b}
    rw [Multiset.erase_cons_tail_of_mem (by simp),
      Multiset.erase_cons_tail_of_mem (by simp), Multiset.erase_singleton,
      Multiset.cons_zero]
  · rfl

theorem freeze_triple_law (a b c M : ℕ) :
    transitionLaw ⟨{a, b, c}, M⟩ false = (3 : ℝ≥0∞)⁻¹ •
      (Measure.dirac ⟨{b, c}, M⟩ + Measure.dirac ⟨{a, c}, M⟩ +
        Measure.dirac ⟨{a, b}, M⟩) := by
  rw [transitionLaw_triple]
  simp only [step, Bool.false_eq_true, ↓reduceIte, freeze_triple_first,
    freeze_triple_second, freeze_triple_third]

private theorem pair_profile_swap (a b M : ℕ) :
    (⟨{a, b}, M⟩ : HeightProfile) = ⟨{b, a}, M⟩ := by
  congr 1
  exact Multiset.pair_comm _ _

/-- The six branches are counted separately, even when their profiles coincide.
The maximum is raised before the child can be frozen. -/
theorem attach_freeze_pair_law (a b M : ℕ) :
    (transitionLaw ⟨{a, b}, M⟩ true).bind (fun p => transitionLaw p false) =
      (6 : ℝ≥0∞)⁻¹ •
        (Measure.dirac ⟨{a, b}, max M (a + 1)⟩ +
          Measure.dirac ⟨{a + 1, b}, max M (a + 1)⟩ +
          Measure.dirac ⟨{a, a + 1}, max M (a + 1)⟩ +
          Measure.dirac ⟨{a, b}, max M (b + 1)⟩ +
          Measure.dirac ⟨{b, b + 1}, max M (b + 1)⟩ +
          Measure.dirac ⟨{a, b + 1}, max M (b + 1)⟩) := by
  rw [transitionLaw_pair, Measure.bind_smul _ _ measurable_from_top.aemeasurable,
    ProfileCompute.bind_add_measurable _ _ _ measurable_from_top,
    Measure.dirac_bind measurable_from_top, Measure.dirac_bind measurable_from_top]
  simp only [step, ↓reduceIte, attach]
  change (2 : ℝ≥0∞)⁻¹ •
      (transitionLaw ⟨{a + 1, a, b}, max M (a + 1)⟩ false +
        transitionLaw ⟨{b + 1, a, b}, max M (b + 1)⟩ false) = _
  rw [freeze_triple_law, freeze_triple_law,
    pair_profile_swap (a + 1) a (max M (a + 1)),
    pair_profile_swap (b + 1) b (max M (b + 1)),
    pair_profile_swap (b + 1) a (max M (b + 1)), ← smul_add, smul_smul]
  have hweight : (2 : ℝ≥0∞)⁻¹ * (3 : ℝ≥0∞)⁻¹ = (6 : ℝ≥0∞)⁻¹ := by
    calc
      _ = ((2 : ℝ≥0∞) * 3)⁻¹ :=
        (ENNReal.mul_inv (Or.inr (by norm_num)) (Or.inr (by norm_num))).symm
      _ = _ := by norm_num
  rw [hweight]
  congr 1
  ac_rfl

/-- Any further all-attachment continuation preserves the exact six-branch
mixture and each branch's raised maximum. -/
theorem attach_freeze_pair_grow_law (a b M n : ℕ) :
    ((transitionLaw ⟨{a, b}, M⟩ true).bind (fun p => transitionLaw p false)).bind
      (fun p => grow p n) =
      (6 : ℝ≥0∞)⁻¹ •
        (grow ⟨{a, b}, max M (a + 1)⟩ n +
          grow ⟨{a + 1, b}, max M (a + 1)⟩ n +
          grow ⟨{a, a + 1}, max M (a + 1)⟩ n +
          grow ⟨{a, b}, max M (b + 1)⟩ n +
          grow ⟨{b, b + 1}, max M (b + 1)⟩ n +
          grow ⟨{a, b + 1}, max M (b + 1)⟩ n) := by
  rw [attach_freeze_pair_law, Measure.bind_smul _ _ measurable_from_top.aemeasurable]
  simp only [ProfileCompute.bind_add_measurable _ _ _ measurable_from_top,
    Measure.dirac_bind measurable_from_top]

end FreezingGrowth.HeightProfile
