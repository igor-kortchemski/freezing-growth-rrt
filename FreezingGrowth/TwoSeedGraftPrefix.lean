module

public import FreezingGrowth.TwoSeedGraftCoupling

/-! The actual freezing/attachment prefix under the common ordered pair. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory
open scoped Classical ENNReal

private theorem uniform_pair {α : Type*} [MeasurableSpace α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    Measure.uniformOfFinset ({a, b} : Finset α) =
      (2 : ℝ≥0∞)⁻¹ • (Measure.dirac a + Measure.dirac b) := by
  simp [Measure.uniformOfFinset, hab]

theorem uniformRootPair_pair (a b : ℕ) (hab : a ≠ b) :
    uniformRootPair ({a, b} : Finset ℕ) =
      (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (a, b) + Measure.dirac (b, a)) := by
  have he : ({a, b} : Finset ℕ).offDiag = {(a, b), (b, a)} := by
    ext p
    simp only [Finset.mem_offDiag, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [uniformRootPair, he, uniform_pair]
  intro h
  exact hab (congrArg Prod.fst h)

theorem transition_pair (s : Forward.State) (t : ℕ) (sign : Bool) {a b : ℕ}
    (hs : s.active = {a, b}) (hab : a ≠ b) :
    Forward.transitionLaw s t sign = (2 : ℝ≥0∞)⁻¹ •
      (Measure.dirac (Forward.step s t sign a) + Measure.dirac (Forward.step s t sign b)) := by
  have hne : s.active.Nonempty := by rw [hs]; simp
  rw [Forward.transitionLaw, ite_eq_left hne, hs, uniform_pair a b hab,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _), Measure.map_dirac' (measurable_of_countable _)]

private theorem bind_add (μ ν : Measure Forward.State) (K : Forward.State → Measure Forward.State) :
    (μ + ν).bind K = μ.bind K + ν.bind K := by
  ext A hA
  simp only [Measure.bind_apply hA measurable_from_top.aemeasurable,
    Measure.add_apply, lintegral_add_measure]

theorem freeze_attach_pair (s : Forward.State) (T : ℕ) {a b : ℕ}
    (hs : s.active = {a, b}) (hab : a ≠ b) :
    (Forward.transitionLaw s (T + 1) false).bind
        (fun q => Forward.transitionLaw q (T + 2) true) =
      (uniformRootPair s.active).map (fun p =>
        Forward.attach (Forward.freeze s (T + 1) p.2) (T + 2) p.1) := by
  have ha : a ∈ s.active := by rw [hs]; simp
  have hb : b ∈ s.active := by rw [hs]; simp
  have hfa : (Forward.freeze s (T + 1) a).active = {b} := by
    simp [Forward.freeze, hs, hab]
  have hfb : (Forward.freeze s (T + 1) b).active = {a} := by
    change s.active.erase b = {a}
    rw [hs]
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [transition_pair s (T + 1) false hs hab,
    Measure.bind_smul _ _ measurable_from_top.aemeasurable, bind_add,
    Measure.dirac_bind measurable_from_top, Measure.dirac_bind measurable_from_top]
  simp only [Forward.step, ite_eq_left ha, ite_eq_left hb, Bool.false_eq_true, ↓reduceIte]
  rw [Forward.transitionLaw, ite_eq_left (by rw [hfa]; simp), hfa,
    Forward.transitionLaw, ite_eq_left (by rw [hfb]; simp), hfb]
  simp only [Measure.uniformOfFinset, Finset.card_singleton, Nat.cast_one, inv_one,
    one_smul, Finset.sum_singleton, Measure.map_dirac' (measurable_of_countable _)]
  simp only [Forward.step, hfa, hfb, Finset.mem_singleton, ↓reduceIte]
  rw [hs, uniformRootPair_pair a b hab,
    Measure.map_smul _ (measurable_of_countable _).aemeasurable,
    Measure.map_add _ _ (measurable_of_countable _),
    Measure.map_dirac' (measurable_of_countable _), Measure.map_dirac' (measurable_of_countable _)]
  congr 1
  exact add_comm _ _

theorem stateSampleLaw_longPrefix (s : Forward.State) {T : ℕ} (_hs : Forward.ValidAt T s)
    (hc : s.active.card = 2) (n : ℕ) :
    (stateSampleLaw s n).map (longPrefixState T) =
      (Forward.transitionLaw s (T + 1) false).bind
        (fun q => Forward.transitionLaw q (T + 2) true) := by
  obtain ⟨a, b, hab, hsab⟩ := Finset.card_eq_two.mp hc
  rw [freeze_attach_pair s T hsab hab, stateSampleLaw,
    Measure.map_bind (measurable_of_countable _).aemeasurable measurable_from_top.aemeasurable]
  calc
    _ = (uniformRootPair s.active).bind (fun p => Measure.dirac
        (Forward.attach (Forward.freeze s (T + 1) p.2) (T + 2) p.1)) := by
      apply Measure.bind_congr_right
      exact Filter.Eventually.of_forall (fun p => by
        dsimp only
        rw [Measure.map_map measurable_from_top measurable_from_top]
        change (Forward.treeLaw RRT.allAttach (n + 1)).map (fun _ =>
          Forward.attach (Forward.freeze s (T + 1) p.2) (T + 2) p.1) = _
        rw [Measure.map_const, measure_univ, one_smul])
    _ = _ := Measure.bind_dirac_eq_map _ (measurable_of_countable _)

end FreezingGrowth.TwoSeedGraft
