module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Density transport and finite product densities

These measure identities support the exponential-spacing bridge. They concern
actual measures and do not condition on an endpoint of probability zero.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory
open scoped ENNReal BigOperators

theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {T : α → β} (hT : Measurable T)
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (fun x => f (T x))).map T = (μ.map T).withDensity f := by
  ext s hs
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs),
    withDensity_apply _ hs, setLIntegral_map hs hf hT]

theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  have h := map_withDensity_comp μ e.measurable (hf.comp e.symm.measurable)
  have he : (fun x => (f ∘ e.symm) (e x)) = f := by
    funext x
    simp only [Function.comp_apply, e.symm_apply_apply]
  rw [he] at h
  exact h

/-- A product of unnormalized factors with total mass one is the product of
its probability marginals. Thus unknown polar normalization constants cancel. -/
theorem prod_eq_prod_marginals {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    [IsProbabilityMeasure (μ.prod ν)] :
    μ.prod ν = ((μ.prod ν).map Prod.fst).prod ((μ.prod ν).map Prod.snd) := by
  have hm : μ Set.univ * ν Set.univ = 1 := by
    rw [← Measure.prod_prod, Set.univ_prod_univ, measure_univ]
  rw [Measure.map_fst_prod, Measure.map_snd_prod,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    mul_comm, hm, one_smul]

theorem finitePi_withDensity {d : ℕ} (μ : Fin d → Measure ℝ)
    [∀ i, SigmaFinite (μ i)] (f : Fin d → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hfinite : ∀ i x, f i x ≠ ∞) :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  classical
  induction d with
  | zero =>
    have he : (fun i : Fin 0 => (μ i).withDensity (f i)) = μ := by
      funext i
      exact i.elim0
    simp only [he, Finset.univ_eq_empty, Finset.prod_empty]
    exact (withDensity_one (μ := Measure.pi μ)).symm
  | succ d ih =>
    let (i : Fin (d + 1)) : SigmaFinite ((μ i).withDensity (f i)) :=
      MeasureTheory.SigmaFinite.withDensity_of_ne_top' (hfinite i)
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
    apply e.measurableEmbedding.map_injective
    rw [(measurePreserving_piFinSuccAbove (fun i => (μ i).withDensity (f i)) 0).map_eq,
      map_withDensity_equiv _ e (by fun_prop),
      (measurePreserving_piFinSuccAbove μ 0).map_eq]
    simp only [Fin.zero_succAbove]
    rw [ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ)
      (fun i => hfinite i.succ), prod_withDensity (hf 0) (by fun_prop)]
    congr 1
    funext x
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.prod_univ_succ]

end FreezingGrowth.PWIT
