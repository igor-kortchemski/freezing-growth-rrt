module

public import FreezingGrowth.ReverseIndexedKernel

/-! Bijections of finite positions preserve uniform ordered distinct pairs. -/

@[expose] public section

namespace FreezingGrowth.ReverseHeightList

open MeasureTheory
open scoped Classical

/-- Extend a finite position bijection to natural numbers. Its values outside
the source position range are irrelevant to the uniform kernel. -/
def positionMap {m n : ℕ} (e : Fin m ≃ Fin n) (i : ℕ) : ℕ :=
  if hi : i < m then (e ⟨i, hi⟩).val else 0

@[simp] theorem positionMap_fin {m n : ℕ} (e : Fin m ≃ Fin n) (i : Fin m) :
    positionMap e i.val = (e i).val := by
  simp [positionMap, i.isLt]

theorem positionMap_lt {m n i : ℕ} (e : Fin m ≃ Fin n) (hi : i < m) :
    positionMap e i < n := by
  simpa only [positionMap, dite_eq_left hi] using (e ⟨i, hi⟩).isLt

theorem positionMap_injOn {m n : ℕ} (e : Fin m ≃ Fin n) :
    Set.InjOn (positionMap e) (Finset.range m) := by
  intro i hi j hj he
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  simp only [positionMap, dite_eq_left hi', dite_eq_left hj'] at he
  exact congrArg (fun a : Fin m => a.val) (e.injective (Fin.ext he))

def positionPair {m n : ℕ} (e : Fin m ≃ Fin n) (p : ℕ × ℕ) : ℕ × ℕ :=
  (positionMap e p.1, positionMap e p.2)

theorem positionPair_injOn {m n : ℕ} (e : Fin m ≃ Fin n) :
    Set.InjOn (positionPair e) (Finset.range m).offDiag := by
  intro p hp q hq he
  obtain ⟨hp₁, hp₂, _⟩ := Finset.mem_offDiag.mp hp
  obtain ⟨hq₁, hq₂, _⟩ := Finset.mem_offDiag.mp hq
  exact Prod.ext (positionMap_injOn e hp₁ hq₁ (congrArg Prod.fst he))
    (positionMap_injOn e hp₂ hq₂ (congrArg Prod.snd he))

theorem positionPair_image {m n : ℕ} (e : Fin m ≃ Fin n) :
    ((Finset.range m).offDiag.image (positionPair e)) = (Finset.range n).offDiag := by
  ext p
  constructor
  · intro hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hq
    exact Finset.mem_offDiag.mpr
      ⟨Finset.mem_range.mpr (positionMap_lt e (Finset.mem_range.mp ha)),
        Finset.mem_range.mpr (positionMap_lt e (Finset.mem_range.mp hb)),
        fun he => hab (positionMap_injOn e ha hb he)⟩
  · intro hp
    obtain ⟨ha, hb, hab⟩ := Finset.mem_offDiag.mp hp
    let a : Fin n := ⟨p.1, Finset.mem_range.mp ha⟩
    let b : Fin n := ⟨p.2, Finset.mem_range.mp hb⟩
    have hne : (e.symm a).val ≠ (e.symm b).val := by
      intro he
      have he' : a = b := e.symm.injective (Fin.ext he)
      exact hab (congrArg Fin.val he')
    refine Finset.mem_image.mpr
      ⟨((e.symm a).val, (e.symm b).val), Finset.mem_offDiag.mpr
        ⟨Finset.mem_range.mpr (e.symm a).isLt,
          Finset.mem_range.mpr (e.symm b).isLt, hne⟩, ?_⟩
    simp only [positionPair, positionMap_fin, Equiv.apply_symm_apply, a, b]

/-- Actual uniform sampling over ordered distinct positions is equivariant
under a position bijection, including empty pair spaces. -/
theorem map_uniformRootPair_positions {m n : ℕ} (e : Fin m ≃ Fin n) :
    (uniformRootPair (Finset.range m)).map (positionPair e) =
      uniformRootPair (Finset.range n) := by
  unfold uniformRootPair
  rw [map_uniformOfFinset_of_injOn _ _ (measurable_of_countable _)
    (positionPair_injOn e), positionPair_image e]

/-- The pair kernel is supported on its exact finite sample space. -/
theorem uniformRootPair_ae_offDiag (s : Finset ℕ) :
    ∀ᵐ p ∂uniformRootPair s, p ∈ s.offDiag := by
  rw [ae_iff]
  simp [uniformRootPair, Measure.uniformOfFinset_apply]

end FreezingGrowth.ReverseHeightList
