module

public import FreezingGrowth.PWIT.SimplexBridge
public import FreezingGrowth.PWIT.LeadingSplit

/-! Concatenation retains the actual independent-clock law and its prefix sums. -/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem map_append_finiteClockLaw (m n : ℕ) :
    ((finiteClockLaw m).prod (finiteClockLaw n)).map
        (fun z => Fin.append z.1 z.2) = finiteClockLaw (m + n) := by
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)).symm
  let f := MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ)
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
  have h₁ := measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin m ⊕ Fin n => clockLaw)
  have h₂ := measurePreserving_piCongrLeft (fun _ : Fin (m + n) => clockLaw)
    (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))
  have he : (fun z : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append z.1 z.2) = f ∘ e := by
    funext z i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp [f, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply,
        MeasurableEquiv.coe_sumPiEquivProdPi_symm]
  rw [he]
  exact (h₂.comp h₁).map_eq

@[fun_prop] theorem measurable_append (m n : ℕ) :
    Measurable (fun z : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append z.1 z.2) := by
  apply Measurable.of_eval
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [Fin.append_left, Fin.append_right] <;> fun_prop

theorem map_append_three_finiteClockLaw (m n : ℕ) :
    ((finiteClockLaw m).prod ((finiteClockLaw m).prod (finiteClockLaw n))).map
        (fun z => Fin.append z.1 (Fin.append z.2.2 z.2.1)) =
      finiteClockLaw (m + (n + m)) := by
  let inner : (Fin m → ℝ) × (Fin n → ℝ) → Fin (n + m) → ℝ :=
    fun z => Fin.append z.2 z.1
  have him : Measurable inner := (measurable_append n m).comp measurable_swap
  have hi : ((finiteClockLaw m).prod (finiteClockLaw n)).map inner =
      finiteClockLaw (n + m) := by
    change ((finiteClockLaw m).prod (finiteClockLaw n)).map
      ((fun z : (Fin n → ℝ) × (Fin m → ℝ) => Fin.append z.1 z.2) ∘ Prod.swap) = _
    rw [← Measure.map_map (measurable_append n m) measurable_swap,
      Measure.prod_swap, map_append_finiteClockLaw]
  have hprod := Measure.map_prod_map (finiteClockLaw m)
    ((finiteClockLaw m).prod (finiteClockLaw n)) measurable_id him
  rw [Measure.map_id, hi] at hprod
  have he : (fun z : (Fin m → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ)) =>
      Fin.append z.1 (Fin.append z.2.2 z.2.1)) =
      (fun z : (Fin m → ℝ) × (Fin (n + m) → ℝ) => Fin.append z.1 z.2) ∘
        Prod.map id inner := rfl
  rw [he, ← Measure.map_map (measurable_append m (n + m)) (by fun_prop),
    ← hprod, map_append_finiteClockLaw]

theorem totalWait_append {m n : ℕ} (x : Fin m → ℝ) (y : Fin n → ℝ) :
    totalWait (Fin.append x y) = totalWait x + totalWait y := by
  simp only [totalWait, ← List.sum_ofFn, List.ofFn_fin_append, List.sum_append]

theorem vectorPrefix_nonneg {d : ℕ} {x : Fin d → ℝ} (hx : ∀ i, 0 ≤ x i)
    (j : ℕ) (hj : j ≤ d) : 0 ≤ ((List.ofFn x).take j).sum := by
  rw [take_ofFn_eq _ j hj, List.sum_ofFn]
  exact Finset.sum_nonneg fun i _ => hx (i.castLE hj)

theorem vectorPrefix_le_total {d : ℕ} {x : Fin d → ℝ} (hx : ∀ i, 0 ≤ x i)
    (j : ℕ) : ((List.ofFn x).take j).sum ≤ totalWait x := by
  have h := (List.take_sublist j (List.ofFn x)).sum_le_sum (by
    intro z hz
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hx i)
  simpa only [List.sum_ofFn, totalWait] using h

/-- Scaling a nonnegative unit simplex vector to a total at least its length
preserves the unit-chord lower bound with the same allowance. -/
theorem vectorPrefix_unit_scale_lower {d : ℕ} (hd : 0 < d) {a M : ℝ}
    {p : Fin d → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : totalWait p = 1)
    (hM : (d : ℝ) ≤ M) (hL : vectorLeading a ((d : ℝ) • p))
    (j : ℕ) (hj : j ≤ d) :
    (j : ℝ) - a ≤ ((List.ofFn (M • p)).take j).sum := by
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hh := hL ⟨j, by omega⟩
  have hscaled : (∑ i, ((d : ℝ) • p) i) = d := by
    change totalWait ((d : ℝ) • p) = d
    rw [totalWait_smul, hsum, mul_one]
  rw [hscaled, div_mul_cancel₀ _ hdp.ne', vectorPrefix_smul _ _ j hj] at hh
  rw [vectorPrefix_smul _ _ j hj]
  have hnonneg := vectorPrefix_nonneg hp j hj
  have hmul := mul_nonneg (sub_nonneg.mpr hM) hnonneg
  nlinarith

/-- A leading short block of total at most its length provides the lower
bound needed near the end of the full padded path. -/
theorem vectorPrefix_unit_scale_tail {d : ℕ} (hd : 0 < d) {V : ℝ}
    {p : Fin d → ℝ} (hp : ∀ i, 0 ≤ p i) (hsum : totalWait p = 1)
    (hV : V ≤ d) (hL : vectorLeading 0 p) (j : ℕ) (hj : j ≤ d) :
    V - d + j ≤ ((List.ofFn (V • p)).take j).sum := by
  have hdp : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hh := hL ⟨j, by omega⟩
  change (j : ℝ) / d * totalWait p - 0 ≤ ((List.ofFn p).take j).sum at hh
  rw [hsum, mul_one, sub_zero] at hh
  have hchord := (div_le_iff₀ hdp).mp hh
  have hupper := vectorPrefix_le_total hp j
  rw [hsum] at hupper
  have hmul := mul_nonneg (sub_nonneg.mpr hV) (sub_nonneg.mpr hupper)
  rw [vectorPrefix_smul _ _ j hj]
  nlinarith

/-- Prefix bounds adapted to the three different chords imply that the whole
concatenation lies above its unit-slope chord. -/
theorem vectorLeading_append_three_of_prefix_bounds {m n : ℕ}
    (x₁ : Fin m → ℝ) (x₂ : Fin m → ℝ) (x₃ : Fin n → ℝ) (a : ℝ)
    (hN : 0 < m + (n + m))
    (htotal : totalWait x₁ + totalWait x₃ + totalWait x₂ = (m + (n + m) : ℕ))
    (hbuffer : (m : ℝ) + a ≤ totalWait x₁)
    (hfirst : ∀ j ≤ m, (j : ℝ) ≤ ((List.ofFn x₁).take j).sum)
    (hmiddle : ∀ j ≤ n, (j : ℝ) - a ≤ ((List.ofFn x₃).take j).sum)
    (hlast : ∀ j ≤ m, totalWait x₂ - m + j ≤ ((List.ofFn x₂).take j).sum) :
    vectorLeading 0 (Fin.append x₁ (Fin.append x₃ x₂)) := by
  have hNp : (0 : ℝ) < (m + (n + m) : ℕ) := Nat.cast_pos.mpr hN
  have hsum : (∑ i, Fin.append x₁ (Fin.append x₃ x₂) i) = (m + (n + m) : ℕ) := by
    change totalWait (Fin.append x₁ (Fin.append x₃ x₂)) = _
    rw [totalWait_append, totalWait_append]
    linarith
  intro j
  rw [hsum, div_mul_cancel₀ _ hNp.ne', sub_zero]
  by_cases hjm : (j : ℕ) ≤ m
  · rw [vectorPrefix_append_left _ _ j hjm]
    exact hfirst j hjm
  · have hmj : m ≤ (j : ℕ) := by omega
    let k := (j : ℕ) - m
    have hj : (j : ℕ) = m + k := by omega
    change (j : ℝ) ≤ ((List.ofFn (Fin.append x₁ (Fin.append x₃ x₂))).take j).sum
    rw [hj, vectorPrefix_append_right, Nat.cast_add]
    by_cases hkn : k ≤ n
    · rw [vectorPrefix_append_left _ _ k hkn]
      have hh := hmiddle k hkn
      change (m : ℝ) + k ≤ totalWait x₁ + ((List.ofFn x₃).take k).sum
      linarith
    · have hnk : n ≤ k := by omega
      let l := k - n
      have hk : k = n + l := by omega
      have hlm : l ≤ m := by have hjlt := j.isLt; omega
      rw [hk, vectorPrefix_append_right, Nat.cast_add]
      have hh := hlast l hlm
      have htotal' : totalWait x₁ + totalWait x₃ + totalWait x₂ =
          (m : ℝ) + (n : ℝ) + m := by
        simpa only [Nat.cast_add, add_assoc] using htotal
      change (m : ℝ) + ((n : ℝ) + l) ≤
        totalWait x₁ + (totalWait x₃ + ((List.ofFn x₂).take l).sum)
      linarith

/-- The deterministic three-block padding step on canonical simplex vectors.
Both short blocks use their forward leading event. -/
theorem vectorLeading_simplex_padding {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {a U V M : ℝ} (ha : 0 ≤ a)
    (hU : (m : ℝ) + a ≤ U) (hV : V ≤ m) (hM : (n : ℝ) ≤ M)
    (htotal : U + M + V = (m + (n + m) : ℕ))
    {p₁ p₂ : Fin m → ℝ} {p₃ : Fin n → ℝ}
    (hp₁ : ∀ i, 0 ≤ p₁ i) (hp₂ : ∀ i, 0 ≤ p₂ i) (hp₃ : ∀ i, 0 ≤ p₃ i)
    (hs₁ : totalWait p₁ = 1) (hs₂ : totalWait p₂ = 1) (hs₃ : totalWait p₃ = 1)
    (hL₁ : vectorLeading 0 p₁) (hL₂ : vectorLeading 0 p₂)
    (hL₃ : vectorLeading a ((n : ℝ) • p₃)) :
    vectorLeading 0 (Fin.append (U • p₁) (Fin.append (M • p₃) (V • p₂))) := by
  have hmp : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hL₁' : vectorLeading 0 ((m : ℝ) • p₁) := by
    rw [vectorLeading_smul_iff hmp]
    simpa only [zero_div] using hL₁
  apply vectorLeading_append_three_of_prefix_bounds (a := a)
  · omega
  · simpa only [totalWait_smul, hs₁, hs₂, hs₃, mul_one] using htotal
  · simpa only [totalWait_smul, hs₁, mul_one] using hU
  · intro j hj
    simpa only [sub_zero] using
      vectorPrefix_unit_scale_lower hm hp₁ hs₁ (by linarith : (m : ℝ) ≤ U) hL₁' j hj
  · intro j hj
    exact vectorPrefix_unit_scale_lower hn hp₃ hs₃ hM hL₃ j hj
  · intro j hj
    simpa only [totalWait_smul, hs₂, mul_one] using
      vectorPrefix_unit_scale_tail hm hp₂ hs₂ hV hL₂ j hj

end FreezingGrowth.PWIT
