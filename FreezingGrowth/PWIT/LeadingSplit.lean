module

public import FreezingGrowth.PWIT.VectorLeading

/-! Deterministic chord comparisons for the common-ancestor decomposition.
Every assertion is pointwise; no clock independence is used here. -/

@[expose] public section
namespace FreezingGrowth.PWIT

theorem prefix_chord_bound {i j n S Z Δ : ℝ}
    (hij : i ≤ j) (hj : 0 < j) (hn : 0 < n) (hΔ : 0 ≤ Δ)
    (hS : S = j / n * Z + Δ) :
    i / j * S - Δ ≤ i / n * Z := by
  have hcoef : i / j ≤ 1 := (div_le_one hj).mpr hij
  have he : (i / j * S - Δ) - i / n * Z = (i / j - 1) * Δ := by
    rw [hS]
    field_simp
    ring
  have hh : (i / j - 1) * Δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hΔ
  linarith

theorem suffix_chord_bound {i j q S Z Δ : ℝ}
    (hi : 0 ≤ i) (hj : 0 ≤ j) (hq : 0 < q) (hΔ : 0 ≤ Δ)
    (hS : S = j / (j + q) * Z + Δ) :
    i / q * (Z - S) - Δ ≤ (j + i) / (j + q) * Z - S := by
  have hn : 0 < j + q := by linarith
  have he : ((j + i) / (j + q) * Z - S) - (i / q * (Z - S) - Δ) = i / q * Δ := by
    rw [hS]
    field_simp
    ring
  have hh : 0 ≤ i / q * Δ := by positivity
  linarith

theorem sum_append_vector {j q : ℕ} (x : Fin j → ℝ) (y : Fin q → ℝ) :
    (∑ i, Fin.append x y i) = (∑ i, x i) + ∑ i, y i := by
  rw [← List.sum_ofFn, List.ofFn_fin_append, List.sum_append, List.sum_ofFn, List.sum_ofFn]

theorem vectorPrefix_append_left {j q : ℕ} (x : Fin j → ℝ) (y : Fin q → ℝ)
    (i : ℕ) (hi : i ≤ j) :
    ((List.ofFn (Fin.append x y)).take i).sum = ((List.ofFn x).take i).sum := by
  rw [List.ofFn_fin_append, List.take_append_of_le_length (by simpa using hi)]

theorem vectorPrefix_append_right {j q : ℕ} (x : Fin j → ℝ) (y : Fin q → ℝ) (i : ℕ) :
    ((List.ofFn (Fin.append x y)).take (j + i)).sum =
      (∑ k, x k) + ((List.ofFn y).take i).sum := by
  rw [List.ofFn_fin_append]
  have he := List.take_length_add_append (l₁ := List.ofFn x) (l₂ := List.ofFn y) i
  simpa only [List.length_ofFn, List.sum_append, List.sum_ofFn] using congrArg List.sum he

/-- A leading path forces a near-leading condition on both pieces, with the
same nonnegative excess of the splitting point above the full chord. -/
theorem vectorLeading_split {j q : ℕ} (hj : 0 < j) (hq : 0 < q)
    {x : Fin j → ℝ} {y : Fin q → ℝ} (h : vectorLeading 0 (Fin.append x y)) :
    let Z : ℝ := (∑ i, x i) + ∑ i, y i
    let Δ : ℝ := (∑ i, x i) - (j : ℝ) / (j + q : ℕ) * Z
    0 ≤ Δ ∧ vectorLeading Δ x ∧ vectorLeading Δ y := by
  dsimp only
  let Z : ℝ := (∑ i, x i) + ∑ i, y i
  let Δ : ℝ := (∑ i, x i) - (j : ℝ) / (j + q : ℕ) * Z
  have hjr : (0 : ℝ) < j := Nat.cast_pos.mpr hj
  have hqr : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hnr : (0 : ℝ) < (j + q : ℕ) := by positivity
  have hsum : (∑ i, x i) = (j : ℝ) / (j + q : ℕ) * Z + Δ := by dsimp [Δ]; ring
  have h0 := h ⟨j, by omega⟩
  simp only [sub_zero, sum_append_vector, vectorPrefix_append_left x y j le_rfl] at h0
  have htake : (List.ofFn x).take j = List.ofFn x := by
    simpa only [List.length_ofFn] using (List.take_length (l := List.ofFn x))
  rw [htake, List.sum_ofFn] at h0
  have hΔ : 0 ≤ Δ := sub_nonneg.mpr h0
  refine ⟨hΔ, ?_, ?_⟩
  · intro i
    have hi := h ⟨i, by omega⟩
    simp only [sub_zero, sum_append_vector,
      vectorPrefix_append_left x y i (by omega)] at hi
    exact (prefix_chord_bound (by exact_mod_cast (by omega : (i : ℕ) ≤ j))
      hjr hnr hΔ hsum).trans hi
  · intro i
    have hi := h ⟨j + i, by omega⟩
    simp only [sub_zero, sum_append_vector, vectorPrefix_append_right, Nat.cast_add] at hi
    have hsum' : (∑ i, x i) = (j : ℝ) / ((j : ℝ) + q) * Z + Δ := by
      simpa only [Nat.cast_add] using hsum
    have hc := suffix_chord_bound (Nat.cast_nonneg (α := ℝ) (i : ℕ)) hjr.le hqr hΔ hsum'
    dsimp [Z] at hc
    have he : (∑ k, x k) + (∑ k, y k) - (∑ k, x k) = ∑ k, y k := by ring
    rw [he] at hc
    linarith

/-- The same allowance, expressed using a common endpoint-window center.
It can therefore be used simultaneously for two paths sharing a prefix. -/
theorem vectorLeading_split_window {j q : ℕ} (hj : 0 < j) (hq : 0 < q)
    {x : Fin j → ℝ} {y : Fin q → ℝ} {m : ℝ}
    (h : vectorLeading 0 (Fin.append x y))
    (hwin : m - 1 ≤ (∑ i, x i) + ∑ i, y i) :
    let A : ℝ := (∑ i, x i) - (j : ℝ) / (j + q : ℕ) * m + 1
    0 ≤ A ∧ vectorLeading A x ∧ vectorLeading A y := by
  obtain ⟨hΔ, hx, hy⟩ := vectorLeading_split hj hq h
  let Z : ℝ := (∑ i, x i) + ∑ i, y i
  let Δ : ℝ := (∑ i, x i) - (j : ℝ) / (j + q : ℕ) * Z
  let A : ℝ := (∑ i, x i) - (j : ℝ) / (j + q : ℕ) * m + 1
  have hn : (0 : ℝ) < (j + q : ℕ) := by positivity
  have hα0 : 0 ≤ (j : ℝ) / (j + q : ℕ) := by positivity
  have hα1 : (j : ℝ) / (j + q : ℕ) ≤ 1 := by
    apply (div_le_one hn).mpr
    exact_mod_cast (Nat.le_add_right j q)
  have hh : (j : ℝ) / (j + q : ℕ) * (m - Z) ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_left (show m - Z ≤ 1 by dsimp [Z]; linarith) hα0
    linarith
  have hle : Δ ≤ A := by dsimp [Δ, A]; nlinarith
  exact ⟨hΔ.trans hle, vectorLeading_mono hle hx, vectorLeading_mono hle hy⟩

end FreezingGrowth.PWIT
