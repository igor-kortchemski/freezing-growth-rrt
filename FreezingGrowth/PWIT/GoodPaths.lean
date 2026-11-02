module

public import FreezingGrowth.PWIT.PathClocks
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Finite good-path counts for the one-sided height argument

These are the rank window and three barriers from Addario-Berry–Ford,
arXiv:1012.2544v3, Sections 4–6, specialized to the actual exponential clock
model. This module only constructs the finite measurable count; it does not
assert the ballot estimates or either moment estimate needed for its success.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable def timeCenter (d : ℕ) : ℝ :=
  (d : ℝ) / Real.exp 1 + 3 * Real.log d / (2 * Real.exp 1)

noncomputable def rankWindowRadius (d : ℕ) : ℝ :=
  Real.sqrt (6 * d * Real.log d)

/-- AF13's `Y_d`, including the full prescribed window of excess ranks. -/
noncomputable def rankWindow (d : ℕ) : Finset Vertex := by
  classical
  exact (Finset.range (⌊(d : ℝ) / Real.exp 1 + rankWindowRadius d⌋₊ + 1)).biUnion
    (fun k => if |(k : ℝ) - (d : ℝ) / Real.exp 1| ≤ rankWindowRadius d
      then rankClass d k else ∅)

/-- `L_a`: the path stays at least `-a` above its endpoint chord. -/
def leading (a : ℝ) (v : Vertex) (ω : Sample) : Prop :=
  ∀ j : Fin (v.length + 1),
    (j : ℝ) / v.length * birth ω v - a ≤ birth ω (v.take j)

/-- `B_a`: an interior prefix comes too close to the endpoint chord. -/
def badInterior (a : ℝ) (v : Vertex) (ω : Sample) : Prop :=
  ∃ j : Fin (v.length + 1),
    a ^ 40 ≤ (j : ℝ) ∧ (j : ℝ) ≤ (v.length : ℝ) - a ^ 40 ∧
    birth ω (v.take j) ≤ (j : ℝ) / v.length * birth ω v +
      (min (j : ℝ) ((v.length : ℝ) - j)) ^ (1 / 40 : ℝ)

/-- `D_a` is deterministic once the child ranks have been fixed. -/
def badRanks (a : ℝ) (v : Vertex) : Prop :=
  ∃ j : Fin (v.length + 1),
    3 * a * (j : ℝ) < rankSum (v.take j) ∨
      3 * a * ((v.length : ℝ) - j) <
        (rankSum v : ℝ) - rankSum (v.take j)

def goodEvent (d : ℕ) (a : ℝ) (v : Vertex) : Set Sample :=
  {ω | timeCenter d - 1 ≤ birth ω v ∧ birth ω v ≤ timeCenter d ∧
    leading a v ω ∧ ¬ badInterior a v ω ∧ ¬ badRanks a v}

noncomputable def goodCount (d : ℕ) (a : ℝ) (ω : Sample) : ℝ :=
  ∑ v ∈ rankWindow d, (goodEvent d a v).indicator (fun _ => (1 : ℝ)) ω

theorem mem_rankWindow {d : ℕ} {v : Vertex} :
    v ∈ rankWindow d ↔ v.length = d ∧
      |(v.sum : ℝ) - (d : ℝ) / Real.exp 1| ≤ rankWindowRadius d := by
  classical
  simp only [rankWindow, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨k, _, hk⟩
    split_ifs at hk with hb
    · obtain ⟨hd, hs⟩ := mem_rankClass.mp hk
      exact ⟨hd, by simpa [hs] using hb⟩
    · simp at hk
  · rintro ⟨hd, hb⟩
    refine ⟨v.sum, ?_, ?_⟩
    · have hu : (v.sum : ℝ) ≤ (d : ℝ) / Real.exp 1 + rankWindowRadius d := by
        have := (abs_le.mp hb).2
        linarith
      exact Nat.lt_succ_of_le (Nat.le_floor hu)
    · rw [ite_eq_left hb]
      exact mem_rankClass.mpr ⟨hd, rfl⟩

theorem measurableSet_leading (a : ℝ) (v : Vertex) :
    MeasurableSet {ω | leading a v ω} := by
  unfold leading
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun j =>
    measurableSet_le (((measurable_birth v).const_mul _).sub_const a)
      (measurable_birth (v.take j))

theorem measurableSet_badInterior (a : ℝ) (v : Vertex) :
    MeasurableSet {ω | badInterior a v ω} := by
  classical
  unfold badInterior
  rw [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro j
  by_cases h₁ : a ^ 40 ≤ (j : ℝ)
  · by_cases h₂ : (j : ℝ) ≤ (v.length : ℝ) - a ^ 40
    · simpa only [h₁, h₂, true_and] using
        measurableSet_le (measurable_birth (v.take j))
          (((measurable_birth v).const_mul _).add_const _)
    · simp [h₂]
  · simp [h₁]

theorem measurableSet_goodEvent (d : ℕ) (a : ℝ) (v : Vertex) :
    MeasurableSet (goodEvent d a v) := by
  classical
  by_cases hr : badRanks a v
  · simp [goodEvent, hr]
  · simpa only [goodEvent, hr, not_false_eq_true, and_true, Set.ofPred_and, Set.compl_ofPred] using
      (measurableSet_le measurable_const (measurable_birth v)).inter
        ((measurableSet_le (measurable_birth v) measurable_const).inter
          ((measurableSet_leading a v).inter (measurableSet_badInterior a v).compl))

@[fun_prop] theorem measurable_goodCount (d : ℕ) (a : ℝ) :
    Measurable (goodCount d a) := by
  unfold goodCount
  exact Finset.measurable_sum _ fun v _ =>
    measurable_const.indicator (measurableSet_goodEvent d a v)

theorem integrable_goodCount (d : ℕ) (a : ℝ) : Integrable (goodCount d a) law := by
  unfold goodCount
  exact integrable_finsetSum _ fun v _ =>
    (integrable_const (1 : ℝ)).indicator (measurableSet_goodEvent d a v)

theorem goodCount_nonneg (d : ℕ) (a : ℝ) (ω : Sample) : 0 ≤ goodCount d a ω := by
  unfold goodCount
  apply Finset.sum_nonneg
  intro v _
  exact Set.indicator_nonneg (fun _ _ => by norm_num) _

theorem goodCount_le_card (d : ℕ) (a : ℝ) (ω : Sample) :
    goodCount d a ω ≤ (rankWindow d).card := by
  classical
  unfold goodCount
  calc
    _ ≤ ∑ _v ∈ rankWindow d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases h : ω ∈ goodEvent d a v <;> simp [h]
    _ = _ := by simp

theorem integrable_goodCount_sq (d : ℕ) (a : ℝ) :
    Integrable (fun ω => goodCount d a ω ^ 2) law := by
  apply (integrable_const (((rankWindow d).card : ℝ) ^ 2)).mono'
    ((measurable_goodCount d a).pow_const 2).aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (goodCount_nonneg d a ω) (goodCount_le_card d a ω) 2

end FreezingGrowth.PWIT
