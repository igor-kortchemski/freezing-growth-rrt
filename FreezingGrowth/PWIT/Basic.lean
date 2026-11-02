module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Tactic

/-!
# Exponential clocks on the Ulam–Harris tree

An entry `i` of a vertex address denotes child rank `i + 1`. The independent
coordinates are interarrival times, not the cumulative birth delays of siblings.
Only finite path times and measurable generation events are used here.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

abbrev Vertex := List ℕ
abbrev Coordinate := Vertex × ℕ
abbrev Sample := Coordinate → ℝ

noncomputable def clockLaw : Measure ℝ := expMeasure 1

instance : IsProbabilityMeasure clockLaw :=
  isProbabilityMeasure_expMeasure (by norm_num)

noncomputable def law : Measure Sample :=
  Measure.infinitePi fun _ : Coordinate => clockLaw

instance : IsProbabilityMeasure law := by
  unfold law
  infer_instance

/-- The delay from a parent to its child of mathematical rank `i + 1`. -/
def childDelay (ω : Sample) (v : Vertex) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (i + 1), ω (v, j)

/-- The independent coordinates below the child with address `i`. -/
def childSample (ω : Sample) (i : ℕ) : Sample :=
  fun c => ω (i :: c.1, c.2)

/-- Birth time relative to the root, obtained from the finitely many ancestral
delays. The root has time zero. -/
def birth (ω : Sample) : Vertex → ℝ
  | [] => 0
  | i :: v => childDelay ω [] i + birth (childSample ω i) v

@[simp] theorem birth_nil (ω : Sample) : birth ω [] = 0 := rfl

@[simp] theorem birth_cons (ω : Sample) (i : ℕ) (v : Vertex) :
    birth ω (i :: v) = childDelay ω [] i + birth (childSample ω i) v := rfl

@[fun_prop] theorem measurable_childDelay (v : Vertex) (i : ℕ) :
    Measurable (fun ω : Sample => childDelay ω v i) := by
  unfold childDelay
  fun_prop

@[fun_prop] theorem measurable_childSample (i : ℕ) :
    Measurable (fun ω : Sample => childSample ω i) := by
  exact Measurable.of_eval fun c => measurable_pi_apply (i :: c.1, c.2)

@[fun_prop] theorem measurable_birth (v : Vertex) : Measurable (fun ω => birth ω v) := by
  induction v with
  | nil => exact measurable_const
  | cons i v ih =>
    exact (measurable_childDelay [] i).add (ih.comp (measurable_childSample i))

/-- This definition does not assume that a minimum over an infinite generation
has been attained. -/
def reaches (d : ℕ) (t : ℝ) : Set Sample :=
  {ω | ∃ v : Vertex, v.length = d ∧ birth ω v ≤ t}

theorem measurableSet_reaches (d : ℕ) (t : ℝ) : MeasurableSet (reaches d t) := by
  have he : reaches d t = ⋃ v : {v : Vertex // v.length = d},
      {ω | birth ω v.1 ≤ t} := by
    ext ω
    simp [reaches]
  rw [he]
  exact MeasurableSet.iUnion fun v => measurableSet_le (measurable_birth v.1) measurable_const

@[fun_prop] theorem measurable_reaches_indicator (d : ℕ) (t : ℝ) :
    Measurable ((reaches d t).indicator (fun _ : Sample => (1 : ℝ))) :=
  measurable_const.indicator (measurableSet_reaches d t)

theorem map_coordinate (c : Coordinate) : law.map (fun ω => ω c) = clockLaw := by
  exact Measure.infinitePi_map_eval (fun _ : Coordinate => clockLaw) c

theorem independent_clocks : iIndepFun (fun c (ω : Sample) => ω c) law :=
  iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

theorem clockLaw_ae_pos : ∀ᵐ x ∂clockLaw, 0 < x := by
  have hz : clockLaw (Set.Iic 0) = 0 := by
    apply (measureReal_eq_zero_iff).mp
    rw [← cdf_eq_real]
    simp [clockLaw, cdf_expMeasure_eq (by norm_num : (0 : ℝ) < 1)]
  have h := (measure_eq_zero_iff_ae_notMem).mp hz
  simpa using h

/-- Simultaneous positivity is legitimate because the clock index is countable. -/
theorem ae_all_clocks_pos : ∀ᵐ ω ∂law, ∀ c : Coordinate, 0 < ω c := by
  apply ae_all_iff.mpr
  intro c
  apply ae_of_ae_map (measurable_pi_apply c).aemeasurable
  rw [map_coordinate]
  exact clockLaw_ae_pos

theorem childDelay_pos {ω : Sample} (hω : ∀ c, 0 < ω c) (v : Vertex) (i : ℕ) :
    0 < childDelay ω v i := by
  unfold childDelay
  exact Finset.sum_pos (fun j _ => hω (v, j)) (by simp)

theorem birth_nonneg {ω : Sample} (hω : ∀ c, 0 ≤ ω c) (v : Vertex) :
    0 ≤ birth ω v := by
  induction v generalizing ω with
  | nil => simp
  | cons i v ih =>
    rw [birth_cons]
    apply add_nonneg
    · exact Finset.sum_nonneg fun j _ => hω ([], j)
    · exact ih (fun c => hω (i :: c.1, c.2))

theorem birth_pos {ω : Sample} (hω : ∀ c, 0 < ω c) {v : Vertex} (hv : v ≠ []) :
    0 < birth ω v := by
  cases v with
  | nil => exact (hv rfl).elim
  | cons i v =>
    rw [birth_cons]
    exact add_pos_of_pos_of_nonneg (childDelay_pos hω [] i)
      (birth_nonneg (fun c => (hω (i :: c.1, c.2)).le) v)

theorem ae_all_birth_pos : ∀ᵐ ω ∂law, ∀ v : Vertex, v ≠ [] → 0 < birth ω v := by
  filter_upwards [ae_all_clocks_pos] with ω hω
  exact fun _ hv => birth_pos hω hv

theorem reaches_mono_time {d : ℕ} {s t : ℝ} (hst : s ≤ t) :
    reaches d s ⊆ reaches d t := by
  rintro ω ⟨v, hv, ht⟩
  exact ⟨v, hv, ht.trans hst⟩

@[simp] theorem reaches_zero (t : ℝ) :
    reaches 0 t = if 0 ≤ t then Set.univ else ∅ := by
  ext ω
  simp [reaches]

end FreezingGrowth.PWIT
