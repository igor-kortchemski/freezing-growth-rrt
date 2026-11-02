module

public import FreezingGrowth.PWIT.Erlang
public import Mathlib.Data.List.TakeDrop

/-!
# The actual joint law of the increments along a fixed path

The rows of interarrival clocks at distinct ancestors are independent. Thus
the edge increments, unlike cumulative birth times, have a product Gamma law.
This is the law that must be averaged over a rank class before using cyclic
symmetry; a fixed path's unequal Gamma shapes are not exchangeable.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def subtreeSample (ω : Sample) (v : Vertex) : Sample :=
  fun c => ω (v ++ c.1, c.2)

@[simp] theorem subtreeSample_nil (ω : Sample) : subtreeSample ω [] = ω := by
  funext c
  simp [subtreeSample]

theorem birth_append (ω : Sample) (v w : Vertex) :
    birth ω (v ++ w) = birth ω v + birth (subtreeSample ω v) w := by
  induction v generalizing ω with
  | nil => simp
  | cons i v ih =>
    rw [List.cons_append, birth_cons, birth_cons, ih]
    have he : subtreeSample (childSample ω i) v = subtreeSample ω (i :: v) := rfl
    rw [he]
    exact (add_assoc _ _ _).symm

/-- The increment from depth `i` to depth `i + 1`, with zero-based child labels. -/
def pathIncrement (v : Vertex) (ω : Sample) (i : Fin v.length) : ℝ :=
  childDelay ω (v.take i) (v.get i)

@[fun_prop] theorem measurable_pathIncrement (v : Vertex) : Measurable (pathIncrement v) :=
  Measurable.of_eval fun _ => measurable_childDelay _ _

theorem birth_take_succ (ω : Sample) (v : Vertex) (i : Fin v.length) :
    birth ω (v.take ((i : ℕ) + 1)) = birth ω (v.take i) + pathIncrement v ω i := by
  rw [← List.take_concat_get' v i i.isLt, birth_append, birth_cons, birth_nil, add_zero]
  simp [pathIncrement, childDelay, subtreeSample]

/-- Prefix birth time is the sum of its actual edge increments. -/
theorem birth_take_eq_sum (ω : Sample) (v : Vertex) (j : ℕ) (hj : j ≤ v.length) :
    birth ω (v.take j) = ∑ i : Fin j, pathIncrement v ω (i.castLE hj) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : j ≤ v.length := le_trans (Nat.le_succ j) hj
    rw [birth_take_succ ω v ⟨j, hj⟩, Fin.sum_univ_castSucc]
    rw [ih hj']
    rfl

theorem birth_eq_sum_pathIncrement (ω : Sample) (v : Vertex) :
    birth ω v = ∑ i, pathIncrement v ω i := by
  simpa using birth_take_eq_sum ω v v.length le_rfl

noncomputable def rowLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => clockLaw

instance : IsProbabilityMeasure rowLaw := by
  unfold rowLaw
  infer_instance

theorem map_rootRow : law.map (fun (ω : Sample) j => ω ([], j)) = rowLaw :=
  Measure.map_infinitePi_infinitePi_of_inj (by intro i j h; simpa using h)

theorem map_row_sum (n : ℕ) :
    rowLaw.map (fun x => ∑ j ∈ Finset.range (n + 1), x j) =
      gammaMeasure ((n : ℝ) + 1) 1 := by
  rw [← map_rootRow, Measure.map_map (by fun_prop) (by fun_prop)]
  exact map_clockSum_succ n

private theorem pathRowIndex_injective (v : Vertex) :
    Function.Injective (fun p : Fin v.length × ℕ => (v.take p.1, p.2)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hv : v.take i = v.take j := congrArg Prod.fst h
  have hi : i = j := by
    apply Fin.ext
    have hl := congrArg List.length hv
    simpa only [List.length_take, min_eq_left i.isLt.le, min_eq_left j.isLt.le] using hl
  have hab : a = b := congrArg Prod.snd h
  subst j
  subst b
  rfl

theorem map_pathRows (v : Vertex) :
    law.map (fun (ω : Sample) (i : Fin v.length) j => ω (v.take i, j)) =
      Measure.infinitePi (fun _ : Fin v.length => rowLaw) := by
  have hm := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Coordinate => clockLaw) (pathRowIndex_injective v)
  have hc := Measure.infinitePi_map_curry (fun (_ : Fin v.length) (_ : ℕ) => clockLaw)
  rw [← hm, Measure.map_map (by fun_prop) (by fun_prop)] at hc
  exact hc

theorem map_pathRows_of_length (v : Vertex) (d : ℕ) (hv : v.length = d) :
    law.map (fun (ω : Sample) (i : Fin d) j => ω (v.take i, j)) =
      Measure.infinitePi (fun _ : Fin d => rowLaw) := by
  subst d
  exact map_pathRows v

/-- The full product law, not just the marginal of the endpoint. -/
theorem map_pathIncrement (v : Vertex) :
    law.map (pathIncrement v) =
      Measure.pi (fun i : Fin v.length => gammaMeasure ((v.get i : ℝ) + 1) 1) := by
  let sums : (Fin v.length → ℕ → ℝ) → Fin v.length → ℝ :=
    fun rows i => ∑ j ∈ Finset.range (v.get i + 1), rows i j
  have hs : Measurable sums := by
    unfold sums
    fun_prop
  have he : pathIncrement v =
      sums ∘ (fun (ω : Sample) (i : Fin v.length) j => ω (v.take i, j)) := rfl
  rw [he, ← Measure.map_map hs (by fun_prop), map_pathRows]
  dsimp only [sums]
  rw [Measure.infinitePi_map_pi (μ := fun _ : Fin v.length => rowLaw)
    (f := fun i (x : ℕ → ℝ) => ∑ j ∈ Finset.range (v.get i + 1), x j)
    (by intro i; fun_prop)]
  rw [Measure.infinitePi_eq_pi]
  simp only [map_row_sum]

end FreezingGrowth.PWIT
