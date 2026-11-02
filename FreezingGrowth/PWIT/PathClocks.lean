module

public import FreezingGrowth.PWIT.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.List.OfFn

/-!
# The finite independent clocks used by a path

A path of child ranks `v.map (· + 1)` uses their sum many distinct exponential
coordinates. This connects the actual path birth time to a finite product law;
it does not assume a Gamma convolution theorem.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Sum of the positive mathematical child ranks along a path. -/
def rankSum (v : Vertex) : ℕ := (v.map (· + 1)).sum

@[simp] theorem rankSum_nil : rankSum [] = 0 := rfl

@[simp] theorem rankSum_cons (i : ℕ) (v : Vertex) :
    rankSum (i :: v) = i + 1 + rankSum v := by simp [rankSum]

theorem rankSum_eq_length_add_sum (v : Vertex) : rankSum v = v.length + v.sum := by
  induction v with
  | nil => rfl
  | cons i v ih => simp [rankSum_cons, ih]; omega

/-- Distinct interarrival coordinates whose sum is a path's birth time. -/
def pathCoordinates : Vertex → List Coordinate
  | [] => []
  | i :: v =>
    (List.range (i + 1)).map (fun j => ([], j)) ++
      (pathCoordinates v).map (fun c => (i :: c.1, c.2))

@[simp] theorem pathCoordinates_length (v : Vertex) :
    (pathCoordinates v).length = rankSum v := by
  induction v with
  | nil => rfl
  | cons i v ih => simp [pathCoordinates, ih]

theorem pathCoordinates_nodup (v : Vertex) : (pathCoordinates v).Nodup := by
  induction v with
  | nil => simp [pathCoordinates]
  | cons i v ih =>
    rw [pathCoordinates, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · exact (List.nodup_range).map (by intro a b h; simpa using h)
    · exact ih.map (by rintro ⟨a, b⟩ ⟨c, d⟩ h; simpa using h)
    · intro c hc d hd he
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hd
      simp at he

theorem birth_eq_sum_pathCoordinates (ω : Sample) (v : Vertex) :
    birth ω v = ((pathCoordinates v).map ω).sum := by
  induction v generalizing ω with
  | nil => rfl
  | cons i v ih =>
    rw [birth_cons, pathCoordinates, List.map_append, List.sum_append, List.map_map,
      List.map_map, ih]
    rfl

theorem map_pathClocks (v : Vertex) :
    law.map (fun ω (j : Fin (pathCoordinates v).length) => ω ((pathCoordinates v).get j)) =
      Measure.pi (fun _ : Fin (pathCoordinates v).length => clockLaw) := by
  have hi := independent_clocks.precomp (pathCoordinates_nodup v).injective_get
  rw [hi.map_fun_eq_pi_map (fun j => (measurable_pi_apply _).aemeasurable)]
  simp only [map_coordinate]

theorem map_birth_finite_sum (v : Vertex) :
    law.map (fun ω => birth ω v) =
      (Measure.pi (fun _ : Fin (pathCoordinates v).length => clockLaw)).map
        (fun x => ∑ j, x j) := by
  rw [← map_pathClocks v, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  rw [birth_eq_sum_pathCoordinates]
  change _ = ∑ j : Fin (pathCoordinates v).length, ω ((pathCoordinates v).get j)
  rw [← List.sum_ofFn, List.ofFn_comp', List.ofFn_get]

/-- The finite class of depth `d` paths with total positive rank `d + k`. -/
def rankClass (d k : ℕ) : Finset Vertex :=
  (Finset.Nat.antidiagonalTuple d k).image List.ofFn

theorem mem_rankClass {d k : ℕ} {v : Vertex} :
    v ∈ rankClass d k ↔ v.length = d ∧ v.sum = k := by
  classical
  constructor
  · rintro hv
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨List.length_ofFn, by simpa [List.sum_ofFn] using
      Finset.Nat.mem_antidiagonalTuple.mp hf⟩
  · rintro ⟨hd, hk⟩
    subst d
    apply Finset.mem_image.mpr
    refine ⟨v.get, ?_, List.ofFn_get v⟩
    apply Finset.Nat.mem_antidiagonalTuple.mpr
    simpa [← List.sum_ofFn, List.ofFn_get] using hk

theorem mem_rankClass_iff_rankSum {d k : ℕ} {v : Vertex} :
    v ∈ rankClass d k ↔ v.length = d ∧ rankSum v = d + k := by
  rw [mem_rankClass, rankSum_eq_length_add_sum]
  omega

theorem rankClass_disjoint {d k l : ℕ} (hkl : k ≠ l) :
    Disjoint (rankClass d k) (rankClass d l) := by
  rw [Finset.disjoint_left]
  intro v hv hw
  exact hkl ((mem_rankClass.mp hv).2.symm.trans (mem_rankClass.mp hw).2)

end FreezingGrowth.PWIT
