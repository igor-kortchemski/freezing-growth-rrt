module

public import FreezingGrowth.PWIT.Basic

/-!
# The first-root-birth decomposition

Removing the first root clock separates all remaining coordinates into the
root remainder and the descendants of the first child. Their laws are
independent copies of the original clock law. No chronological infinite-tree
enumeration or independence of cumulative sibling delays is assumed.
-/

@[expose] public section

namespace FreezingGrowth.PWIT

open MeasureTheory ProbabilityTheory
open scoped BigOperators

def firstClock (ω : Sample) : ℝ := ω ([], 0)

def leftIndex : Coordinate → Coordinate
  | ([], j) => ([], j + 1)
  | (i :: v, j) => ((i + 1) :: v, j)

def rightIndex (c : Coordinate) : Coordinate := (0 :: c.1, c.2)

def leftSample (ω : Sample) : Sample := fun c => ω (leftIndex c)
def rightSample (ω : Sample) : Sample := fun c => ω (rightIndex c)

@[fun_prop] theorem measurable_firstClock : Measurable firstClock :=
  measurable_pi_apply ([], 0)

@[fun_prop] theorem measurable_leftSample : Measurable leftSample :=
  Measurable.of_eval fun c => measurable_pi_apply (leftIndex c)

@[fun_prop] theorem measurable_rightSample : Measurable rightSample :=
  Measurable.of_eval fun c => measurable_pi_apply (rightIndex c)

theorem leftIndex_injective : Function.Injective leftIndex := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  cases v with
  | nil =>
    cases w with
    | nil => simpa [leftIndex] using h
    | cons j w => simp [leftIndex] at h
  | cons i v =>
    cases w with
    | nil => simp [leftIndex] at h
    | cons j w => simpa [leftIndex] using h

theorem rightIndex_injective : Function.Injective rightIndex := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  simpa [rightIndex] using h

theorem leftIndex_ne_rightIndex (c d : Coordinate) : leftIndex c ≠ rightIndex d := by
  rcases c with ⟨v, i⟩
  cases v <;> simp [leftIndex, rightIndex]

theorem leftIndex_ne_first (c : Coordinate) : leftIndex c ≠ ([], 0) := by
  rcases c with ⟨v, i⟩
  cases v <;> simp [leftIndex]

theorem rightIndex_ne_first (c : Coordinate) : rightIndex c ≠ ([], 0) := by
  simp [rightIndex]

theorem map_firstClock : law.map firstClock = clockLaw := map_coordinate ([], 0)

theorem map_leftSample : law.map leftSample = law :=
  Measure.map_infinitePi_infinitePi_of_inj leftIndex_injective

theorem map_rightSample : law.map rightSample = law :=
  Measure.map_infinitePi_infinitePi_of_inj rightIndex_injective

/-- Functions of disjoint families of clock coordinates are independent. -/
theorem indepFun_reindex {α β : Type*} (f : α → Coordinate) (g : β → Coordinate)
    (hfg : ∀ a b, f a ≠ g b) :
    IndepFun (fun (ω : Sample) a => ω (f a)) (fun ω b => ω (g b)) law := by
  have hd : Disjoint (Set.range f) (Set.range g) := by
    rw [Set.disjoint_left]
    rintro c ⟨a, rfl⟩ ⟨b, hb⟩
    exact hfg a b hb.symm
  have hi := iIndepFun.indepFun_set (Set.range f) (Set.range g) hd independent_clocks
    (fun c => measurable_pi_apply c)
  exact hi.comp
    (Measurable.of_eval fun a => measurable_pi_apply ⟨f a, ⟨a, rfl⟩⟩)
    (Measurable.of_eval fun b => measurable_pi_apply ⟨g b, ⟨b, rfl⟩⟩)

theorem indep_left_right : IndepFun leftSample rightSample law :=
  indepFun_reindex leftIndex rightIndex leftIndex_ne_rightIndex

theorem indep_firstClock_pair :
    IndepFun firstClock (fun ω => (leftSample ω, rightSample ω)) law := by
  let rest : Coordinate ⊕ Coordinate → Coordinate := Sum.elim leftIndex rightIndex
  have hi := indepFun_reindex (fun _ : Unit => ([], 0)) rest (by
    intro _ c
    cases c with
    | inl c => exact (leftIndex_ne_first c).symm
    | inr c => exact (rightIndex_ne_first c).symm)
  exact hi.comp (measurable_pi_apply ())
    ((Measurable.of_eval fun c => measurable_pi_apply (Sum.inl c)).prodMk
      (Measurable.of_eval fun c => measurable_pi_apply (Sum.inr c)))

/-- Actual joint distribution of the first wait and the two complete remaining
clock samples, with the product nesting used by the renewal integral. -/
theorem firstBirth_joint_law :
    law.map (fun ω => (firstClock ω, (leftSample ω, rightSample ω))) =
      clockLaw.prod (law.prod law) := by
  rw [indep_firstClock_pair.map_prod_eq_prod_map_map
    measurable_firstClock.aemeasurable
    (measurable_leftSample.prodMk measurable_rightSample).aemeasurable,
    map_firstClock,
    indep_left_right.map_prod_eq_prod_map_map
      measurable_leftSample.aemeasurable measurable_rightSample.aemeasurable,
    map_leftSample, map_rightSample]

theorem childDelay_left (ω : Sample) (i : ℕ) :
    childDelay ω [] (i + 1) = firstClock ω + childDelay (leftSample ω) [] i := by
  unfold childDelay firstClock leftSample
  simpa [leftIndex, add_comm] using
    (Finset.sum_range_succ' (fun j => ω ([], j)) (i + 1))

@[simp] theorem childSample_left (ω : Sample) (i : ℕ) :
    childSample (leftSample ω) i = childSample ω (i + 1) := by
  rfl

theorem birth_firstChild (ω : Sample) (v : Vertex) :
    birth ω (0 :: v) = firstClock ω + birth (rightSample ω) v := by
  change childDelay ω [] 0 + birth (rightSample ω) v = _
  simp [childDelay, firstClock]

theorem birth_laterChild (ω : Sample) (i : ℕ) (v : Vertex) :
    birth ω ((i + 1) :: v) = firstClock ω + birth (leftSample ω) (i :: v) := by
  rw [birth_cons, childDelay_left, birth_cons, childSample_left]
  exact add_assoc _ _ _

/-- Exact path-event decomposition. Positivity is not needed for this identity;
it is needed later to exclude births at negative residual times. -/
theorem reaches_succ_firstBirth (ω : Sample) (d : ℕ) (t : ℝ) :
    ω ∈ reaches (d + 1) t ↔
      leftSample ω ∈ reaches (d + 1) (t - firstClock ω) ∨
      rightSample ω ∈ reaches d (t - firstClock ω) := by
  constructor
  · rintro ⟨v, hv, ht⟩
    cases v with
    | nil => simp at hv
    | cons i v =>
      cases i with
      | zero =>
        right
        refine ⟨v, by simpa using hv, ?_⟩
        rw [birth_firstChild] at ht
        linarith
      | succ i =>
        left
        refine ⟨i :: v, by simpa using hv, ?_⟩
        rw [birth_laterChild] at ht
        linarith
  · rintro (⟨v, hv, ht⟩ | ⟨v, hv, ht⟩)
    · cases v with
      | nil => simp at hv
      | cons i v =>
        refine ⟨(i + 1) :: v, by simpa using hv, ?_⟩
        rw [birth_laterChild]
        linarith
    · refine ⟨0 :: v, by simp [hv], ?_⟩
      rw [birth_firstChild]
      linarith

end FreezingGrowth.PWIT
