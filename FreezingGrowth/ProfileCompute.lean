module

public import FreezingGrowth.ProfileCode

/-!
# Integer-weighted finite profile enumeration

Every row is counted, including duplicate rows. Sorting and coalescing merely
combine equal profile codes and preserve all additive weighted observables.
No rational normalization is performed here; the probability-law bridge must
account for the common number of active choices at each step.
-/

@[expose] public section

namespace FreezingGrowth.ProfileCompute

abbrev WeightedCounts := List (ProfileCode × ℕ)

def weightedSum {A : Type*} [AddCommMonoid A] (f : ProfileCode → A)
    (D : WeightedCounts) : A := (D.map (fun row => row.2 • f row.1)).sum

@[simp]
theorem weightedSum_nil {A : Type*} [AddCommMonoid A] (f : ProfileCode → A) :
    weightedSum f [] = 0 := rfl

@[simp]
theorem weightedSum_cons {A : Type*} [AddCommMonoid A] (f : ProfileCode → A)
    (p : ProfileCode) (w : ℕ) (D : WeightedCounts) :
    weightedSum f ((p, w) :: D) = w • f p + weightedSum f D := rfl

@[simp]
theorem weightedSum_append {A : Type*} [AddCommMonoid A] (f : ProfileCode → A)
    (D E : WeightedCounts) : weightedSum f (D ++ E) = weightedSum f D + weightedSum f E := by
  simp [weightedSum]

theorem weightedSum_perm {A : Type*} [AddCommMonoid A] (f : ProfileCode → A)
    {D E : WeightedCounts} (h : D.Perm E) : weightedSum f D = weightedSum f E :=
  (h.map (fun row : ProfileCode × ℕ => row.2 • f row.1)).sum_eq

/-- Combine the current run of identical codes, retaining every integer weight. -/
def coalesceAux (p : ProfileCode) (w : ℕ) : WeightedCounts → WeightedCounts
  | [] => [(p, w)]
  | (q, v) :: D =>
      if p == q then coalesceAux p (w + v) D else (p, w) :: coalesceAux q v D

def coalesce : WeightedCounts → WeightedCounts
  | [] => []
  | (p, w) :: D => coalesceAux p w D

theorem weightedSum_coalesceAux {A : Type*} [AddCommMonoid A]
    (f : ProfileCode → A) (p : ProfileCode) (w : ℕ) (D : WeightedCounts) :
    weightedSum f (coalesceAux p w D) = w • f p + weightedSum f D := by
  induction D generalizing p w with
  | nil => simp [coalesceAux]
  | cons row D ih =>
    obtain ⟨q, v⟩ := row
    by_cases h : p = q
    · subst q
      simp [coalesceAux, ih, add_nsmul, add_assoc]
    · simp [coalesceAux, h, ih]

theorem weightedSum_coalesce {A : Type*} [AddCommMonoid A]
    (f : ProfileCode → A) (D : WeightedCounts) : weightedSum f (coalesce D) = weightedSum f D := by
  cases D with
  | nil => rfl
  | cons row D =>
    obtain ⟨p, w⟩ := row
    exact weightedSum_coalesceAux f p w D

theorem property_coalesceAux (P : ProfileCode → Prop) (p : ProfileCode) (w : ℕ)
    (D : WeightedCounts) (hp : P p) (hD : ∀ row ∈ D, P row.1) :
    ∀ row ∈ coalesceAux p w D, P row.1 := by
  induction D generalizing p w with
  | nil => simpa [coalesceAux] using hp
  | cons row D ih =>
    obtain ⟨q, v⟩ := row
    have hq : P q := hD (q, v) (by simp)
    have htail : ∀ row ∈ D, P row.1 := fun row hr => hD row (by simp [hr])
    by_cases he : p = q
    · subst q
      simpa [coalesceAux] using ih p (w + v) hp htail
    · simp only [coalesceAux, beq_iff_eq, he, ↓reduceIte, List.mem_cons]
      intro row hr
      rcases hr with rfl | hr
      · exact hp
      · exact ih q v hq htail row hr

theorem property_coalesce (P : ProfileCode → Prop) (D : WeightedCounts)
    (hD : ∀ row ∈ D, P row.1) : ∀ row ∈ coalesce D, P row.1 := by
  cases D with
  | nil => simp [coalesce]
  | cons row D =>
    obtain ⟨p, w⟩ := row
    exact property_coalesceAux P p w D (hD (p, w) (by simp))
      (fun row hr => hD row (by simp [hr]))

def rowLE (a b : ProfileCode × ℕ) : Bool := (compare a.1 b.1).isLE

/-- Structurally recursive merge. Fuel exhaustion still preserves every row. -/
def mergeFuel : ℕ → WeightedCounts → WeightedCounts → WeightedCounts
  | 0, D, E => D ++ E
  | _ + 1, [], E => E
  | _ + 1, D, [] => D
  | n + 1, a :: D, b :: E =>
      if rowLE a b then a :: mergeFuel n D (b :: E)
      else b :: mergeFuel n (a :: D) E

theorem mergeFuel_perm (n : ℕ) (D E : WeightedCounts) :
    (mergeFuel n D E).Perm (D ++ E) := by
  induction n generalizing D E with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases D with
    | nil => simp [mergeFuel]
    | cons a D =>
      cases E with
      | nil => simp [mergeFuel]
      | cons b E =>
        simp only [mergeFuel]
        split
        · exact (ih D (b :: E)).cons a
        · exact ((ih (a :: D) E).cons b).trans List.perm_middle.symm

/-- Exposed merge sort avoids hidden imported implementation bodies during kernel reduction. -/
def sortFuel : ℕ → WeightedCounts → WeightedCounts
  | 0, D => D
  | n + 1, D =>
      if D.length ≤ 1 then D else
        mergeFuel D.length (sortFuel n (D.take (D.length / 2)))
          (sortFuel n (D.drop (D.length / 2)))

theorem sortFuel_perm (n : ℕ) (D : WeightedCounts) : (sortFuel n D).Perm D := by
  induction n generalizing D with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    simp only [sortFuel]
    split
    · exact List.Perm.refl _
    · refine ((mergeFuel_perm _ _ _).trans ((ih _).append (ih _))).trans ?_
      rw [List.take_append_drop]

def sort (D : WeightedCounts) : WeightedCounts := sortFuel D.length D

theorem sort_perm (D : WeightedCounts) : (sort D).Perm D := sortFuel_perm _ _

/-- Sort by profile code and combine equal consecutive codes. -/
def aggregate (D : WeightedCounts) : WeightedCounts := coalesce (sort D)

/-- The central aggregation certificate: every additive observable is unchanged. -/
theorem weightedSum_aggregate {A : Type*} [AddCommMonoid A]
    (f : ProfileCode → A) (D : WeightedCounts) :
    weightedSum f (aggregate D) = weightedSum f D := by
  rw [aggregate, weightedSum_coalesce]
  exact weightedSum_perm f (sort_perm D)

/-- Aggregation never introduces a new profile code. -/
theorem property_aggregate (P : ProfileCode → Prop) (D : WeightedCounts)
    (hD : ∀ row ∈ D, P row.1) : ∀ row ∈ aggregate D, P row.1 := by
  apply property_coalesce
  intro row hr
  exact hD row ((sort_perm D).mem_iff.mp hr)

/-- Expand every occurrence branch, preserving the previous history weight. -/
def rawStep (sign : Bool) (D : WeightedCounts) : WeightedCounts :=
  D.flatMap (fun row => (row.1.branches sign).map (fun p => (p, row.2)))

theorem weightedSum_map_weight {A : Type*} [AddCommMonoid A]
    (f : ProfileCode → A) (w : ℕ) (ps : List ProfileCode) :
    weightedSum f (ps.map (fun p => (p, w))) = w • (ps.map f).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih]

/-- Raw expansion sums over occurrence choices, rather than distinct depth values. -/
theorem weightedSum_rawStep {A : Type*} [AddCommMonoid A]
    (f : ProfileCode → A) (sign : Bool) (D : WeightedCounts) :
    weightedSum f (rawStep sign D) =
      weightedSum (fun p => ((p.branches sign).map f).sum) D := by
  induction D with
  | nil => simp [rawStep]
  | cons row D ih =>
    obtain ⟨p, w⟩ := row
    change weightedSum f (((p.branches sign).map (fun q => (q, w))) ++ rawStep sign D) = _
    rw [weightedSum_append, weightedSum_map_weight, ih, weightedSum_cons]

def next (sign : Bool) (D : WeightedCounts) : WeightedCounts := aggregate (rawStep sign D)

theorem weightedSum_next {A : Type*} [AddCommMonoid A]
    (f : ProfileCode → A) (sign : Bool) (D : WeightedCounts) :
    weightedSum f (next sign D) =
      weightedSum (fun p => ((p.branches sign).map f).sum) D := by
  rw [next, weightedSum_aggregate, weightedSum_rawStep]

/-- Integer history counts after following the given signs. -/
def run (signs : List Bool) : WeightedCounts := signs.foldl (fun D sign => next sign D)
  [(ProfileCode.initial, 1)]

@[simp]
theorem run_nil : run [] = [(ProfileCode.initial, 1)] := rfl

theorem run_append_singleton (signs : List Bool) (sign : Bool) :
    run (signs ++ [sign]) = next sign (run signs) := by
  simp [run, List.foldl_append]

def totalWeight (D : WeightedCounts) : ℕ := (D.map Prod.snd).sum

def heightWeight (D : WeightedCounts) : ℕ := (D.map (fun row => row.2 * row.1.maximum)).sum

/-- Compute the two statistics together, avoiding duplicate traversal during checking. -/
def statistics (D : WeightedCounts) : ℕ × ℕ :=
  D.foldl (fun acc row => (acc.1 + row.2, acc.2 + row.2 * row.1.maximum)) (0, 0)

theorem statistics_eq (D : WeightedCounts) : statistics D = (totalWeight D, heightWeight D) := by
  have haux : ∀ (E : WeightedCounts) (a b : ℕ),
      E.foldl (fun acc row => (acc.1 + row.2, acc.2 + row.2 * row.1.maximum)) (a, b) =
        (a + totalWeight E, b + heightWeight E) := by
    intro E
    induction E with
    | nil => intro a b; simp [totalWeight, heightWeight]
    | cons row E ih =>
      intro a b
      obtain ⟨p, w⟩ := row
      simp [List.foldl_cons, ih, totalWeight, heightWeight, add_assoc]
  simpa [statistics] using haux D 0 0

theorem totalWeight_eq_weightedSum (D : WeightedCounts) :
    totalWeight D = weightedSum (fun _ => (1 : ℕ)) D := by
  simp [totalWeight, weightedSum]

theorem heightWeight_eq_weightedSum (D : WeightedCounts) :
    heightWeight D = weightedSum ProfileCode.maximum D := by
  simp [heightWeight, weightedSum]

end FreezingGrowth.ProfileCompute
