module

public import FreezingGrowth.ProfileCompute

/-!
# Exact terminal statistics without terminal aggregation

Weighted observables can be propagated backwards through the last attachments.
The two-step formula below preserves occurrence multiplicities and the stored
maximum over all vertices. An empty active set remains absorbing.
-/

@[expose] public section

namespace FreezingGrowth.ProfileCompute

theorem statistics_eq_weightedSum (D : WeightedCounts) :
    statistics D = weightedSum (fun p => ((1 : ℕ), p.maximum)) D := by
  rw [statistics_eq]
  induction D with
  | nil => rfl
  | cons row D ih =>
    obtain ⟨p,w⟩ := row
    rw [weightedSum_cons, ← ih]
    simp [totalWeight, heightWeight]

theorem sum_profile_statistics (ps : List ProfileCode) :
    (ps.map (fun p => ((1 : ℕ), p.maximum))).sum =
      (ps.length, (ps.map ProfileCode.maximum).sum) := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih, Nat.add_comm]

theorem statistics_next (sign : Bool) (D : WeightedCounts) :
    statistics (next sign D) = weightedSum (fun p : ProfileCode =>
      ((p.branches sign).length, ((p.branches sign).map ProfileCode.maximum).sum)) D := by
  rw [statistics_eq_weightedSum, weightedSum_next]
  simp only [sum_profile_statistics]

theorem statistics_next_next (first second : Bool) (D : WeightedCounts) :
    statistics (next second (next first D)) = weightedSum (fun p : ProfileCode =>
      ((p.branches first).map (fun q =>
        ((q.branches second).length, ((q.branches second).map ProfileCode.maximum).sum))).sum) D := by
  rw [statistics_next, weightedSum_next]

/-- Every active vertex lies below the maximum over all vertices. -/
def MaximumBounded (p : ProfileCode) : Prop := ∀ d ∈ p.activeDepths, d ≤ p.maximum

theorem maximumBounded_initial : MaximumBounded ProfileCode.initial := by
  simp [MaximumBounded, ProfileCode.initial]

theorem MaximumBounded.attach {p : ProfileCode} (hp : MaximumBounded p) (d : ℕ) :
    MaximumBounded (p.attach d) := by
  intro e he
  have hperm := ProfileCode.attach_activeDepths_perm p d
  have he' : e ∈ (d + 1) :: p.activeDepths := hperm.mem_iff.mp he
  rcases List.mem_cons.mp he' with rfl | he'
  · exact le_max_right _ _
  · exact (hp e he').trans (le_max_left _ _)

theorem MaximumBounded.freeze {p : ProfileCode} (hp : MaximumBounded p) (d : ℕ) :
    MaximumBounded (p.freeze d) := by
  intro e he
  exact hp e (List.mem_of_mem_erase he)

theorem MaximumBounded.step {p : ProfileCode} (hp : MaximumBounded p) (sign : Bool) (d : ℕ) :
    MaximumBounded (p.step sign d) := by
  cases sign
  · exact hp.freeze d
  · exact hp.attach d

theorem MaximumBounded.branches {p q : ProfileCode} (hp : MaximumBounded p)
    (sign : Bool) (hq : q ∈ p.branches sign) : MaximumBounded q := by
  by_cases he : p.activeDepths = []
  · rw [ProfileCode.branches_eq_of_empty p sign he] at hq
    have hqp : q = p := List.mem_singleton.mp hq
    subst q
    exact hp
  · rw [ProfileCode.branches_eq_of_nonempty p sign he] at hq
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hq
    exact hp.step sign d

theorem next_maximumBounded (D : WeightedCounts) (sign : Bool)
    (hD : ∀ row ∈ D, MaximumBounded row.1) :
    ∀ row ∈ next sign D, MaximumBounded row.1 := by
  unfold next
  apply property_aggregate MaximumBounded
  intro row hr
  obtain ⟨old, ho, hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  exact (hD old ho).branches sign hq

theorem run_maximumBounded (signs : List Bool) :
    ∀ row ∈ run signs, MaximumBounded row.1 := by
  induction signs using List.reverseRecOn with
  | nil => simpa using maximumBounded_initial
  | append_singleton signs sign ih =>
    rw [run_append_singleton]
    exact next_maximumBounded _ _ ih

theorem sum_attach_maximum (ds : List ℕ) (M : ℕ) (hds : ∀ d ∈ ds, d ≤ M) :
    (ds.map (fun d => max M (d + 1))).sum = ds.length * M + ds.count M := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := hds d (by simp)
    have htail : ∀ e ∈ ds, e ≤ M := fun e he => hds e (by simp [he])
    rw [List.map_cons, List.sum_cons, ih htail]
    by_cases he : d = M
    · subst d
      simp [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
    · have hd' : d + 1 ≤ M := by omega
      simp [he, max_eq_left hd', Nat.add_mul,
        Nat.add_comm, Nat.add_left_comm]

def oneAttachStatistics (p : ProfileCode) : ℕ × ℕ :=
  if p.activeDepths.isEmpty then (1, p.maximum) else
    (p.activeDepths.length, p.activeDepths.length * p.maximum + p.activeDepths.count p.maximum)

theorem oneAttachStatistics_eq (p : ProfileCode) (hp : MaximumBounded p) :
    ((p.branches true).length, ((p.branches true).map ProfileCode.maximum).sum) =
      oneAttachStatistics p := by
  by_cases he : p.activeDepths = []
  · simp [ProfileCode.branches_eq_of_empty p true he, oneAttachStatistics, he]
  · rw [ProfileCode.branches_eq_of_nonempty p true he]
    simp only [List.length_map, List.map_map]
    change (p.activeDepths.length, (p.activeDepths.map (fun d => max p.maximum (d + 1))).sum) = _
    rw [sum_attach_maximum _ _ hp]
    simp [oneAttachStatistics, he]

theorem oneAttachStatistics_attach (p : ProfileCode) (hp : MaximumBounded p)
    (d : ℕ) (hd : d ≤ p.maximum) :
    oneAttachStatistics (p.attach d) =
      (p.activeDepths.length + 1,
       (p.activeDepths.length + 1) * p.maximum +
         (if d = p.maximum then p.activeDepths.length + 2 else p.activeDepths.count p.maximum) +
         if d + 1 = p.maximum then 1 else 0) := by
  have hne : (p.attach d).activeDepths ≠ [] := by
    intro h
    have hl := congrArg List.length h
    simp at hl
  simp only [oneAttachStatistics, List.isEmpty_eq_false_iff.mpr hne, Bool.false_eq_true,
    ↓reduceIte, ProfileCode.attach_length]
  by_cases he : d = p.maximum
  · subst d
    have hnot : p.maximum + 1 ∉ p.activeDepths := by
      intro h
      have := hp _ h
      omega
    have hc : p.activeDepths.count (p.maximum + 1) = 0 :=
      List.count_eq_zero.mpr hnot
    simp [ProfileCode.attach, ProfileCode.insertSorted_eq, List.orderedInsert_count, hc,
      Nat.add_mul, Nat.mul_add]
    omega
  · have hle : d + 1 ≤ p.maximum := by omega
    simp [ProfileCode.attach, ProfileCode.insertSorted_eq, List.orderedInsert_count,
      max_eq_left hle, he, Nat.add_assoc]

theorem sum_pair_constant (ds : List ℕ) (a : ℕ) (f : ℕ → ℕ) :
    (ds.map (fun d => (a, f d))).sum = (ds.length * a, (ds.map f).sum) := by
  induction ds with
  | nil => apply Prod.ext <;> simp
  | cons d ds ih => simp [ih, Nat.add_mul, Nat.add_comm]

theorem sum_two_attach_cases (ds : List ℕ) (M K L C : ℕ) :
    (ds.map (fun d => K + (if d = M then L else C) + if d + 1 = M then 1 else 0)).sum =
      ds.length * K + ds.count M * L + (ds.length - ds.count M) * C +
        ds.countP (fun d => d + 1 == M) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    rw [List.map_cons, List.sum_cons, ih]
    by_cases he : d = M
    · subst d
      simp [Nat.add_sub_add_right]
      ring
    · have hc : ds.count M ≤ ds.length := List.count_le_length
      have hsub : ds.length + 1 - ds.count M = (ds.length - ds.count M) + 1 := by omega
      simp only [List.length_cons, List.count_cons_of_ne he, List.countP_cons, hsub,
        ite_eq_right he]
      by_cases hb : d + 1 = M <;> simp [hb] <;> ring

/-- Exact statistics of all pairs of subsequent attachment choices. -/
def twoAttachStatistics (p : ProfileCode) : ℕ × ℕ :=
  if p.activeDepths.isEmpty then (1, p.maximum) else
    let a := p.activeDepths.length
    let c := p.activeDepths.count p.maximum
    let b := p.activeDepths.countP (fun d => d + 1 == p.maximum)
    (a * (a + 1), a * (a + 1) * p.maximum + c * (a + 2) + (a - c) * c + b)

theorem twoAttachStatistics_eq (p : ProfileCode) (hp : MaximumBounded p) :
    ((p.branches true).map (fun q =>
      ((q.branches true).length, ((q.branches true).map ProfileCode.maximum).sum))).sum =
      twoAttachStatistics p := by
  by_cases he : p.activeDepths = []
  · simp [ProfileCode.branches_eq_of_empty p true he, twoAttachStatistics, he]
  · rw [ProfileCode.branches_eq_of_nonempty p true he, List.map_map]
    have hmap : p.activeDepths.map (fun d =>
        (((p.step true d).branches true).length,
          (((p.step true d).branches true).map ProfileCode.maximum).sum)) =
        p.activeDepths.map (fun d =>
          (p.activeDepths.length + 1,
            (p.activeDepths.length + 1) * p.maximum +
              (if d = p.maximum then p.activeDepths.length + 2 else p.activeDepths.count p.maximum) +
              if d + 1 = p.maximum then 1 else 0)) := by
      apply List.map_congr_left
      intro d hd
      change (((p.attach d).branches true).length,
        (((p.attach d).branches true).map ProfileCode.maximum).sum) = _
      rw [oneAttachStatistics_eq _ (hp.attach d), oneAttachStatistics_attach p hp d (hp d hd)]
    change (p.activeDepths.map (fun d =>
        (((p.step true d).branches true).length,
          (((p.step true d).branches true).map ProfileCode.maximum).sum))).sum = _
    rw [hmap, sum_pair_constant, sum_two_attach_cases]
    simp [twoAttachStatistics, he, Nat.mul_assoc]

theorem statistics_two_attach (D : WeightedCounts)
    (hD : ∀ row ∈ D, MaximumBounded row.1) :
    statistics (next true (next true D)) = weightedSum twoAttachStatistics D := by
  rw [statistics_next_next]
  unfold weightedSum
  congr 1
  apply List.map_congr_left
  intro row hr
  exact congrArg (fun v : ℕ × ℕ => row.2 • v) (twoAttachStatistics_eq row.1 (hD row hr))

theorem weightedSum_snd (f : ProfileCode → ℕ × ℕ) (D : WeightedCounts) :
    (weightedSum f D).2 = weightedSum (fun p => (f p).2) D := by
  induction D with
  | nil => rfl
  | cons row D ih =>
    obtain ⟨p,w⟩ := row
    simp [weightedSum_cons, ih]

theorem heightWeight_two_attach (D : WeightedCounts)
    (hD : ∀ row ∈ D, MaximumBounded row.1) :
    heightWeight (next true (next true D)) =
      weightedSum (fun p => (twoAttachStatistics p).2) D := by
  simpa only [statistics_eq, weightedSum_snd] using
    congrArg Prod.snd (statistics_two_attach D hD)

end FreezingGrowth.ProfileCompute
