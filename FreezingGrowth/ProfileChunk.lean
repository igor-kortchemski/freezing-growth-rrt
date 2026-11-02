module

public import FreezingGrowth.ProfileTailStatistics
public import FreezingGrowth.ProfileEnumeration

/-!
# Splitting a profile computation into independently checkable pieces

Kernel evaluation of one long enumeration keeps every intermediate term alive. The
enumeration is linear in its initial table, so a run can be cut after a prefix:
every observable of the full run is the weighted sum over the prefix table of the
same observable of the continuation started from a single profile. Cutting the
prefix table into consecutive chunks then yields statements whose kernel
evaluation is small. These are exact identities for arbitrary additive
observables; they assume no numerical value.
-/

@[expose] public section

namespace FreezingGrowth.ProfileCompute

/-- Continue the integer enumeration from an arbitrary weighted table. -/
def runFrom (signs : List Bool) (D : WeightedCounts) : WeightedCounts :=
  signs.foldl (fun D sign => next sign D) D

@[simp] theorem runFrom_nil (D : WeightedCounts) : runFrom [] D = D := rfl

@[simp] theorem runFrom_cons (sign : Bool) (signs : List Bool) (D : WeightedCounts) :
    runFrom (sign :: signs) D = runFrom signs (next sign D) := rfl

theorem run_append (A B : List Bool) : run (A ++ B) = runFrom B (run A) := by
  simp [run, runFrom, List.foldl_append]

/-- Linearity of the enumeration: continuing from a table is the weighted sum of
continuing from each profile separately. -/
theorem weightedSum_runFrom {A : Type*} [AddCommMonoid A] (f : ProfileCode → A)
    (B : List Bool) : ∀ D : WeightedCounts, weightedSum f (runFrom B D) =
      weightedSum (fun p => weightedSum f (runFrom B [(p, 1)])) D := by
  induction B with
  | nil =>
    intro D
    apply weightedSum_congr
    intro row _
    simp [weightedSum]
  | cons sign B ih =>
    intro D
    rw [runFrom_cons, ih (next sign D), weightedSum_next]
    apply weightedSum_congr
    intro row _
    rw [runFrom_cons, ih (next sign [(row.1, 1)]), weightedSum_next]
    simp [weightedSum]

/-- Cut a run after `A`, peel the last two attachments in closed form, and keep the
`B` steps in between as a per-profile continuation. -/
theorem statistics_run_two_attach_split (A B : List Bool) :
    statistics (run ((A ++ B) ++ [true, true])) =
      weightedSum (fun p => weightedSum twoAttachStatistics (runFrom B [(p, 1)])) (run A) := by
  rw [show (A ++ B) ++ [true, true] = ((A ++ B) ++ [true]) ++ [true] by simp,
    run_append_singleton, run_append_singleton,
    statistics_two_attach _ (run_maximumBounded _), run_append, weightedSum_runFrom]

/-- The `i`-th block of `k` consecutive rows. -/
def chunk (D : WeightedCounts) (k i : ℕ) : WeightedCounts := (D.drop (k * i)).take k

theorem weightedSum_chunks {A : Type*} [AddCommMonoid A] (f : ProfileCode → A)
    (D : WeightedCounts) (k : ℕ) : ∀ m : ℕ, weightedSum f D =
      (∑ i ∈ Finset.range m, weightedSum f (chunk D k i)) + weightedSum f (D.drop (k * m)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    have hsplit : weightedSum f (D.drop (k * m)) =
        weightedSum f (chunk D k m) + weightedSum f (D.drop (k * (m + 1))) := by
      have hd : (D.drop (k * m)).drop k = D.drop (k * (m + 1)) := by
        rw [List.drop_drop, Nat.mul_succ]
      rw [← weightedSum_append, chunk, ← hd, List.take_append_drop]
    exact hsplit

end FreezingGrowth.ProfileCompute
