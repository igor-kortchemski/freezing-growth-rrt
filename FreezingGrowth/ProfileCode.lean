module

public import FreezingGrowth.HeightProfile
public import Mathlib.Data.List.Sort

/-!
# Computable codes for height profiles

The list stores active-depth occurrences, including repetitions. Sorting is
an efficiency invariant only: decoding always takes the associated multiset.
The maximum retains frozen vertices. Branches enumerate one outcome for each
active occurrence, so their multiplicities implement uniform vertex choice.
-/

@[expose] public section

namespace FreezingGrowth

@[ext]
structure ProfileCode where
  activeDepths : List ℕ
  maximum : ℕ
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Ord, Repr

namespace ProfileCode

def decode (p : ProfileCode) : HeightProfile := ⟨p.activeDepths, p.maximum⟩

def initial : ProfileCode := ⟨[0], 0⟩

def Sorted (p : ProfileCode) : Prop := p.activeDepths.Pairwise (· ≤ ·)

/-- Insertion into a nondecreasing list. This duplicates `List.orderedInsert (· ≤ ·)`
as an exposed definition, so that kernel computation in `module` files can unfold it. -/
def insertSorted (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

theorem insertSorted_eq (x : ℕ) (l : List ℕ) :
    insertSorted x l = l.orderedInsert (· ≤ ·) x := by
  induction l with
  | nil => simp only [insertSorted, List.orderedInsert_nil]
  | cons y ys ih => simp only [insertSorted, List.orderedInsert_cons, ih]

def attach (p : ProfileCode) (d : ℕ) : ProfileCode :=
  ⟨insertSorted (d + 1) p.activeDepths, max p.maximum (d + 1)⟩

theorem attach_activeDepths (p : ProfileCode) (d : ℕ) :
    (attach p d).activeDepths = p.activeDepths.orderedInsert (· ≤ ·) (d + 1) :=
  insertSorted_eq _ _

theorem attach_activeDepths_perm (p : ProfileCode) (d : ℕ) :
    (attach p d).activeDepths.Perm ((d + 1) :: p.activeDepths) := by
  rw [attach_activeDepths]
  exact List.perm_orderedInsert (· ≤ ·) (d + 1) p.activeDepths

def freeze (p : ProfileCode) (d : ℕ) : ProfileCode :=
  ⟨p.activeDepths.erase d, p.maximum⟩

def step (p : ProfileCode) (sign : Bool) (d : ℕ) : ProfileCode :=
  if sign then attach p d else freeze p d

/-- Each list occurrence is a separate equally likely choice. Extinction absorbs. -/
def branches (p : ProfileCode) (sign : Bool) : List ProfileCode :=
  if p.activeDepths.isEmpty then [p] else p.activeDepths.map (step p sign)

@[simp]
theorem decode_initial : decode initial = HeightProfile.initial := rfl

@[simp]
theorem decode_card (p : ProfileCode) : p.decode.activeDepths.card = p.activeDepths.length := rfl

@[simp]
theorem decode_maximum (p : ProfileCode) : p.decode.maximum = p.maximum := rfl

@[simp]
theorem decode_attach (p : ProfileCode) (d : ℕ) :
    (attach p d).decode = HeightProfile.attach p.decode d := by
  apply HeightProfile.ext
  · exact Multiset.coe_eq_coe.mpr (attach_activeDepths_perm p d)
  · rfl

@[simp]
theorem decode_freeze (p : ProfileCode) (d : ℕ) :
    (freeze p d).decode = HeightProfile.freeze p.decode d := rfl

@[simp]
theorem decode_step (p : ProfileCode) (sign : Bool) (d : ℕ) :
    (step p sign d).decode = HeightProfile.step p.decode sign d := by
  cases sign <;> simp [step, HeightProfile.step]

/-- Decoding the occurrence list gives precisely the mathematical profile branches. -/
theorem map_decode_branches (p : ProfileCode) (sign : Bool) :
    (branches p sign).map decode =
      if p.activeDepths.isEmpty then [p.decode]
      else p.activeDepths.map (HeightProfile.step p.decode sign) := by
  unfold branches
  split <;> simp [List.map_map, Function.comp_def]

theorem branches_eq_of_nonempty (p : ProfileCode) (sign : Bool)
    (hp : p.activeDepths ≠ []) : branches p sign = p.activeDepths.map (step p sign) := by
  simp [branches, hp]

theorem branches_eq_of_empty (p : ProfileCode) (sign : Bool)
    (hp : p.activeDepths = []) : branches p sign = [p] := by
  simp [branches, hp]

theorem branches_length (p : ProfileCode) (sign : Bool) :
    (branches p sign).length = max p.activeDepths.length 1 := by
  cases h : p.activeDepths with
  | nil => simp [branches, h]
  | cons d ds => simp [branches, h]

@[simp]
theorem attach_length (p : ProfileCode) (d : ℕ) :
    (attach p d).activeDepths.length = p.activeDepths.length + 1 := by
  rw [attach_activeDepths]
  exact List.orderedInsert_length _ _ _

theorem freeze_length (p : ProfileCode) {d : ℕ} (hd : d ∈ p.activeDepths) :
    (freeze p d).activeDepths.length = p.activeDepths.length - 1 := by
  exact List.length_erase_of_mem hd

theorem branches_active_length_of_pos {p q : ProfileCode} (sign : Bool)
    (hp : 0 < p.activeDepths.length) (hq : q ∈ p.branches sign) :
    q.activeDepths.length = if sign then p.activeDepths.length + 1
      else p.activeDepths.length - 1 := by
  have hne : p.activeDepths ≠ [] := by intro h; simp [h] at hp
  rw [branches_eq_of_nonempty p sign hne] at hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  cases sign
  · exact freeze_length p hd
  · exact attach_length p d

theorem branches_active_length_of_zero {p q : ProfileCode} (sign : Bool)
    (hp : p.activeDepths.length = 0) (hq : q ∈ p.branches sign) :
    q.activeDepths.length = 0 := by
  have he : p.activeDepths = [] := List.length_eq_zero_iff.mp hp
  rw [branches_eq_of_empty p sign he] at hq
  have hqp : q = p := List.mem_singleton.mp hq
  subst q
  exact hp

theorem sorted_initial : initial.Sorted := by simp [Sorted, initial]

theorem Sorted.attach {p : ProfileCode} (hp : p.Sorted) (d : ℕ) : (p.attach d).Sorted := by
  unfold Sorted
  rw [attach_activeDepths]
  exact hp.orderedInsert _ _

theorem Sorted.freeze {p : ProfileCode} (hp : p.Sorted) (d : ℕ) : (p.freeze d).Sorted :=
  hp.erase d

theorem Sorted.step {p : ProfileCode} (hp : p.Sorted) (sign : Bool) (d : ℕ) :
    (p.step sign d).Sorted := by
  cases sign
  · exact hp.freeze d
  · exact hp.attach d

end ProfileCode

end FreezingGrowth
