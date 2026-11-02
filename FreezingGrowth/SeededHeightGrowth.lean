module

public import FreezingGrowth.HeightProfile
public import FreezingGrowth.ProfileEnumeration

/-!
# Height profiles growing from active seeds

The old maximum is retained even when its vertices are frozen. Offsets act on
every active occurrence, so equal depths retain their sampling multiplicity.
-/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory
open scoped Classical ENNReal

private theorem add_max_nat (a b c : ℕ) : a + max b c = max (a + b) (a + c) := by
  omega

def shift (a M : ℕ) (p : HeightProfile) : HeightProfile :=
  ⟨p.activeDepths.map (a + ·), max M (a + p.maximum)⟩

def join (a b M : ℕ) (p q : HeightProfile) : HeightProfile :=
  ⟨p.activeDepths.map (a + ·) + q.activeDepths.map (b + ·),
    max M (max (a + p.maximum) (b + q.maximum))⟩

theorem shift_attach (a M : ℕ) (p : HeightProfile) (d : ℕ) :
    shift a M (attach p d) = attach (shift a M p) (a + d) := by
  ext
  · simp [shift, attach, Nat.add_assoc]
  · simp only [shift, attach, add_max_nat, Nat.add_assoc]
    ac_rfl

theorem join_attach_left (a b M : ℕ) (p q : HeightProfile) (d : ℕ) :
    join a b M (attach p d) q = attach (join a b M p q) (a + d) := by
  ext
  · simp [join, attach, Nat.add_assoc]
  · simp only [join, attach, add_max_nat, Nat.add_assoc]
    ac_rfl

theorem join_attach_right (a b M : ℕ) (p q : HeightProfile) (d : ℕ) :
    join a b M p (attach q d) = attach (join a b M p q) (b + d) := by
  ext
  · simp [join, attach, Nat.add_assoc, Multiset.add_cons]
  · simp only [join, attach, add_max_nat, Nat.add_assoc]
    ac_rfl

theorem map_multiset_diracs (s : Multiset ℕ) (f : ℕ → ℕ) :
    ((s.map Measure.dirac).sum).map f = ((s.map f).map Measure.dirac).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons d s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons,
      Measure.map_add _ _ (measurable_of_countable f),
      Measure.map_dirac' (measurable_of_countable f), ih]

theorem map_ofMultiset (s : Multiset ℕ) (f : ℕ → ℕ) :
    (Measure.ofMultiset s).map f = Measure.ofMultiset (s.map f) := by
  rw [ProfileCompute.ofMultiset_eq_inverse_smul,
    ProfileCompute.ofMultiset_eq_inverse_smul,
    Measure.map_smul _ (measurable_of_countable f).aemeasurable,
    map_multiset_diracs, Multiset.card_map]

theorem ratio_mul_inverse (a d : ℕ) (ha : 0 < a) :
    ((a : ℝ≥0∞) / d) * (a : ℝ≥0∞)⁻¹ = (d : ℝ≥0∞)⁻¹ := by
  rw [div_eq_mul_inv]
  calc
    _ = (d : ℝ≥0∞)⁻¹ * ((a : ℝ≥0∞) * (a : ℝ≥0∞)⁻¹) := by ac_rfl
    _ = _ := by
      rw [ENNReal.mul_inv_cancel (by exact_mod_cast ha.ne') (ENNReal.natCast_ne_top _),
        mul_one]

theorem ofMultiset_add (s t : Multiset ℕ) (hs : 0 < s.card) (ht : 0 < t.card) :
    Measure.ofMultiset (s + t) =
      ((s.card : ℝ≥0∞) / (s.card + t.card : ℕ)) • Measure.ofMultiset s +
      ((t.card : ℝ≥0∞) / (s.card + t.card : ℕ)) • Measure.ofMultiset t := by
  simp_rw [ProfileCompute.ofMultiset_eq_inverse_smul]
  rw [Multiset.card_add, Multiset.map_add, Multiset.sum_add,
    smul_add, smul_smul, smul_smul, ratio_mul_inverse _ _ hs,
    ratio_mul_inverse _ _ ht]

theorem shift_transition (a M : ℕ) (p : HeightProfile) (hp : p.activeDepths ≠ 0) :
    (transitionLaw p true).map (shift a M) = transitionLaw (shift a M p) true := by
  have he : (shift a M p).activeDepths ≠ 0 := by
    simpa [shift] using hp
  rw [transitionLaw, ite_eq_right hp, transitionLaw, ite_eq_right he,
    Measure.map_map measurable_from_top measurable_from_top,
    show (shift a M p).activeDepths = p.activeDepths.map (a + ·) from rfl,
    ← map_ofMultiset, Measure.map_map measurable_from_top (measurable_of_countable _)]
  congr 1
  funext d
  exact shift_attach a M p d

theorem join_transition (a b M : ℕ) (p q : HeightProfile)
    (hp : 0 < p.activeDepths.card) (hq : 0 < q.activeDepths.card) :
    transitionLaw (join a b M p q) true =
      ((p.activeDepths.card : ℝ≥0∞) / (p.activeDepths.card + q.activeDepths.card : ℕ)) •
        (transitionLaw p true).map (fun p' => join a b M p' q) +
      ((q.activeDepths.card : ℝ≥0∞) / (p.activeDepths.card + q.activeDepths.card : ℕ)) •
        (transitionLaw q true).map (fun q' => join a b M p q') := by
  have hp0 : p.activeDepths ≠ 0 := by intro h; simp [h] at hp
  have hq0 : q.activeDepths ≠ 0 := by intro h; simp [h] at hq
  have hj0 : (join a b M p q).activeDepths ≠ 0 := by
    intro h
    have := congrArg Multiset.card h
    have hc : p.activeDepths.card + q.activeDepths.card = 0 := by
      simpa only [join, Multiset.card_add, Multiset.card_map, Multiset.card_zero] using this
    omega
  rw [transitionLaw, ite_eq_right hj0]
  change (Measure.ofMultiset (p.activeDepths.map (a + ·) +
    q.activeDepths.map (b + ·))).map (step (join a b M p q) true) = _
  rw [ofMultiset_add _ _ (by simpa using hp) (by simpa using hq),
    Measure.map_add _ _ measurable_from_top,
    Measure.map_smul _ measurable_from_top.aemeasurable,
    Measure.map_smul _ measurable_from_top.aemeasurable]
  simp only [Multiset.card_map]
  congr 1
  · rw [transitionLaw, ite_eq_right hp0,
      Measure.map_map measurable_from_top measurable_from_top, ← map_ofMultiset,
      Measure.map_map measurable_from_top (measurable_of_countable _)]
    congr 2
    funext d
    exact (join_attach_left a b M p q d).symm
  · rw [transitionLaw, ite_eq_right hq0,
      Measure.map_map measurable_from_top measurable_from_top, ← map_ofMultiset,
      Measure.map_map measurable_from_top (measurable_of_countable _)]
    congr 2
    funext d
    exact (join_attach_right a b M p q d).symm

noncomputable def grow (p : HeightProfile) : ℕ → Measure HeightProfile
  | 0 => Measure.dirac p
  | n + 1 => (grow p n).bind (fun q => transitionLaw q true)

end FreezingGrowth.HeightProfile
