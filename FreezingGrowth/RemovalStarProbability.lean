module

public import FreezingGrowth.RemoveAttachAnalytic

/-! Star probabilities and non-domination for the two removal words. -/

@[expose] public section
namespace FreezingGrowth

open MeasureTheory
open scoped Classical ENNReal

namespace RRTSplit

theorem heightPairLaw_ae_not_both_zero {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ p ∂heightPairLaw n, ¬(p.1 = 0 ∧ p.2 = 0) := by
  rw [heightPairLaw_eq_map, ae_map_iff measurable_from_top.aemeasurable
    (Set.to_countable _).measurableSet]
  filter_upwards [treeLaw_split_describes n] with s hs
  intro hz
  have hlen {r : ℕ} {c : Component} (hc : Component.WellFormed r c)
      (hh : Forward.treeHeight c.tree = 0) : c.labels.length ≤ 1 := by
    by_contra h
    have hv : 1 ∈ c.tree.vertices := by rw [hc.vertices]; simp; omega
    have hd := Forward.height_le_treeHeight hv
    have he := (hc.valid.height_eq_zero_iff hv).mp (by omega)
    omega
  have hr := hlen hs.formed.root hz.1
  have hc := hlen hs.formed.child hz.2
  have hsum := hs.formed.edges_sum
  omega

end RRTSplit

namespace HeightProfile

theorem join_seed_cdf (a b M : ℕ) (hab : max a b ≤ M) (n h : ℕ) :
    grow ⟨{a,b},M⟩ n {p | p.maximum ≤ h} =
      RRTSplit.heightPairLaw n {p | seedHeight a b M p ≤ h} := by
  have he := congrArg (fun μ : Measure ℕ => μ {k | k ≤ h})
    (join_seed_maximum_law a b M hab n)
  simpa only [Measure.map_apply measurable_from_top (show MeasurableSet {k : ℕ | k ≤ h} from by trivial),
    Measure.map_apply (measurable_of_countable _) (show MeasurableSet {k : ℕ | k ≤ h} from by trivial),
    Set.preimage_ofPred_eq] using he

theorem single_seed_cdf (a M : ℕ) (ha : a ≤ M) (n h : ℕ) :
    grow ⟨{a},M⟩ n {p | p.maximum ≤ h} =
      Forward.heightLaw RRT.allAttach n {k | max M (a + k) ≤ h} := by
  rw [single_seed_growth a M ha,
    Measure.map_apply measurable_from_top (by trivial), Forward.heightLaw,
    Measure.map_apply measurable_from_top (by trivial)]
  rfl

theorem heightLaw_cdf_eq_wordLaw (xs : Word) (h : ℕ) :
    xs.heightLaw {k | k ≤ h} = wordLaw xs {p | p.maximum ≤ h} := by
  rw [Word.heightLaw, ← map_law_maximum,
    Measure.map_apply measurable_from_top (by trivial)]
  rfl

end HeightProfile

theorem removalShort_height_le_one {n : ℕ} (hn : 1 ≤ n) :
    (removalShort n).heightLaw {k | k ≤ 1} =
      (2 : ℝ≥0∞)⁻¹ * (n.factorial : ℝ≥0∞)⁻¹ := by
  rw [HeightProfile.heightLaw_cdf_eq_wordLaw, removalShort, HeightProfile.short_word_law,
    Measure.smul_apply, Measure.add_apply, smul_eq_mul,
    HeightProfile.single_seed_cdf 0 1 (by decide),
    HeightProfile.single_seed_cdf 1 1 (by decide)]
  have hz : Forward.heightLaw RRT.allAttach n {k | max 1 (1 + k) ≤ 1} = 0 := by
    rw [Forward.heightLaw, Measure.map_apply measurable_from_top (by trivial)]
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [RRT.treeHeight_pos hn] with s hs
    change ¬max 1 (1 + Forward.treeHeight s) ≤ 1
    omega
  rw [hz]
  have he : {k : ℕ | max 1 (0 + k) ≤ 1} = {k | k ≤ 1} := by ext k; simp
  rw [he, RRT.height_le_one_mass, add_zero]

theorem removalLong_height_le_one {n : ℕ} (hn : 1 ≤ n) :
    (removalLong n).heightLaw {k | k ≤ 1} =
      (3 : ℝ≥0∞)⁻¹ * ((n + 1).factorial : ℝ≥0∞)⁻¹ := by
  rw [HeightProfile.heightLaw_cdf_eq_wordLaw, removalLong, HeightProfile.long_word_law,
    Measure.smul_apply]
  simp only [Measure.add_apply, smul_eq_mul,
    show (2 : ℕ) • HeightProfile.grow ⟨{0,1},1⟩ n =
      HeightProfile.grow ⟨{0,1},1⟩ n + HeightProfile.grow ⟨{0,1},1⟩ n by simp [two_smul]]
  rw [HeightProfile.join_seed_cdf 0 1 1 (by decide),
    HeightProfile.join_seed_cdf 0 1 2 (by decide),
    HeightProfile.join_seed_cdf 0 2 2 (by decide),
    HeightProfile.join_seed_cdf 1 1 1 (by decide),
    HeightProfile.join_seed_cdf 1 2 2 (by decide)]
  have hz : RRTSplit.heightPairLaw n {p | HeightProfile.seedHeight 1 1 1 p ≤ 1} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [RRTSplit.heightPairLaw_ae_not_both_zero hn] with p hp
    simp only [HeightProfile.seedHeight]
    omega
  have he : {p : ℕ × ℕ | HeightProfile.seedHeight 0 1 1 p ≤ 1} =
      {p | max p.1 (p.2 + 1) = 1} := by
    ext p
    change HeightProfile.seedHeight 0 1 1 p ≤ 1 ↔ max p.1 (p.2 + 1) = 1
    simp only [HeightProfile.seedHeight]
    omega
  have hstar : RRTSplit.heightPairLaw n {p | max p.1 (p.2 + 1) = 1} =
      ((n + 1).factorial : ℝ≥0∞)⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp [Nat.factorial_ne_zero])).mp
    simpa [Measure.real] using RRTSplit.heightPairLaw_height_one n
  have hempty (a b : ℕ) : {p : ℕ × ℕ | HeightProfile.seedHeight a b 2 p ≤ 1} = ∅ := by
    ext p
    change HeightProfile.seedHeight a b 2 p ≤ 1 ↔ False
    change max 2 (max (a + p.1) (b + p.2)) ≤ 1 ↔ False
    exact iff_false_intro (fun h => by have := (le_max_left 2 _).trans h; omega)
  rw [hz, he, hstar, hempty, hempty, hempty]
  simp only [measure_empty, add_zero]
  have hcoef : (6 : ℝ≥0∞)⁻¹ * 2 = 3⁻¹ := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    norm_num
  calc
    _ = ((6 : ℝ≥0∞)⁻¹ * 2) * ((n + 1).factorial : ℝ≥0∞)⁻¹ := by
      rw [← two_mul]
      ac_rfl
    _ = _ := by rw [hcoef]

theorem Word.heightLaw_pos_of_attachments (xs : Word) (ha : xs.admissible)
    (hp : 1 ≤ xs.attachments) : ∀ᵐ k ∂xs.heightLaw, 0 < k := by
  rw [Word.heightLaw, Forward.heightLaw,
    ae_map_iff measurable_from_top.aemeasurable (by trivial)]
  filter_upwards [Forward.treeLaw_valid xs.toSigns xs.length,
    Forward.treeLaw_counts xs.toSigns xs.length
      ((Word.admissible_iff_le_extinctionTime xs).mp ha)] with s hs hc
  have hcard : 1 < s.vertices.card := by
    have he := hc.2
    change s.vertices.card = xs.attachments + 1 at he
    omega
  obtain ⟨v, hv, hv0⟩ := Finset.exists_mem_ne hcard 0
  have hh := hs.height_parent v hv hv0
  have hle := Forward.height_le_treeHeight hv
  omega

private theorem removalShort_attachments (n : ℕ) : 1 ≤ (removalShort n).attachments := by
  rw [removalShort, Word.attachments_append, (Word.replicate_true_inFamily n).2]
  rw [show Word.attachments [true, false] = 1 by decide +kernel]
  omega

private theorem removalLong_attachments (n : ℕ) : 1 ≤ (removalLong n).attachments := by
  rw [removalLong, Word.attachments_append, (Word.replicate_true_inFamily n).2]
  rw [show Word.attachments [true, true, false] = 2 by decide +kernel]
  omega

theorem removalShort_height_one {n : ℕ} (hn : 1 ≤ n) :
    (removalShort n).heightLaw.real {1} = 1 / (2 * (n.factorial : ℝ)) := by
  have he : (removalShort n).heightLaw {1} = (removalShort n).heightLaw {k | k ≤ 1} := by
    apply measure_congr
    filter_upwards [Word.heightLaw_pos_of_attachments _ (removalShort_admissible n)
      (removalShort_attachments n)] with k hk
    change (k = 1) = (k ≤ 1)
    apply propext
    omega
  rw [Measure.real, he, removalShort_height_le_one hn]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  ring

theorem removalLong_height_one {n : ℕ} (hn : 1 ≤ n) :
    (removalLong n).heightLaw.real {1} = 1 / (3 * ((n + 1).factorial : ℝ)) := by
  have he : (removalLong n).heightLaw {1} = (removalLong n).heightLaw {k | k ≤ 1} := by
    apply measure_congr
    filter_upwards [Word.heightLaw_pos_of_attachments _ (removalLong_admissible n)
      (removalLong_attachments n)] with k hk
    change (k = 1) = (k ≤ 1)
    apply propext
    omega
  rw [Measure.real, he, removalLong_height_le_one hn]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  ring

theorem removal_not_heightLE {n : ℕ} (hn : 1 ≤ n) :
    ¬Word.HeightLE (removalLong n) (removalShort n) := by
  intro h
  have ht := (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (h 2)
  change (removalLong n).heightLaw.real {k | 2 ≤ k} ≤
    (removalShort n).heightLaw.real {k | 2 ≤ k} at ht
  have hcomp : {k : ℕ | 2 ≤ k} = {k : ℕ | k ≤ 1}ᶜ := by ext k; simp; omega
  rw [hcomp, measureReal_compl (by trivial), measureReal_compl (by trivial),
    probReal_univ, probReal_univ] at ht
  have hl : (removalLong n).heightLaw.real {k | k ≤ 1} =
      1 / (3 * ((n + 1).factorial : ℝ)) := by
    rw [Measure.real, removalLong_height_le_one hn]
    simp
    ring
  have hs : (removalShort n).heightLaw.real {k | k ≤ 1} =
      1 / (2 * (n.factorial : ℝ)) := by
    rw [Measure.real, removalShort_height_le_one hn]
    simp
    ring
  rw [hl, hs] at ht
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hstrict : (1 : ℝ) / (3 * ((n + 1).factorial : ℝ)) < 1 / (2 * (n.factorial : ℝ)) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  linarith

end FreezingGrowth
