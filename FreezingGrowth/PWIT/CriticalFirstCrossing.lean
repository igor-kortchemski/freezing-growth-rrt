module

public import FreezingGrowth.PWIT.CriticalBarrierGeometry
public import FreezingGrowth.PWIT.LogBarrierIntensity
public import FreezingGrowth.PWIT.Leading

/-! A finite first crossing on a witnessing actual PWIT path. The reduction
is used only on nonnegative clock samples and does not assume a minimum over
the infinite generation is attained. -/

@[expose] public section
namespace FreezingGrowth.PWIT

open MeasureTheory Set

noncomputable def crossingAllowance (d j : ℕ) (a c : ℝ) : ℝ :=
  a + c * Real.log ((min j (d - j) : ℕ) + 1 : ℝ)

theorem log_min_window_local {d j i : ℕ} (hjd : j ≤ d) (hij : i ≤ j) :
    Real.log ((min i (d - i) : ℕ) + 1 : ℝ) ≤
      Real.log ((min j (d - j) : ℕ) + 1 : ℝ) +
        Real.log ((min i (j - i) : ℕ) + 1 : ℝ) := by
  by_cases hj : 2 * j ≤ d
  · rw [Nat.min_eq_left (show i ≤ d - i by omega),
      Nat.min_eq_left (show j ≤ d - j by omega)]
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (i : ℝ) + 1)
      (show (i : ℝ) + 1 ≤ (j : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hij 1)
    have hl : 0 ≤ Real.log ((min i (j - i) : ℕ) + 1 : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ min i (j - i) + 1 by omega))
    linarith
  · rw [Nat.min_eq_right (show d - j ≤ j by omega)]
    exact log_min_window_bound hjd hij

theorem criticalCrossingBarrier_uniform {d j i : ℕ} (hd : 0 < d) (hj : 0 < j)
    (hjd : j ≤ d) (hij : i ≤ j) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    -crossingAllowance d j a c - c * Real.log ((min i (j - i) : ℕ) + 1 : ℝ) ≤
      criticalCrossingBarrier d i a c - (i : ℝ) / j * criticalCrossingBarrier d j a c := by
  rw [criticalCrossingBarrier_chord hd hj]
  have hlog := mul_le_mul_of_nonneg_left (log_min_window_local hjd hij) hc
  have hLj : 0 ≤ Real.log ((min j (d - j) : ℕ) + 1 : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ min j (d - j) + 1 by omega))
  have hiR : 0 ≤ (i : ℝ) / j := div_nonneg (Nat.cast_nonneg i) (Nat.cast_nonneg j)
  have hp := mul_nonneg hiR (mul_nonneg hc hLj)
  have hapos := mul_nonneg hiR ha
  unfold crossingAllowance
  nlinarith

theorem first_critical_crossing_index {d : ℕ} (hd : 0 < d) {a c : ℝ}
    (ha : criticalCrossingOffset ≤ a) (hc : 0 ≤ c) (S : ℕ → ℝ)
    (hSn : ∀ j ≤ d, 0 ≤ S j)
    (hend : S d ≤ criticalCrossingBarrier d d a c) :
    ∃ j, 30 ≤ j ∧ j ≤ d ∧ 0 ≤ criticalCrossingBarrier d j a c ∧
      S j ≤ criticalCrossingBarrier d j a c ∧
        ∀ i < j, criticalCrossingBarrier d i a c ≤ S i := by
  have hex : ∃ j, S j ≤ criticalCrossingBarrier d j a c := ⟨d, hend⟩
  let j := Nat.find hex
  have hj : S j ≤ criticalCrossingBarrier d j a c := Nat.find_spec hex
  have hjd : j ≤ d := Nat.find_min' hex hend
  have hnonneg : 0 ≤ criticalCrossingBarrier d j a c := (hSn j hjd).trans hj
  have hlarge : 30 ≤ j := by
    by_contra h
    have hh := criticalCrossingBarrier_small hd (show j < 30 by omega) ha hc
    linarith
  refine ⟨j, hlarge, hjd, hnonneg, hj, ?_⟩
  intro i hi
  exact (lt_of_not_ge (Nat.find_min hex hi)).le

theorem logVectorBarrier_of_crossing_prefix {d j : ℕ} [NeZero j]
    (hd : 0 < d) (hjd : j ≤ d) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (x : Fin j → ℝ) (hend : totalWait x ≤ criticalCrossingBarrier d j a c)
    (hprev : ∀ i : Fin j, criticalCrossingBarrier d i.val a c ≤ cyclicPrefix x i.val) :
    logVectorBarrier (crossingAllowance d j a c) c x := by
  unfold logVectorBarrier softBridge
  intro i
  rw [centeredBridge_zero, sub_zero]
  change -logBarrierAllowance (crossingAllowance d j a c) c i ≤
    cyclicPrefix x i.val - (i : ℝ) / j * totalWait x
  have hb := criticalCrossingBarrier_uniform hd (NeZero.pos j) hjd i.isLt.le ha hc
  have hm := mul_le_mul_of_nonneg_left hend
    (div_nonneg (Nat.cast_nonneg (α := ℝ) i.val) (Nat.cast_nonneg (α := ℝ) j))
  have hp := hprev i
  unfold logBarrierAllowance
  linarith

theorem take_ofFn_nat {d : ℕ} (r : Fin d → ℕ) (j : ℕ) (hj : j ≤ d) :
    (List.ofFn r).take j = List.ofFn (fun i : Fin j => r (i.castLE hj)) := by
  apply List.ext_getElem
  · simp [List.length_take, Nat.min_eq_left hj]
  · intro i hi hi'
    simp only [List.getElem_take, List.getElem_ofFn]
    rfl

noncomputable def crossingGenerationEvent (d j : ℕ) (a c : ℝ) : Set Sample :=
  if hj : 0 < j then
    {ω | 0 ≤ criticalCrossingBarrier d j a c ∧ ∃ r : Fin j → ℕ,
      tupleIncrement r ω ∈ @logBarrierVectorEvent j ⟨hj.ne'⟩
        (crossingAllowance d j a c) c (Icc 0 (criticalCrossingBarrier d j a c))}
  else ∅

theorem measurableSet_crossingGenerationEvent (d j : ℕ) (a c : ℝ) :
    MeasurableSet (crossingGenerationEvent d j a c) := by
  by_cases hj : 0 < j
  · let : NeZero j := ⟨hj.ne'⟩
    by_cases hb : 0 ≤ criticalCrossingBarrier d j a c
    · have hE := measurableSet_logBarrierVectorEvent j (crossingAllowance d j a c) c
        (measurableSet_Icc : MeasurableSet (Icc 0 (criticalCrossingBarrier d j a c)))
      have he : crossingGenerationEvent d j a c =
          ⋃ r : Fin j → ℕ, tupleIncrement r ⁻¹'
            logBarrierVectorEvent j (crossingAllowance d j a c) c (Icc 0 (criticalCrossingBarrier d j a c)) := by
        ext ω
        simp only [crossingGenerationEvent, dite_eq_left hj, Set.mem_iUnion,
          Set.mem_preimage, Set.mem_ofPred_eq, hb, true_and]
      rw [he]
      exact MeasurableSet.iUnion fun r => hE.preimage (measurable_tupleIncrement r)
    · have he : crossingGenerationEvent d j a c = ∅ := by
        ext ω
        simp only [crossingGenerationEvent, dite_eq_left hj, Set.mem_ofPred_eq,
          hb, false_and, Set.mem_empty_iff_false]
      rw [he]
      exact MeasurableSet.empty
  · simp only [crossingGenerationEvent, dite_eq_right hj]
    exact MeasurableSet.empty

theorem reaches_first_crossing {d : ℕ} (hd : 30 ≤ d) {a c : ℝ}
    (ha : criticalCrossingOffset ≤ a) (hc : 0 ≤ c) {ω : Sample}
    (hω : ∀ z, 0 ≤ ω z) (hr : ω ∈ reaches d (timeCenter d - a)) :
    ∃ j ∈ Finset.Icc 30 d, ω ∈ crossingGenerationEvent d j a c := by
  obtain ⟨v, hvd, hbirth⟩ := hr
  let S : ℕ → ℝ := fun j => birth ω (v.take j)
  have hdpos : 0 < d := by omega
  have hSn : ∀ j ≤ d, 0 ≤ S j := fun j _ => birth_nonneg hω (v.take j)
  have hend : S d ≤ criticalCrossingBarrier d d a c := by
    rw [criticalCrossingBarrier_self hdpos]
    simpa only [S, ← hvd, List.take_length] using hbirth
  obtain ⟨j, hj30, hjd, hb, hj, hprev⟩ := first_critical_crossing_index hdpos ha hc S hSn hend
  have hjpos : 0 < j := by omega
  let : NeZero j := ⟨hjpos.ne'⟩
  have hjv : j ≤ v.length := by omega
  let r : Fin j → ℕ := fun i => v.get (i.castLE hjv)
  have htake : List.ofFn r = v.take j := by
    have hh := take_ofFn_nat v.get j hjv
    rw [List.ofFn_get] at hh
    exact hh.symm
  have htotal : totalWait (tupleIncrement r ω) = S j := by
    change (∑ i, tupleIncrement r ω i) = birth ω (v.take j)
    rw [← birth_ofFn_eq_sum_tupleIncrement, htake]
  have hpref (i : Fin j) : cyclicPrefix (tupleIncrement r ω) i.val = S i.val := by
    rw [cyclicPrefix_tupleIncrement r ω i.val i.isLt.le, htake, List.take_take,
      Nat.min_eq_left i.isLt.le]
  have hbar : logVectorBarrier (crossingAllowance d j a c) c (tupleIncrement r ω) := by
    apply logVectorBarrier_of_crossing_prefix hdpos hjd
      (criticalCrossingOffset_pos.le.trans ha) hc
    · rw [htotal]
      exact hj
    · intro i
      rw [hpref]
      exact hprev i.val i.isLt
  refine ⟨j, Finset.mem_Icc.mpr ⟨hj30, hjd⟩, ?_⟩
  rw [crossingGenerationEvent, dite_eq_left hjpos]
  refine ⟨hb, r, ?_, hbar⟩
  rw [htotal]
  exact ⟨hSn j hjd, hj⟩

end FreezingGrowth.PWIT
