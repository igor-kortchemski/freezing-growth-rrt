module

public import FreezingGrowth.FiniteMarkovHistorySupport
public import FreezingGrowth.ReverseDelayedLongerLaw
public import FreezingGrowth.ReverseFirstUseGraft

/-! The first actual distinguished-vertex use on complete finite histories.
Chronological indices increase, while the source indices decrease. -/

@[expose] public section
namespace FreezingGrowth.ReverseOrdered

open MeasureTheory

def FirstUseStep (i : ℕ) (z z' : InitializationSample) : Prop :=
  z.used = false → z'.used = true → FirstUseGraft (consumeDelayed z) i z'

def FirstUseAt (F : Forest) (i : ℕ) (h : FiniteMarkov.History InitializationSample)
    (r : Fin h.states.length) : Prop :=
  h.states[r.val].used = true ∧
    (∀ s : Fin h.states.length, s < r → h.states[s.val].used = false) ∧
    (r.val = 0 → FirstUseGraft F i h.states[r.val]) ∧
    (∀ hr : 0 < r.val,
      FirstUseGraft (consumeDelayed (h.states[r.val - 1]'(by omega))) i h.states[r.val])

/-- Reversing chronological time gives exactly the source's maximum used index. -/
theorem FirstUseAt.reverse_max {F : Forest} {i : ℕ}
    {h : FiniteMarkov.History InitializationSample} {r : Fin h.states.length}
    (hr : FirstUseAt F i h r) (s : Fin h.states.length) (hs : h.states[s.val].used = true) :
    h.states.length - 1 - s.val ≤ h.states.length - 1 - r.val := by
  have hsr : r.val ≤ s.val := by
    by_contra hn
    have hfalse := hr.2.1 s (show s < r by omega)
    rw [hs] at hfalse
    contradiction
  omega

theorem delayedHistoryLaw_ae_firstUseStep (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (t : ℕ) (ht : t ≤ F.forest.roots.card - 1) :
    ∀ᵐ h ∂delayedHistoryLaw F i t, h.states.IsChain (FirstUseStep i) := by
  apply FiniteMarkov.historyLaw_ae_chain
  intro s hs
  rw [finiteRunLaw_delayed]
  filter_upwards [delayedLawAfter_ae_valid F hi s (by omega)] with z hz
  by_cases hu : z.used = false
  · filter_upwards [delayedTransition_ae_firstUseGraft hz (by omega) hu] with z' hz'
    exact fun _ => hz'
  · exact Filter.Eventually.of_forall (fun _ hfalse _ => False.elim (hu hfalse))

theorem delayedHistoryLaw_terminal_used (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card) :
    ∀ᵐ h ∂delayedHistoryLaw F i (F.forest.roots.card - 1), h.current.used = true := by
  have hh := delayedLawAfter_terminal_used F hi hF
  rw [← finiteRunLaw_delayed, ← FiniteMarkov.historyLaw_current] at hh
  exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hh

theorem delayedHistoryLaw_firstUse (F : Forest) {i : ℕ}
    (hi : Sum.inr i ∉ F.forest.vertices) (hF : 1 ≤ F.forest.roots.card) :
    ∀ᵐ h ∂delayedHistoryLaw F i (F.forest.roots.card - 1),
      h.states.length = F.forest.roots.card ∧ ∃ r : Fin h.states.length, FirstUseAt F i h r := by
  have hinit := FiniteMarkov.historyLaw_ae_initial (initializationLaw F i)
    (fun _ => delayedTransition i) (fun z => z.used = true → FirstUseGraft F i z)
    (initializationLaw_ae_firstUseGraft F hi) (F.forest.roots.card - 1)
  filter_upwards [delayedHistoryLaw_ae_firstUseStep F hi _ le_rfl,
    delayedHistoryLaw_terminal_used F hi hF, hinit,
    FiniteMarkov.historyLaw_ae_length (initializationLaw F i)
      (fun _ => delayedTransition i) (F.forest.roots.card - 1)] with h hchain hterminal hstart hlen
  have hlen' : h.states.length = F.forest.roots.card := by omega
  have hex : ∃ a ∈ h.states, a.used = true :=
    ⟨h.current, h.current_mem_states, hterminal⟩
  obtain ⟨r, hr, hearlier⟩ := FiniteMarkov.first_true_index h.states InitializationSample.used hex
  refine ⟨hlen', r, hr, hearlier, ?_, ?_⟩
  · intro hr0
    have hhead : h.states.head? = some h.states[r.val] := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < h.states.length)]
      congr 1
      simp only [hr0]
    exact hstart _ hhead hr
  · intro hrpos
    let s : Fin h.states.length := ⟨r.val - 1, by omega⟩
    have hpair := hchain.getElem (r.val - 1) (by omega)
    have hind : r.val - 1 + 1 = r.val := by omega
    have he : FirstUseStep i h.states[s.val] h.states[r.val] := by simpa only [hind, s] using hpair
    exact he (hearlier s (by change r.val - 1 < r.val; omega)) hr

structure FirstUseHistorySample where
  incoming : Forest
  history : FiniteMarkov.History InitializationSample

instance : MeasurableSpace FirstUseHistorySample := ⊤
instance : DiscreteMeasurableSpace FirstUseHistorySample := ⟨fun _ => trivial⟩

noncomputable def sourceFirstUseHistoryLaw (k : ℕ) (tail : Word) :
    Measure FirstUseHistorySample :=
  (initializationTailLaw k tail).bind (fun F =>
    (delayedHistoryLaw F k (k - 1)).map (FirstUseHistorySample.mk F))

theorem sourceFirstUseHistoryLaw_current (k : ℕ) (tail : Word) :
    (sourceFirstUseHistoryLaw k tail).map (fun z => z.history.current) =
      sourceDelayedLaw k tail (k - 1) := by
  rw [sourceFirstUseHistoryLaw, Measure.map_bind measurable_from_top.aemeasurable
    measurable_from_top.aemeasurable, sourceDelayedLaw]
  congr 1
  funext F
  rw [Measure.map_map measurable_from_top measurable_from_top]
  change (FiniteMarkov.historyLaw (initializationLaw F k)
    (fun _ => delayedTransition k) (k - 1)).map FiniteMarkov.History.current = _
  rw [FiniteMarkov.historyLaw_current, finiteRunLaw_delayed]

/-- C7 on the actual common-tail/initialization/delayed-history sampling.
The stored pair at the first index is the original sampled pair of the graft. -/
theorem sourceFirstUseHistoryLaw_firstUse (k : ℕ) (hk : 1 ≤ k) (tail : Word)
    (ha : Word.admissible (List.replicate k true ++ [false] ++ tail)) :
    ∀ᵐ z ∂sourceFirstUseHistoryLaw k tail,
      z.history.states.length = k ∧ ∃ r : Fin z.history.states.length, FirstUseAt z.incoming k z.history r := by
  rw [ae_iff, sourceFirstUseHistoryLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
  apply (lintegral_eq_zero_iff measurable_from_top).mpr
  filter_upwards [initializationTailLaw_parameters k tail ha] with F hF
  apply ae_iff.mp
  apply (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mpr
  have hh := delayedHistoryLaw_firstUse F hF.1 (by simpa only [hF.2] using hk)
  simpa only [hF.2] using hh

end FreezingGrowth.ReverseOrdered
