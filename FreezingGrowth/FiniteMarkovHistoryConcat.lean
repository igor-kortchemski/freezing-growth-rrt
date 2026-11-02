module

public import FreezingGrowth.FiniteMarkovHistory

/-! Exact concatenation of finite histories, retaining every earlier state.
Past lists are stored newest first. -/

@[expose] public section
namespace FreezingGrowth.FiniteMarkov

open MeasureTheory

def History.appendPast {α : Type*} (past : List α) (h : History α) : History α :=
  ⟨h.current, h.past ++ past⟩

def History.merge {α : Type*} (h g : History α) : History α := g.appendPast h.past

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

omit [DiscreteMeasurableSpace α] in
theorem historyLaw_congr (μ : Measure α) (K L : ℕ → α → Measure α) (n : ℕ)
    (hKL : ∀ t < n, ∀ a, K t a = L t a) : historyLaw μ K n = historyLaw μ L n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [historyLaw, historyLaw, ih (fun t ht => hKL t (by omega))]
    congr 1
    funext h
    rw [hKL n (by omega)]

/-- Split a whole history after `a` steps and retain its earlier past when
executing the next `b` genuine transitions. -/
theorem historyLaw_add (μ : Measure α) (K : ℕ → α → Measure α) (a b : ℕ) :
    historyLaw μ K (a + b) = (historyLaw μ K a).bind (fun h =>
      (historyLaw (Measure.dirac h.current) (fun t => K (a + t)) b).map (History.merge h)) := by
  induction b with
  | zero =>
    simp only [Nat.add_zero, historyLaw, Measure.map_dirac' Measurable.of_discrete]
    have he : (fun h : History α => Measure.dirac (History.merge h (History.start h.current))) =
        Measure.dirac := by
      funext h
      cases h
      rfl
    rw [he, Measure.bind_dirac]
  | succ b ih =>
    rw [Nat.add_succ, historyLaw, ih]
    simp only [historyLaw]
    rw [Measure.bind_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    congr 1
    funext h
    rw [Measure.bind_map (m := historyLaw (Measure.dirac h.current) (fun t => K (a + t)) b)
      (f := History.merge h)
      (g := fun g : History α => (K (a + b) g.current).map (fun x => g.push x))
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    congr 1
    funext g
    rw [Measure.map_map measurable_from_top Measurable.of_discrete]
    rfl

/-- Expose the first transition while retaining its starting state in the
whole subsequent history. -/
theorem historyLaw_dirac_succ (a : α) (K : ℕ → α → Measure α) (n : ℕ) :
    historyLaw (Measure.dirac a) K (n + 1) =
      (historyLaw (K 0 a) (fun t => K (t + 1)) n).map (History.appendPast [a]) := by
  induction n with
  | zero =>
    rw [historyLaw, historyLaw, historyLaw, Measure.map_dirac' Measurable.of_discrete,
      Measure.dirac_bind measurable_from_top,
      Measure.map_map measurable_from_top Measurable.of_discrete]
    rfl
  | succ n ih =>
    rw [historyLaw, ih, historyLaw]
    rw [Measure.bind_map
      (m := historyLaw (K 0 a) (fun t => K (t + 1)) n)
      (f := History.appendPast [a])
      (g := fun h : History α => (K (n + 1) h.current).map (fun x => h.push x))
      measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    congr 1
    funext h
    rw [Measure.map_map measurable_from_top Measurable.of_discrete]
    rfl

end FreezingGrowth.FiniteMarkov
