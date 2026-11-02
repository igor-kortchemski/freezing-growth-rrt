module

public import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Finite Markov histories and projection by a genuine one-step law identity.
No infinite-trajectory or standard-Borel hypothesis is needed. -/

@[expose] public section
namespace FreezingGrowth.FiniteMarkov

open MeasureTheory

structure History (α : Type*) where
  current : α
  past : List α

instance {α : Type*} : MeasurableSpace (History α) := ⊤
instance {α : Type*} : DiscreteMeasurableSpace (History α) := ⟨fun _ => trivial⟩

def History.start {α : Type*} (a : α) : History α := ⟨a, []⟩
def History.push {α : Type*} (a : α) (h : History α) : History α := ⟨a, h.current :: h.past⟩
def History.map {α β : Type*} (f : α → β) (h : History α) : History β :=
  ⟨f h.current, h.past.map f⟩

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]

noncomputable def runLaw (μ : Measure α) (K : ℕ → α → Measure α) : ℕ → Measure α
  | 0 => μ
  | n + 1 => (runLaw μ K n).bind (K n)

noncomputable def historyLaw (μ : Measure α) (K : ℕ → α → Measure α) : ℕ → Measure (History α)
  | 0 => μ.map History.start
  | n + 1 => (historyLaw μ K n).bind (fun h => (K n h.current).map (fun a => h.push a))

/-- The current coordinate of the full finite history has the actual iterated law. -/
theorem historyLaw_current (μ : Measure α) (K : ℕ → α → Measure α) (n : ℕ) :
    (historyLaw μ K n).map History.current = runLaw μ K n := by
  induction n with
  | zero =>
    rw [historyLaw, Measure.map_map measurable_from_top Measurable.of_discrete]
    exact Measure.map_id
  | succ n ih =>
    rw [historyLaw, runLaw, Measure.map_bind measurable_from_top.aemeasurable
      measurable_from_top.aemeasurable]
    calc
      _ = (historyLaw μ K n).bind (fun h => K n h.current) := by
        congr 1
        funext h
        rw [Measure.map_map measurable_from_top Measurable.of_discrete]
        exact Measure.map_id
      _ = ((historyLaw μ K n).map History.current).bind (K n) :=
        (Measure.bind_map measurable_from_top.aemeasurable Measurable.of_discrete.aemeasurable).symm
      _ = _ := by rw [ih]

/-- A one-step projected-kernel identity on the actually reached states
identifies the entire finite projected history, rather than only its marginals. -/
theorem map_historyLaw (μ : Measure α) (K : ℕ → α → Measure α)
    (L : ℕ → β → Measure β) (f : α → β) (n : ℕ)
    (hK : ∀ t < n, ∀ᵐ a ∂runLaw μ K t, (K t a).map f = L t (f a)) :
    (historyLaw μ K n).map (History.map f) = historyLaw (μ.map f) L n := by
  induction n with
  | zero =>
    rw [historyLaw, historyLaw, Measure.map_map measurable_from_top Measurable.of_discrete,
      Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    rfl
  | succ n ih =>
    have ih' := ih (fun t ht => hK t (by omega))
    have hh : ∀ᵐ h ∂historyLaw μ K n, (K n h.current).map f = L n (f h.current) := by
      have he := hK n (by omega)
      rw [← historyLaw_current μ K n] at he
      exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp he
    rw [historyLaw, historyLaw, Measure.map_bind measurable_from_top.aemeasurable
      measurable_from_top.aemeasurable]
    calc
      _ = (historyLaw μ K n).bind (fun h =>
          (L n (f h.current)).map (fun b => (History.map f h).push b)) := by
        apply Measure.bind_congr_right
        filter_upwards [hh] with h hh
        rw [Measure.map_map measurable_from_top Measurable.of_discrete]
        have he : (K n h.current).map ((History.map f) ∘ (fun a => h.push a)) =
            ((K n h.current).map f).map (fun b => (History.map f h).push b) := by
          rw [Measure.map_map Measurable.of_discrete Measurable.of_discrete]
          rfl
        rw [he, hh]
      _ = ((historyLaw μ K n).map (History.map f)).bind
          (fun h => (L n h.current).map (fun b => h.push b)) :=
        (Measure.bind_map (m := historyLaw μ K n) (f := History.map f)
          (g := fun h : History β => (L n h.current).map (fun b => h.push b))
          measurable_from_top.aemeasurable measurable_from_top.aemeasurable).symm
      _ = _ := by rw [ih']

end FreezingGrowth.FiniteMarkov
