module

public import FreezingGrowth.FiniteMarkovHistory
public import Mathlib.Data.List.Chain

/-! Actual finite-history support, retaining relations on every adjacent pair. -/

@[expose] public section
namespace FreezingGrowth.FiniteMarkov

open MeasureTheory

def History.states {α : Type*} (h : History α) : List α := (h.current :: h.past).reverse

theorem History.states_nonempty {α : Type*} (h : History α) : h.states ≠ [] := by
  simp [History.states]

theorem History.current_mem_states {α : Type*} (h : History α) : h.current ∈ h.states := by
  simp [History.states]

theorem History.states_push {α : Type*} (h : History α) (a : α) :
    (h.push a).states = h.states ++ [a] := by
  simp only [History.states, History.push, List.reverse_cons]

theorem first_true_index {α : Type*} (l : List α) (f : α → Bool)
    (hex : ∃ a ∈ l, f a = true) :
    ∃ j : Fin l.length, f l[j.val] = true ∧
      ∀ i : Fin l.length, i < j → f l[i.val] = false := by
  have hnat : ∃ j, ∃ hj : j < l.length, f l[j] = true :=
    List.exists_mem_iff_getElem.mp hex
  let j := Nat.find hnat
  obtain ⟨hj, hjtrue⟩ := Nat.find_spec hnat
  refine ⟨⟨j, hj⟩, hjtrue, ?_⟩
  intro i hi
  have hn := Nat.find_min hnat hi
  cases hc : f l[i.val] with
  | false => rfl
  | true => exact False.elim (hn ⟨i.isLt, hc⟩)

variable {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]

theorem historyLaw_ae_chain (μ : Measure α) (K : ℕ → α → Measure α)
    (R : α → α → Prop) (n : ℕ)
    (hK : ∀ t < n, ∀ᵐ a ∂runLaw μ K t, ∀ᵐ b ∂K t a, R a b) :
    ∀ᵐ h ∂historyLaw μ K n, h.states.IsChain R := by
  have hreverse : ∀ᵐ h ∂historyLaw μ K n,
      (h.current :: h.past).IsChain (fun b a => R a b) := by
    induction n with
    | zero =>
      rw [historyLaw]
      apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
      exact Filter.Eventually.of_forall (fun _ => List.IsChain.singleton _)
    | succ n ih =>
      have ih' := ih (fun t ht => hK t (by omega))
      have hk : ∀ᵐ h ∂historyLaw μ K n, ∀ᵐ b ∂K n h.current, R h.current b := by
        have hh := hK n (by omega)
        rw [← historyLaw_current μ K n] at hh
        exact (ae_map_iff measurable_from_top.aemeasurable MeasurableSet.of_discrete).mp hh
      rw [ae_iff, historyLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
      apply (lintegral_eq_zero_iff measurable_from_top).mpr
      filter_upwards [ih', hk] with h hh hk
      apply ae_iff.mp
      apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
      filter_upwards [hk] with b hb
      exact List.isChain_cons_cons.mpr ⟨hb, hh⟩
  filter_upwards [hreverse] with h hh
  exact List.isChain_reverse.mpr hh

theorem historyLaw_ae_length (μ : Measure α) (K : ℕ → α → Measure α) (n : ℕ) :
    ∀ᵐ h ∂historyLaw μ K n, h.states.length = n + 1 := by
  induction n with
  | zero =>
    rw [historyLaw]
    apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
    exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    rw [ae_iff, historyLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    apply (lintegral_eq_zero_iff measurable_from_top).mpr
    filter_upwards [ih] with h hh
    apply ae_iff.mp
    apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
    exact Filter.Eventually.of_forall (fun a => by simp only [History.states_push, List.length_append,
      List.length_singleton, hh])

theorem historyLaw_ae_initial (μ : Measure α) (K : ℕ → α → Measure α)
    (P : α → Prop) (hP : ∀ᵐ a ∂μ, P a) (n : ℕ) :
    ∀ᵐ h ∂historyLaw μ K n, ∀ a, h.states.head? = some a → P a := by
  induction n with
  | zero =>
    rw [historyLaw]
    apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
    filter_upwards [hP] with a ha
    intro b hb
    have he : a = b := by simpa only [History.start, History.states, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.head?_cons, Option.some.injEq] using hb
    exact he ▸ ha
  | succ n ih =>
    rw [ae_iff, historyLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    apply (lintegral_eq_zero_iff measurable_from_top).mpr
    filter_upwards [ih] with h hh
    apply ae_iff.mp
    apply (ae_map_iff Measurable.of_discrete.aemeasurable MeasurableSet.of_discrete).mpr
    refine Filter.Eventually.of_forall (fun b a ha => hh a ?_)
    rw [History.states_push, List.head?_append_of_ne_nil h.states (History.states_nonempty h)] at ha
    exact ha

end FreezingGrowth.FiniteMarkov
