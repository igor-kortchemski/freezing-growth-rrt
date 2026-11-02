module

public import FreezingGrowth.TwoSeedGraftLaw

/-! Full-state graft geometry: old vertices keep their entire tree data,
and precisely the embedded non-first master edges are added. -/

@[expose] public section
namespace FreezingGrowth.TwoSeedGraft

open MeasureTheory

def graftEdges (T u v : ℕ) (p : ℕ → ℕ) : ℕ → SimpleGraph ℕ
  | 0 => ⊥
  | n + 1 => graftEdges T u v p n ⊔ SimpleGraph.edge (embedding T u v (p (n + 2))) (T + n + 1)

theorem replay_graph (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ) (n : ℕ) :
    (replay s T u v p n).graph = s.graph ⊔ graftEdges T u v p n := by
  induction n with
  | zero => simp only [replay, graftEdges, sup_bot_eq]
  | succ n ih =>
    change (replay s T u v p n).graph ⊔ _ = _
    rw [ih, graftEdges, sup_assoc]

theorem replay_vertices (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ) (n : ℕ) :
    (replay s T u v p n).vertices = s.vertices ∪
      (Finset.range n).image (fun j => T + j + 1) := by
  induction n with
  | zero => simp only [replay, Finset.range_zero, Finset.image_empty, Finset.union_empty]
  | succ n ih =>
    change insert (T + n + 1) (replay s T u v p n).vertices = _
    have hrange : Finset.range (n + 1) = insert n (Finset.range n) := Finset.range_add_one
    rw [ih, hrange, Finset.image_insert, Finset.union_insert]

theorem replay_parent_old (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ)
    (n a : ℕ) (ha : a ≤ T) : (replay s T u v p n).parent a = s.parent a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Function.update (replay s T u v p n).parent (T + n + 1) _ a = _
    rw [Function.update_of_ne (by omega), ih]

theorem replay_height_old (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ)
    (n a : ℕ) (ha : a ≤ T) : (replay s T u v p n).height a = s.height a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Function.update (replay s T u v p n).height (T + n + 1) _ a = _
    rw [Function.update_of_ne (by omega), ih]

theorem replay_frozenAt_old (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ)
    (n a : ℕ) (ha : a ≤ T) : (replay s T u v p n).frozenAt a = s.frozenAt a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Function.update (replay s T u v p n).frozenAt (T + n + 1) _ a = _
    rw [Function.update_of_ne (by omega), ih]

theorem replay_parent_new (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ)
    (n j : ℕ) (hj : j < n) :
    (replay s T u v p n).parent (T + j + 1) = embedding T u v (p (j + 2)) := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    by_cases hlast : j = n
    · subst j
      change Function.update _ (T + n + 1) _ (T + n + 1) = _
      exact Function.update_self _ _ _
    · change Function.update (replay s T u v p n).parent (T + n + 1) _ (T + j + 1) = _
      rw [Function.update_of_ne (by omega)]
      exact ih j (by omega)

theorem replay_frozenAt_new (s : Forward.State) (T u v : ℕ) (p : ℕ → ℕ)
    (n j : ℕ) (hj : j < n) : (replay s T u v p n).frozenAt (T + j + 1) = none := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
    by_cases hlast : j = n
    · subst j
      change Function.update (replay s T u v p n).frozenAt (T + n + 1) none (T + n + 1) = none
      exact Function.update_self _ _ _
    · change Function.update (replay s T u v p n).frozenAt (T + n + 1) none (T + j + 1) = none
      rw [Function.update_of_ne (by omega)]
      exact ih j (by omega)

theorem continuationLaw_ae_valid {s : Forward.State} {T : ℕ} (hs : Forward.ValidAt T s) (n : ℕ) :
    ∀ᵐ q ∂continuationLaw s T n, Forward.ValidAt (T + n) q := by
  induction n with
  | zero =>
    change ∀ᵐ q ∂Measure.dirac s, Forward.ValidAt T q
    exact (ae_dirac_iff MeasurableSet.of_discrete).mpr hs
  | succ n ih =>
    rw [ae_iff, continuationLaw, Measure.bind_apply (by trivial) measurable_from_top.aemeasurable]
    apply (lintegral_eq_zero_iff measurable_from_top).mpr
    filter_upwards [ih] with q hq
    apply ae_iff.mp
    exact Forward.transitionLaw_ae q (T + n + 1) true (Forward.ValidAt (T + (n + 1)))
      (fun _ => hq.mono (by omega))
      (fun a _ => by simpa only [Nat.add_assoc] using hq.step true a)

end FreezingGrowth.TwoSeedGraft
