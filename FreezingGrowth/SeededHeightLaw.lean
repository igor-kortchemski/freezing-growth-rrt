module

public import FreezingGrowth.SeededHeightGrowth
public import FreezingGrowth.RRTSplitLaw

/-! Pure attachment from one or two active seeds, with the actual RRT laws. -/

@[expose] public section
namespace FreezingGrowth.HeightProfile

open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

instance : Countable HeightProfile :=
  Function.Injective.countable (f := fun p : HeightProfile => (p.activeDepths, p.maximum)) (by
    intro p q h
    exact HeightProfile.ext (congrArg Prod.fst h) (congrArg Prod.snd h))

def project (a b M : ℕ) (r : RRTSplit.Result) : HeightProfile :=
  join a b M (ofState r.2.1) (ofState r.2.2)

theorem measurable_project (a b M : ℕ) : Measurable (project a b M) := by
  have ho : Measurable ofState := measurable_from_top
  have hj : Measurable (fun p : HeightProfile × HeightProfile => join a b M p.1 p.2) :=
    measurable_of_countable _
  exact hj.comp (((ho.comp measurable_fst).prodMk (ho.comp measurable_snd)).comp measurable_snd)

theorem single_seed_growth (a M : ℕ) (ha : a ≤ M) (n : ℕ) :
    grow ⟨{a}, M⟩ n =
      (Forward.treeLaw RRT.allAttach n).map (fun s => shift a M (ofState s)) := by
  induction n with
  | zero =>
    simp [grow, Forward.treeLaw, ofState_initial, shift, initial, max_eq_left ha]
  | succ n ih =>
    rw [grow, ih, Forward.treeLaw,
      Measure.bind_map measurable_from_top.aemeasurable measurable_from_top.aemeasurable,
      Measure.map_bind measurable_from_top.aemeasurable measurable_from_top.aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [Forward.treeLaw_valid RRT.allAttach n,
      Forward.treeLaw_active_nonempty RRT.allAttach n (RRT.before_extinction n)] with s hs hne
    have hp : (ofState s).activeDepths ≠ 0 := by
      intro h
      exact hne.ne_empty ((activeDepths_eq_zero_iff s).mp h)
    rw [← shift_transition a M (ofState s) hp, ← map_transitionLaw hs true,
      Measure.map_map measurable_from_top measurable_from_top]
    rfl

theorem map_sizeKernel_project (a b M k l : ℕ) (s t : Forward.State)
    (hs : Forward.ValidAt k s) (ht : Forward.ValidAt l t)
    (hcs : s.active.card = k + 1) (hct : t.active.card = l + 1) :
    ((RRTSplit.sizeKernel k l) (s, t)).map (project a b M) =
      transitionLaw (join a b M (ofState s) (ofState t)) true := by
  have hps : (ofState s).activeDepths.card = k + 1 := by simpa using hcs
  have hpt : (ofState t).activeDepths.card = l + 1 := by simpa using hct
  have hml : Measurable (Prod.mk (k + 1) :
      Forward.State × Forward.State → RRTSplit.Result) := measurable_prodMk_left
  have hmr : Measurable (Prod.mk k :
      Forward.State × Forward.State → RRTSplit.Result) := measurable_prodMk_left
  have hl : ((RRTSplit.leftKernel k) (s, t)).map (project a b M) =
      (transitionLaw (ofState s) true).map (fun p => join a b M p (ofState t)) := by
    rw [RRTSplit.leftKernel, Kernel.map_apply _ hml,
      Kernel.parallelComp_apply, Kernel.id_apply, RRTSplit.attachmentKernel,
      Kernel.coe_mk, Measure.prod_dirac,
      Measure.map_map (measurable_project a b M) hml,
      Measure.map_map ((measurable_project a b M).comp hml) (by fun_prop),
      ← map_transitionLaw hs true,
      Measure.map_map measurable_from_top measurable_from_top]
    rfl
  have hr : ((RRTSplit.rightKernel k l) (s, t)).map (project a b M) =
      (transitionLaw (ofState t) true).map (fun q => join a b M (ofState s) q) := by
    rw [RRTSplit.rightKernel, Kernel.map_apply _ hmr,
      Kernel.parallelComp_apply, Kernel.id_apply, RRTSplit.attachmentKernel,
      Kernel.coe_mk, Measure.dirac_prod,
      Measure.map_map (measurable_project a b M) hmr,
      Measure.map_map ((measurable_project a b M).comp hmr) measurable_prodMk_left,
      ← map_transitionLaw ht true,
      Measure.map_map measurable_from_top measurable_from_top]
    rfl
  rw [RRTSplit.sizeKernel, Kernel.coe_mk,
    Measure.map_add _ _ (measurable_project a b M),
    Measure.map_smul _ (measurable_project a b M).aemeasurable,
    Measure.map_smul _ (measurable_project a b M).aemeasurable, hl, hr,
    join_transition a b M _ _ (by rw [hps]; omega) (by rw [hpt]; omega), hps, hpt]
  rw [show k + l + 2 = k + 1 + (l + 1) by omega]

theorem join_seed_growth (a b M : ℕ) (hab : max a b ≤ M) (n : ℕ) :
    grow ⟨{a, b}, M⟩ n = (RRTSplit.mixtureLaw n).map (project a b M) := by
  induction n with
  | zero =>
    rw [grow, RRTSplit.mixtureLaw_zero, Measure.map_dirac' (measurable_project a b M)]
    congr 1
    ext <;> simp [project, join, ofState_initial, initial, max_eq_left hab]
  | succ n ih =>
    rw [grow, ih, ← RRTSplit.growthKernel_comp_mixtureLaw,
      Measure.map_bind (RRTSplit.growthKernel n).aemeasurable
        (measurable_project a b M).aemeasurable,
      Measure.bind_map (measurable_project a b M).aemeasurable
        measurable_from_top.aemeasurable,
      ← RRTSplit.treeLaw_firstEdgeSplit n,
      Measure.bind_map (f := RRTSplit.firstEdgeSplit n)
        (g := fun r => transitionLaw (project a b M r) true) measurable_from_top.aemeasurable
        (by
          have hf : Measurable (fun p : HeightProfile => transitionLaw p true) :=
            measurable_from_top
          exact (hf.comp (measurable_project a b M)).aemeasurable),
      Measure.bind_map (f := RRTSplit.firstEdgeSplit n)
        (g := fun r => ((RRTSplit.growthKernel n) r).map (project a b M))
        measurable_from_top.aemeasurable
        ((Measure.measurable_map _ (measurable_project a b M)).comp
          (RRTSplit.growthKernel n).measurable).aemeasurable]
    apply Measure.bind_congr_right
    filter_upwards [RRTSplit.treeLaw_split_describes n] with s hs
    let p := RRTSplit.split n s
    have hp : RRTSplit.Describes n s p := hs
    have hsum := hp.formed.edges_sum
    have hpos := hp.formed.root.length_pos
    have hpos' := hp.formed.child.length_pos
    have hright : n - (p.rootSide.labels.length - 1) = p.childSide.labels.length - 1 := by
      omega
    change transitionLaw (join a b M (ofState p.rootSide.tree)
      (ofState p.childSide.tree)) true =
        ((RRTSplit.sizeKernel (p.rootSide.labels.length - 1)
          (n - (p.rootSide.labels.length - 1)))
            (p.rootSide.tree, p.childSide.tree)).map (project a b M)
    rw [hright]
    exact (map_sizeKernel_project a b M _ _ _ _ hp.formed.root.valid hp.formed.child.valid
      (by rw [hp.formed.root.active]; simp; omega)
      (by rw [hp.formed.child.active]; simp; omega)).symm

end FreezingGrowth.HeightProfile
