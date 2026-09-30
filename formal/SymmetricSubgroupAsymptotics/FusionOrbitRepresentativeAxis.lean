import SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeCharts
import SymmetricSubgroupAsymptotics.BinaryConjugacyTransport
import SymmetricSubgroupAsymptotics.OrbitProfileFromOrbits

/-!
# Goursat axes under a change of labels on one actual orbit

The canonical actual-orbit chart and the representative chart differ only
by conjugating the first block.  Their deleted models are therefore related
by the corresponding first-coordinate group equivalence, with the complete
exterior coordinate left unchanged.  In particular their Goursat axes are
carried by the same equivalence.

This is the chart-conjugacy bridge used after
`BinaryCarrierCanonicalOrbitAxisBridge`: a slot on a witness axis can be
pulled back to the axis determined by a canonical local orbit chart.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical Pointwise

namespace SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeAxis

open SymmetricSubgroupAsymptotics

variable {n w : ℕ} (H : Subgroup (Equiv.Perm (Fin n))) (x : Fin n)
    (hw : Nat.card (MulAction.orbit H x) = w)

/-- The first action in the canonical actual-orbit chart. -/
abbrev ActualAction : Subgroup (Equiv.Perm (Fin w)) :=
  FusionActualOrbitCharts.chartAction H x hw

/-- The same action after changing the labels on the selected orbit by `c`. -/
abbrev RepresentativeAction (c : Equiv.Perm (Fin w)) :
    Subgroup (Equiv.Perm (Fin w)) :=
  MulAut.conj c • ActualAction H x hw

/-- Ambient conjugation as an equivalence between the two literal action
subgroups. -/
def representativeActionEquiv (c : Equiv.Perm (Fin w)) :
    ActualAction H x hw ≃* RepresentativeAction H x hw c :=
  actionConjugacyEquiv c rfl

/-- The coordinate change whose representative chart has prescribed first
point chart `e`. -/
def chartConjugator
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x) :
    Equiv.Perm (Fin w) :=
  (FusionActualOrbitCharts.orbitEquiv H x hw).trans e.symm

@[simp] theorem representativeChart_chartConjugator_inl
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x) (i : Fin w) :
    FusionOrbitRepresentativeCharts.chart H x hw (chartConjugator H x hw e)
        (Sum.inl i) = (e i : Fin n) := by
  simp [FusionOrbitRepresentativeCharts.chart,
    FusionActualOrbitCharts.chart_inl, chartConjugator]

/-- The canonical chart action has exactly the original restriction image
after applying its canonical point chart. -/
theorem orbitEquiv_chartAction_image :
    relabelSubgroup (FusionActualOrbitCharts.orbitEquiv H x hw)
        (ActualAction H x hw) =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H) := by
  change relabelSubgroup (FusionActualOrbitCharts.orbitEquiv H x hw)
      (FusionActualOrbitCharts.chartAction H x hw) = _
  rw [FusionActualOrbitCharts.chartAction_eq_map]
  exact relabelSubgroup_symm
    (FusionActualOrbitCharts.orbitEquiv H x hw).symm _

/-- If `U` is the same actual orbit image in a prescribed local point chart,
then it is literally the representative action for the resulting coordinate
change. -/
theorem representativeAction_eq_of_image
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H)) :
    RepresentativeAction H x hw (chartConjugator H x hw e) = U := by
  change relabelSubgroup (chartConjugator H x hw e)
      (ActualAction H x hw) = U
  apply (relabelSubgroup e).injective
  have hc : (chartConjugator H x hw e).trans e =
      FusionActualOrbitCharts.orbitEquiv H x hw := by
    ext i
    simp [chartConjugator]
  rw [relabelSubgroup_trans, hc, orbitEquiv_chartAction_image H x hw,
    himage]

/-- The fusion-natural action equivalence from the witness chart action to
the action written in an arbitrary exact point chart on the same orbit. -/
def localActionEquiv
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H)) :
    ActualAction H x hw ≃* U :=
  (representativeActionEquiv H x hw (chartConjugator H x hw e)).trans
    (MulEquiv.subgroupCongr
      (representativeAction_eq_of_image H x hw e U himage))

/-- The canonical complete orbit/complement deleted model. -/
def actualDeletedModel :
    Subgroup (ActualAction H x hw × Equiv.Perm (Fin (n-w))) :=
  fusionDeletedModel (ActualAction H x hw)
    (relabelSubgroup (FusionActualOrbitCharts.chart H x hw).symm H)

/-- The complete deleted model after changing only the labels on the selected
orbit. -/
def representativeDeletedModel (c : Equiv.Perm (Fin w)) :
    Subgroup (RepresentativeAction H x hw c × Equiv.Perm (Fin (n-w))) :=
  fusionDeletedModel (RepresentativeAction H x hw c)
    (relabelSubgroup
      (FusionOrbitRepresentativeCharts.chart H x hw c).symm H)

/-- The complete deleted model in an arbitrary exact local point chart. -/
def localDeletedModel
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x)
    (U : Subgroup (Equiv.Perm (Fin w))) :
    Subgroup (U × Equiv.Perm (Fin (n-w))) :=
  fusionDeletedModel U
    (relabelSubgroup
      (FusionOrbitRepresentativeCharts.chart H x hw
        (chartConjugator H x hw e)).symm H)

/-- Bundle the canonical first restriction in its exact image subgroup. -/
def actualFirstHom : H →* ActualAction H x hw :=
  (FusionActualOrbitCharts.firstHom H x hw).codRestrict
    (ActualAction H x hw) (fun g => by
      change FusionActualOrbitCharts.firstHom H x hw g ∈
        FusionActualOrbitCharts.chartAction H x hw
      rw [FusionActualOrbitCharts.chartAction_eq_range]
      exact ⟨g,rfl⟩)

/-- Both canonical restriction coordinates, with the first one bundled in
its exact action subgroup. -/
def actualPairHom :
    H →* ActualAction H x hw × Equiv.Perm (Fin (n-w)) :=
  (actualFirstHom H x hw).prod
    (FusionActualOrbitCharts.secondHom H x hw)

/-- The representative first restriction is canonical restriction followed
by the same ambient conjugacy used on the orbit points. -/
def representativeFirstHom (c : Equiv.Perm (Fin w)) :
    H →* RepresentativeAction H x hw c :=
  (representativeActionEquiv H x hw c).toMonoidHom.comp
    (actualFirstHom H x hw)

/-- Both representative restriction coordinates.  The exterior coordinate
is literally the canonical one. -/
def representativePairHom (c : Equiv.Perm (Fin w)) :
    H →* RepresentativeAction H x hw c × Equiv.Perm (Fin (n-w)) :=
  (representativeFirstHom H x hw c).prod
    (FusionActualOrbitCharts.secondHom H x hw)

private theorem pairSubtypeEmbedding_injective
    {A G : Type*} [Group A] [Group G] (U : Subgroup A) :
    Function.Injective (fun p : U × G => ((p.1 : A),p.2)) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst h
  · simpa using congrArg Prod.snd h

@[simp] theorem actualPairHom_coe (g : H) :
    (((actualPairHom H x hw g).1 : Equiv.Perm (Fin w)),
        (actualPairHom H x hw g).2) =
      FusionActualOrbitCharts.pairHom H x hw g := by
  rfl

@[simp] theorem representativePairHom_coe
    (c : Equiv.Perm (Fin w)) (g : H) :
    (((representativePairHom H x hw c g).1 : Equiv.Perm (Fin w)),
        (representativePairHom H x hw c g).2) =
      FusionOrbitRepresentativeCharts.pairHom H x hw c g := by
  apply Prod.ext
  · change c * FusionActualOrbitCharts.firstHom H x hw g * c⁻¹ =
      c.permCongr (FusionActualOrbitCharts.firstHom H x hw g)
    rfl
  · rfl

/-- The canonical deleted model is exactly the range of the two simultaneous
restrictions, with the first coordinate bundled in its image subgroup. -/
theorem actualDeletedModel_eq_range :
    actualDeletedModel H x hw = (actualPairHom H x hw).range := by
  ext p
  change ((p.1 : Equiv.Perm (Fin w)),p.2) ∈
      fusionPhysicalBlockPullback
        (relabelSubgroup (FusionActualOrbitCharts.chart H x hw).symm H) ↔
    p ∈ (actualPairHom H x hw).range
  rw [FusionActualOrbitCharts.blockPullback_eq_range]
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    apply pairSubtypeEmbedding_injective (ActualAction H x hw)
    exact (actualPairHom_coe H x hw g).trans hg
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    exact (actualPairHom_coe H x hw g).symm.trans
      (congrArg
        (fun p : ActualAction H x hw × Equiv.Perm (Fin (n-w)) =>
          ((p.1 : Equiv.Perm (Fin w)),p.2)) hg)

/-- The representative deleted model is the corresponding conjugated
simultaneous-restriction range. -/
theorem representativeDeletedModel_eq_range (c : Equiv.Perm (Fin w)) :
    representativeDeletedModel H x hw c =
      (representativePairHom H x hw c).range := by
  ext p
  change ((p.1 : Equiv.Perm (Fin w)),p.2) ∈
      fusionPhysicalBlockPullback
        (relabelSubgroup
          (FusionOrbitRepresentativeCharts.chart H x hw c).symm H) ↔
    p ∈ (representativePairHom H x hw c).range
  rw [FusionOrbitRepresentativeCharts.blockPullback_eq_range]
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    apply pairSubtypeEmbedding_injective (RepresentativeAction H x hw c)
    exact (representativePairHom_coe H x hw c g).trans hg
  · rintro ⟨g,hg⟩
    refine ⟨g,?_⟩
    exact (representativePairHom_coe H x hw c g).symm.trans
      (congrArg
        (fun p : RepresentativeAction H x hw c ×
            Equiv.Perm (Fin (n-w)) =>
          ((p.1 : Equiv.Perm (Fin w)),p.2)) hg)

/-- Relabelling one orbit maps the whole deleted model by the induced first
coordinate equivalence and the identity on the complete exterior. -/
theorem representativeDeletedModel_eq_map (c : Equiv.Perm (Fin w)) :
    representativeDeletedModel H x hw c =
      (actualDeletedModel H x hw).map
        (((representativeActionEquiv H x hw c).prodCongr
          (MulEquiv.refl (Equiv.Perm (Fin (n-w))))).toMonoidHom) := by
  rw [representativeDeletedModel_eq_range,actualDeletedModel_eq_range,
    MonoidHom.map_range]
  apply congrArg MonoidHom.range
  ext g <;> rfl

section GoursatTransport

variable {A B G : Type*} [Group A] [Group B] [Group G]

/-- The Goursat first axis is natural under an equivalence of the first
coordinate and an automorphism of the exterior coordinate. -/
private theorem goursatFst_map_prod_equiv (K : Subgroup (A × G))
    (e : A ≃* B) (f : G ≃* G) :
    (K.map (e.prodCongr f).toMonoidHom).goursatFst =
      K.goursatFst.map e.toMonoidHom := by
  ext b
  rw [Subgroup.mem_goursatFst]
  constructor
  · rintro ⟨⟨a,g⟩,hag,heq⟩
    have ha : e a = b := congrArg Prod.fst heq
    have hg : f g = 1 := congrArg Prod.snd heq
    have hg' : g = 1 := f.injective (hg.trans f.map_one.symm)
    subst g
    exact ⟨a,Subgroup.mem_goursatFst.mpr hag,ha⟩
  · rintro ⟨a,ha,heq⟩
    exact ⟨(a,1),Subgroup.mem_goursatFst.mp ha,
      by simpa using Prod.ext heq f.map_one⟩

end GoursatTransport

/-- Changing only the labels on the selected orbit transports the witness
axis by the same literal action equivalence. -/
theorem representativeDeletedAxis_eq_map (c : Equiv.Perm (Fin w)) :
    (representativeDeletedModel H x hw c).goursatFst =
      (actualDeletedModel H x hw).goursatFst.map
        (representativeActionEquiv H x hw c).toMonoidHom := by
  rw [representativeDeletedModel_eq_map]
  exact goursatFst_map_prod_equiv (actualDeletedModel H x hw)
    (representativeActionEquiv H x hw c)
    (MulEquiv.refl (Equiv.Perm (Fin (n-w))))

/-- Pullback-ready orientation: transporting the representative axis back
along the inverse action equivalence recovers the original witness axis.
This is the equality required by `AxisSlot.pullback`. -/
theorem representativeDeletedAxis_map_symm_eq (c : Equiv.Perm (Fin w)) :
    (representativeDeletedModel H x hw c).goursatFst.map
        (representativeActionEquiv H x hw c).symm.toMonoidHom =
      (actualDeletedModel H x hw).goursatFst := by
  rw [representativeDeletedAxis_eq_map,Subgroup.map_map]
  simpa using Subgroup.map_id (actualDeletedModel H x hw).goursatFst

/-- In any exact local point chart, the selected physical axis is the witness
axis transported by the induced action equivalence.  Combined with
`canonicalAxis_eq_fusionDeletedAxis`, this is the direct canonical-local-axis
identification. -/
theorem localDeletedAxis_eq_map
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H)) :
    (localDeletedModel H x hw e U).goursatFst =
      (actualDeletedModel H x hw).goursatFst.map
        (localActionEquiv H x hw e U himage).toMonoidHom := by
  have hU := representativeAction_eq_of_image H x hw e U himage
  subst U
  simpa [localDeletedModel,localActionEquiv] using
    representativeDeletedAxis_eq_map H x hw (chartConjugator H x hw e)

/-- Pullback-ready local-chart form.  A witness `AxisSlot` can be pulled back
along `localActionEquiv.symm` using exactly this equality. -/
theorem localDeletedAxis_map_symm_eq
    (e : Fin w ≃ FusionActualOrbitCharts.orbitSet H x)
    (U : Subgroup (Equiv.Perm (Fin w)))
    (himage : relabelSubgroup e U =
      OrbitProfileFromOrbits.orbitImage H
        (Quotient.mk'' x : OrbitProfileFromOrbits.Orbit H)) :
    (localDeletedModel H x hw e U).goursatFst.map
        (localActionEquiv H x hw e U himage).symm.toMonoidHom =
      (actualDeletedModel H x hw).goursatFst := by
  rw [localDeletedAxis_eq_map H x hw e U himage,Subgroup.map_map]
  simpa using Subgroup.map_id (actualDeletedModel H x hw).goursatFst

end SymmetricSubgroupAsymptotics.FusionOrbitRepresentativeAxis

end
