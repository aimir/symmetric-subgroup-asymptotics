import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitCell

/-!
# Exact target restriction images on unrecorded S16 cells

The unrecorded-orbit argument already shows that a one-cell routed source
block is an orbit of the fusion-natural target.  For reconstruction one also
needs the action on that orbit.  This file retains the canonical block chart
and identifies the complete target restriction image with the displayed
mixture action on that chart.

The result is deliberately independent of the five omitted certificate
constructors.  Their only remaining obligation is local: compute the
one-cell chart and compare it with the exact source-orbit chart stored by the
same certificate.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageAccessor

open SymmetricSubgroupAsymptotics
open BinaryCarrierCellProfile
open BinaryCarrierProfileTransport
open BinaryS16UnrecordedOrbitCell

/-! ## Exact image of a prescribed full-profile block -/

/-- Relabelling a dependent permutation subgroup along the cast induced by
an equality of its index is the subgroup at the transported index. -/
theorem relabelSubgroup_cast_index
    {I : Type*} (Omega : I → Type*)
    (U : ∀ i, Subgroup (Equiv.Perm (Omega i)))
    {i j : I} (h : i = j) :
    relabelSubgroup (Equiv.cast (congrArg Omega h)) (U i) = U j := by
  cases h
  exact relabelSubgroup_refl _

/-- The literal chart of one prescribed transitive block onto the orbit of
one of its points.  Unlike the existential orbit-chart theorem, this keeps
the original occurrence index and the pointwise ambient chart definition. -/
def blockOrbitEquiv
    {ι X : Type*} {Omega : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Omega i))}
    {e : OrbitProfilePoints Omega m ≃ X}
    {G : Subgroup (Equiv.Perm X)}
    (hG : OrbitProfileFullOn U e G)
    {i : ι} (htrans : ∀ x y : Omega i,
      ∃ u : U i, (u : Equiv.Perm (Omega i)) x = y)
    (j : Fin (m i)) (x : Omega i) :
    Omega i ≃
      MulAction.orbitRel.Quotient.orbit
        (Quotient.mk'' (e ⟨i,j,x⟩) :
          OrbitProfileFromOrbits.Orbit G) :=
  let z : X := e ⟨i,j,x⟩
  let o : OrbitProfileFromOrbits.Orbit G := Quotient.mk'' z
  let f : Omega i → X := fun y ↦ e ⟨i,j,y⟩
  let hinj : Function.Injective f := by
    intro y w hyw
    have h := e.injective hyw
    have hp : (j,y) = (j,w) := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    exact congrArg Prod.snd hp
  let hb : Set.range f = o.orbit := by
    rw [← BinaryS16RecordedBlockRecovery.orbit_eq_block_of_transitive
      hG htrans j x]
    exact (MulAction.orbitRel.Quotient.orbit_mk z).symm
  (Equiv.ofInjective f hinj).trans (Equiv.setCongr hb)

@[simp] theorem blockOrbitEquiv_val
    {ι X : Type*} {Omega : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Omega i))}
    {e : OrbitProfilePoints Omega m ≃ X}
    {G : Subgroup (Equiv.Perm X)}
    (hG : OrbitProfileFullOn U e G)
    {i : ι} (htrans : ∀ x y : Omega i,
      ∃ u : U i, (u : Equiv.Perm (Omega i)) x = y)
    (j : Fin (m i)) (x y : Omega i) :
    ((blockOrbitEquiv hG htrans j x y :
        MulAction.orbitRel.Quotient.orbit
          (Quotient.mk'' (e ⟨i,j,x⟩) :
            OrbitProfileFromOrbits.Orbit G)) : X) = e ⟨i,j,y⟩ :=
  rfl

/-- Fullness identifies the entire restriction image on a prescribed
transitive block, in the literal chart above. -/
theorem blockOrbitEquiv_image
    {ι X : Type*} {Omega : ι → Type*} {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Omega i))}
    {e : OrbitProfilePoints Omega m ≃ X}
    {G : Subgroup (Equiv.Perm X)}
    (hG : OrbitProfileFullOn U e G)
    {i : ι} (htrans : ∀ x y : Omega i,
      ∃ u : U i, (u : Equiv.Perm (Omega i)) x = y)
    (j : Fin (m i)) (x : Omega i) :
    relabelSubgroup (blockOrbitEquiv hG htrans j x) (U i) =
      OrbitProfileFromOrbits.orbitImage G
        (Quotient.mk'' (e ⟨i,j,x⟩) :
          OrbitProfileFromOrbits.Orbit G) := by
  let c := blockOrbitEquiv hG htrans j x
  let o : OrbitProfileFromOrbits.Orbit G := Quotient.mk'' (e ⟨i,j,x⟩)
  have hc (y : Omega i) : (c y : X) = e ⟨i,j,y⟩ := by
    exact blockOrbitEquiv_val hG htrans j x y
  have htransport (g : G) (u : U i)
      (hu : ∀ y : Omega i, (g : Equiv.Perm X) (e ⟨i,j,y⟩) =
        e ⟨i,j,(u : Equiv.Perm (Omega i)) y⟩) :
      c.permCongr (u : Equiv.Perm (Omega i)) =
        MulAction.toPermHom G o.orbit g := by
    apply Equiv.ext
    intro q
    apply Subtype.ext
    change (c ((u : Equiv.Perm (Omega i)) (c.symm q)) : X) =
      (g : Equiv.Perm X) (q : X)
    rw [hc, ← hu]
    have hq : e ⟨i,j,c.symm q⟩ = (q : X) := by
      simpa only [c] using congrArg Subtype.val (c.apply_symm_apply q)
    exact congrArg (g : Equiv.Perm X) hq
  ext v
  change v ∈ (U i).map c.permCongrHom.toMonoidHom ↔
    v ∈ (MulAction.toPermHom G o.orbit).range
  constructor
  · rintro ⟨u,hu,rfl⟩
    obtain ⟨g,hg⟩ := hG.full i j ⟨u,hu⟩
    exact ⟨g,(htransport g ⟨u,hu⟩ hg).symm⟩
  · rintro ⟨g,rfl⟩
    obtain ⟨u,hu⟩ := hG.maps g i j
    exact ⟨u.val,u.property,htransport g u hu⟩

/-! ## The exact action on an S16 one-cell source block -/

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)

/-- The final S16 assembly map is, on one literal occurrence, the exact
orbit chart stored by that occurrence's selected local model. -/
@[simp] theorem assemble_apply_localModelChart
    (q : Occurrence H hH)
    (x : BinaryS16JointOrbitData.Points H hH q.1) :
    BinaryS16FusionNaturalPointChart.assemble H hH ⟨q,x⟩ =
      (((BinaryS16JointOrbitData.localModel H hH q.1).chart.pointEquiv x :
        q.1.orbit) : Fin (2 * N)) := by
  change
    ((((BinaryS16JointOrbitData.data H hH).localChart q.1 q.2 x :
        ((BinaryS16JointOrbitData.data H hH).orbitIndex q).orbit) :
      Fin (2 * N))) = _
  rw [BinaryS16JointAxisRouting.localChart_eq_transportedModelChart H hH q]
  exact BinaryS16JointAxisRouting.exactOrbitChart_transport_point_coe
    H (BinaryS16JointOrbitData.orbitIndex_eq_fst H hH q).symm
      (BinaryS16JointOrbitData.localModel H hH q.1).chart x

/-- A one-cell routed source occurrence carries not only a target orbit with
the same point set, but the complete restriction image of the target.  After
transport to the literal source block, that image is exactly the mixture
action in the cell chart used by the fusion-natural construction.

This is the action-level strengthening of
`targetOrbit_eq_sourceOrbit_of_uniqueCell`. -/
theorem targetOrbitImage_eq_sourceBlockAction_of_uniqueCell
    {G : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (hG : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH) G)
    (q : Occurrence H hH) (c : (RouteSlot H hH q).Cells)
    (hunique : ∀ d : (RouteSlot H hH q).Cells, d = c)
    (htrans : PermutationSubgroupTransitive
      (mixtureAction ((RouteSlot H hH q).color c))) :
    ∃ z : Fin (2 * N), ∃ hz :
        MulAction.orbit G z = q.1.orbit,
      ∃ chart : mixturePoints ((RouteSlot H hH q).color c) ≃ q.1.orbit,
        relabelSubgroup (Equiv.setCongr hz)
            (OrbitProfileFromOrbits.orbitImage G (Quotient.mk'' z)) =
          relabelSubgroup chart
            (mixtureAction ((RouteSlot H hH q).color c)) ∧
        ∀ y,
          ((chart y : q.1.orbit) : Fin (2 * N)) =
            BinaryS16FusionNaturalPointChart.assemble H hH
              ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩⟩ := by
  let d : Cell H hH := ⟨q,c⟩
  let a := cellToOccurrence
    (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
    (cellColor H hH) d
  let castPoint : mixturePoints (cellColor H hH d) ≃ mixturePoints a.1 :=
    Equiv.cast (congrArg mixturePoints
      (cellToOccurrence_color
        (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
        (cellColor H hH) d).symm)
  let x : mixturePoints (cellColor H hH d) := Classical.choice inferInstance
  let z : Fin (2 * N) :=
    cellPointChart H hH ⟨a.1,a.2,castPoint x⟩
  have hfull := target_full_on_cellPointChart H hH hG
  have htrans' : PermutationSubgroupTransitive (mixtureAction a.1) := by
    rw [cellToOccurrence_color
      (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
      (cellColor H hH) d]
    exact htrans
  have htransSubtype : ∀ u v : mixturePoints a.1,
      ∃ g : mixtureAction a.1,
        (g : Equiv.Perm (mixturePoints a.1)) u = v := by
    intro u v
    obtain ⟨g,hg,huv⟩ := htrans' u v
    exact ⟨⟨g,hg⟩,huv⟩
  let p : OrbitProfileFromOrbits.Orbit G := Quotient.mk'' z
  have hpblock : p.orbit =
      Set.range (fun y : mixturePoints a.1 ↦
        cellPointChart H hH ⟨a.1,a.2,y⟩) := by
    exact BinaryS16RecordedBlockRecovery.orbit_eq_block_of_transitive
      hfull htransSubtype
      a.2 (castPoint x)
  have hblockSource :
      Set.range (fun y : mixturePoints a.1 ↦
        cellPointChart H hH ⟨a.1,a.2,y⟩) = q.1.orbit := by
    calc
      Set.range (fun y : mixturePoints a.1 ↦
          cellPointChart H hH ⟨a.1,a.2,y⟩) =
          Set.range (fun y : mixturePoints (cellColor H hH d) ↦
            BinaryS16FusionNaturalPointChart.assemble H hH
              ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩⟩) := by
        ext w
        constructor
        · rintro ⟨y,rfl⟩
          obtain ⟨y,rfl⟩ := castPoint.surjective y
          refine ⟨y,?_⟩
          simpa only [d,a,castPoint,cellColor] using
            (cellPointChart_apply H hH d y).symm
        · rintro ⟨y,rfl⟩
          refine ⟨castPoint y,?_⟩
          simpa only [d,a,castPoint,cellColor] using
            cellPointChart_apply H hH d y
      _ = Set.range (fun y : BinaryS16JointOrbitData.Points H hH q.1 ↦
            BinaryS16FusionNaturalPointChart.assemble H hH ⟨q,y⟩) := by
        ext w
        constructor
        · rintro ⟨y,rfl⟩
          exact ⟨BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩,rfl⟩
        · rintro ⟨y,rfl⟩
          obtain ⟨x,hx⟩ := slotChart_fixedCell_surjective H hH q c hunique y
          exact ⟨x,congrArg
            (fun t ↦ BinaryS16FusionNaturalPointChart.assemble H hH ⟨q,t⟩)
            hx⟩
      _ = q.1.orbit := assemble_block H hH q
  have hz : MulAction.orbit G z = q.1.orbit := hpblock.trans hblockSource
  let targetChart : mixturePoints a.1 ≃ p.orbit :=
    blockOrbitEquiv hfull htransSubtype a.2 (castPoint x)
  let sourceChartA : mixturePoints a.1 ≃ q.1.orbit :=
    targetChart.trans (Equiv.setCongr hz)
  let sourceChart : mixturePoints ((RouteSlot H hH q).color c) ≃ q.1.orbit :=
    castPoint.trans sourceChartA
  have hcastAction :
      relabelSubgroup castPoint
          (mixtureAction ((RouteSlot H hH q).color c)) =
        mixtureAction a.1 := by
    exact relabelSubgroup_cast_index mixturePoints mixtureAction
      (cellToOccurrence_color
        (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
        (cellColor H hH) d).symm
  refine ⟨z,hz,sourceChart,?_,?_⟩
  · calc
      relabelSubgroup (Equiv.setCongr hz)
          (OrbitProfileFromOrbits.orbitImage G p) =
          relabelSubgroup (Equiv.setCongr hz)
            (relabelSubgroup targetChart (mixtureAction a.1)) := by
              rw [blockOrbitEquiv_image hfull htransSubtype
                a.2 (castPoint x)]
      _ = relabelSubgroup sourceChartA (mixtureAction a.1) := by
            exact relabelSubgroup_trans targetChart (Equiv.setCongr hz)
              (mixtureAction a.1)
      _ = relabelSubgroup sourceChart
          (mixtureAction ((RouteSlot H hH q).color c)) := by
            rw [← hcastAction]
            exact relabelSubgroup_trans castPoint sourceChartA
              (mixtureAction ((RouteSlot H hH q).color c))
  · intro y
    change ((sourceChartA (castPoint y) : q.1.orbit) : Fin (2 * N)) = _
    change ((targetChart (castPoint y) : p.orbit) : Fin (2 * N)) = _
    rw [blockOrbitEquiv_val]
    simpa only [d,a,castPoint,cellColor] using cellPointChart_apply H hH d y

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageAccessor

end
