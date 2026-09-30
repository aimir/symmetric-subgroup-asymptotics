import SymmetricSubgroupAsymptotics.BinaryS16RecordedBlockRecovery
import SymmetricSubgroupAsymptotics.BinaryS16TargetOrbitAccessor
import SymmetricSubgroupAsymptotics.BinaryS16DirectPhysicalEncoding

/-!
# One-cell S16 source orbits inside the physical target

The mixed table deliberately omits the one-cell routes: the four critical
actions and the regular cyclic-four action.  Those blocks are nevertheless
visible without a further mark.  The fusion-natural target is full on the
exact original-label chart, and a one-cell route occupies one complete orbit
of that target.

This file proves that statement at the literal point-set level.  The only
routes not covered by the one-cell argument are the degree-eight and
degree-sixteen carrier routes, and those are impossible under the hypothesis
that the orbit emitted no mixed-table record.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitCell

open SymmetricSubgroupAsymptotics
open BinaryCarrierCellProfile
open BinaryCarrierFusionNaturalPointChart
open BinaryCarrierProfileTransport
open BinaryCarrierWordClosure
open BinaryDegreeEightPhysicalDecoration
open BinaryS16CanonicalCarrierProfile
open BinaryS16CanonicalMixedBlockTable
open BinaryS16DirectCertifiedOrbitProfile
open BinaryS16DirectFixedSupportClosure
open BinaryS16DirectPhysicalEncoding
open BinaryS16DirectPhysicalTarget
open BinaryS16FusionNaturalPointChart
open BinaryS16RecordedBlockRecovery
open BinaryS16TargetOrbitAccessor

/-! ## The cellwise form of the fusion-natural chart -/

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : ResidualSector H)

abbrev Occurrence :=
  BinaryS16FusionNaturalPointChart.Occurrence H hH

abbrev RouteSlot (q : Occurrence H hH) :=
  BinaryS16FusionNaturalPointChart.routeSlot H hH q

abbrev Cell := Σ q : Occurrence H hH, (RouteSlot H hH q).Cells

def cellColor (c : Cell H hH) :
    BinaryCarrierProfileTransport.MixtureKind :=
  (RouteSlot H hH c.1).color c.2

/-- Replace the deterministically selected certificate by a propositionally
equal explicit certificate before reducing its routed slot.  The resulting
slot type is independent of the certificate witness, so equality induction
removes the otherwise troublesome dependent rewrite. -/
theorem routeSlot_eq_of_profile
    (q : Occurrence H hH) (D : OrbitCertificate H q.1)
    (hp : profile H hH q.1 = D) :
    RouteSlot H hH q =
      (BinaryS16JointAxisRouting.routeCertificate H hH q D hp).axisSlot.slot := by
  unfold RouteSlot BinaryS16FusionNaturalPointChart.routeSlot
  unfold BinaryS16JointAxisRouting.axisRouting
  cases hp
  rfl

/-- Transport a constant cell colour back across equality of routed slots.
This isolates the dependent cell argument from ordinary slot rewriting. -/
theorem slot_color_eq_of_eq
    {S T : Slot} {g : BinaryCarrierProfileTransport.MixtureKind}
    (h : S = T) (c : S.Cells)
    (hcolor : ∀ d : T.Cells, T.color d = g) :
    S.color c = g := by
  subst T
  exact hcolor c

/-- The fusion-natural point chart after rewriting its profile multiplicity
as the literal colour-fibre multiplicity of the routed cells.  Naming this
chart removes the harmless outer dependent cast from the cell calculation. -/
def cellPointChart :
    OrbitProfilePoints mixturePoints
      (multiplicity
        (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
        (cellColor H hH)) ≃ Fin (2 * N) :=
  (profilePointEquivOccurrencePoint mixturePoints
      (multiplicity
        (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
        (cellColor H hH))).trans
    ((occurrencePointEquivCellPoint
      (fun q : Occurrence H hH ↦ RouteSlot H hH q)).trans
    ((Equiv.sigmaAssoc (fun q c ↦
      mixturePoints ((RouteSlot H hH q).color c))).trans
    ((Equiv.sigmaCongrRight
      (BinaryS16FusionNaturalPointChart.slotChart H hH)).trans
      (BinaryS16FusionNaturalPointChart.assemble H hH))))

/-- Rewriting the indexed multiplicity turns exact fullness on `pointChart`
into exact fullness on the literal cell chart. -/
theorem fullOn_cast_source
    {I X : Type*} {Omega : I → Type*} {m n : I → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Omega i))}
    {G : Subgroup (Equiv.Perm X)}
    (hm : m = n) (e : OrbitProfilePoints Omega n ≃ X)
    (hG : OrbitProfileFullOn U
      ((Equiv.cast (congrArg (OrbitProfilePoints Omega) hm)).trans e) G) :
    OrbitProfileFullOn U e G := by
  subst n
  simpa using hG

theorem target_full_on_cellPointChart
    {G : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (hG : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH) G) :
    OrbitProfileFullOn mixtureAction (cellPointChart H hH) G := by
  apply fullOn_cast_source
    (BinaryCarrierCellProfile.indexed_multiplicity
      (cells (BinaryS16FusionNaturalPointChart.routeSlot H hH))
      (colors (BinaryS16FusionNaturalPointChart.routeSlot H hH)))
    (cellPointChart H hH)
  simpa only [BinaryS16FusionNaturalPointChart.pointChart,
    BinaryCarrierFusionNaturalPointChart.pointChart, cellPointChart] using hG

/-- A point in a literal routed cell goes, under the cell chart, through the
retained local chart and then through the simultaneous original-orbit chart.
The cast is only the canonical equality between a cell's stored colour and
its colour-fibre occurrence. -/
theorem cellPointChart_apply
    (c : Cell H hH)
    (x : mixturePoints (cellColor H hH c)) :
    let a := cellToOccurrence
      (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
      (cellColor H hH) c
    cellPointChart H hH
        ⟨a.1,a.2,
          Equiv.cast (congrArg mixturePoints
            (cellToOccurrence_color
              (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
              (cellColor H hH) c).symm) x⟩ =
      BinaryS16FusionNaturalPointChart.assemble H hH
        ⟨c.1,
          BinaryS16FusionNaturalPointChart.slotChart H hH c.1 ⟨c.2,x⟩⟩ := by
  let a := cellToOccurrence
    (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
    (cellColor H hH) c
  let e := occurrencePointEquivCellPoint
    (fun q : Occurrence H hH ↦ RouteSlot H hH q)
  have he : e
      ⟨a,
        Equiv.cast (congrArg mixturePoints
          (cellToOccurrence_color
            (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
            (cellColor H hH) c).symm) x⟩ =
      ⟨c,x⟩ := by
    have ha :=
      (occurrenceToCell
        (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
        (cellColor H hH)).apply_symm_apply c
    dsimp [e,a,occurrencePointEquivCellPoint,Equiv.sigmaCongr,
      Equiv.sigmaCongrLeft,Equiv.sigmaCongrRight,cellToOccurrence]
    apply Sigma.ext ha
    exact cast_heq _ _
  change BinaryS16FusionNaturalPointChart.assemble H hH
      ((Equiv.sigmaCongrRight
        (BinaryS16FusionNaturalPointChart.slotChart H hH))
      ((Equiv.sigmaAssoc (fun q c ↦
        mixturePoints ((RouteSlot H hH q).color c)))
      (e ⟨a,
        Equiv.cast (congrArg mixturePoints
          (cellToOccurrence_color
            (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
            (cellColor H hH) c).symm) x⟩))) = _
  rw [he]
  rfl

/-- The final assembly chart sends the complete local point set of a routed
literal occurrence onto precisely its original source orbit. -/
theorem assemble_block (q : Occurrence H hH) :
    Set.range (fun x : BinaryS16JointOrbitData.Points H hH q.1 ↦
      BinaryS16FusionNaturalPointChart.assemble H hH ⟨q,x⟩) =
        q.1.orbit := by
  simpa only [BinaryS16FusionNaturalPointChart.assemble,
    profilePointEquivOccurrencePoint,
    BinaryS16JointOrbitData.orbitIndex_eq_fst] using
      (BinaryS16JointOrbitData.data H hH).chart_block q.1 q.2

/-- One literal cell fills the complete local source model whenever it is
the only cell in its routed slot. -/
theorem slotChart_fixedCell_surjective
    (q : Occurrence H hH) (c : (RouteSlot H hH q).Cells)
    (hunique : ∀ d : (RouteSlot H hH q).Cells, d = c) :
    Function.Surjective (fun x : mixturePoints ((RouteSlot H hH q).color c) ↦
      BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,x⟩) := by
  intro y
  obtain ⟨z,hz⟩ :=
    (BinaryS16FusionNaturalPointChart.slotChart H hH q).surjective y
  rcases z with ⟨d,x⟩
  have hd : d = c := hunique d
  subst d
  exact ⟨x,hz⟩

/-- A one-cell routed source occurrence is an orbit of every subgroup full
on the fusion-natural target chart. -/
theorem targetOrbit_eq_sourceOrbit_of_uniqueCell
    {G : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (hG : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH) G)
    (q : Occurrence H hH) (c : (RouteSlot H hH q).Cells)
    (hunique : ∀ d : (RouteSlot H hH q).Cells, d = c)
    (htrans : PermutationSubgroupTransitive
      (mixtureAction ((RouteSlot H hH q).color c))) :
    ∃ z : Fin (2 * N), MulAction.orbit G z = q.1.orbit := by
  let d : Cell H hH := ⟨q,c⟩
  let a := cellToOccurrence
    (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
    (cellColor H hH) d
  let e : mixturePoints (cellColor H hH d) ≃ mixturePoints a.1 :=
    Equiv.cast (congrArg mixturePoints
      (cellToOccurrence_color
        (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
        (cellColor H hH) d).symm)
  have htrans' : PermutationSubgroupTransitive (mixtureAction a.1) := by
    rw [cellToOccurrence_color
      (fun q : Occurrence H hH ↦ (RouteSlot H hH q).Cells)
      (cellColor H hH) d]
    exact htrans
  have htransSubtype : ∀ x y : mixturePoints a.1,
      ∃ u : mixtureAction a.1,
        (u : Equiv.Perm (mixturePoints a.1)) x = y := by
    intro x y
    obtain ⟨u,hu,hxy⟩ := htrans' x y
    exact ⟨⟨u,hu⟩,hxy⟩
  let x : mixturePoints (cellColor H hH d) := Classical.choice inferInstance
  let z : Fin (2 * N) :=
    BinaryS16FusionNaturalPointChart.assemble H hH
      ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,x⟩⟩
  refine ⟨z,?_⟩
  have horbit := orbit_eq_block_of_transitive
    (target_full_on_cellPointChart H hH hG) htransSubtype a.2 (e x)
  have hbase : cellPointChart H hH ⟨a.1,a.2,e x⟩ = z := by
    simpa only [d,a,e,z,cellColor] using cellPointChart_apply H hH d x
  rw [hbase] at horbit
  rw [horbit]
  calc
    Set.range (fun y : mixturePoints a.1 ↦
        cellPointChart H hH ⟨a.1,a.2,y⟩) =
        Set.range (fun y : mixturePoints (cellColor H hH d) ↦
          BinaryS16FusionNaturalPointChart.assemble H hH
            ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩⟩) := by
      ext w
      constructor
      · rintro ⟨y,rfl⟩
        obtain ⟨y,rfl⟩ := e.surjective y
        refine ⟨y,?_⟩
        simpa only [d,a,e,cellColor] using
          (cellPointChart_apply H hH d y).symm
      · rintro ⟨y,rfl⟩
        refine ⟨e y,?_⟩
        simpa only [d,a,e,cellColor] using cellPointChart_apply H hH d y
    _ = Set.range (fun y : BinaryS16JointOrbitData.Points H hH q.1 ↦
          BinaryS16FusionNaturalPointChart.assemble H hH ⟨q,y⟩) := by
      ext w
      constructor
      · rintro ⟨y,rfl⟩
        exact ⟨BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩,rfl⟩
      · rintro ⟨y,rfl⟩
        obtain ⟨x,hx⟩ := slotChart_fixedCell_surjective H hH q c hunique y
        exact ⟨x,congrArg
          (fun z ↦ BinaryS16FusionNaturalPointChart.assemble H hH ⟨q,z⟩)
          hx⟩
    _ = q.1.orbit := assemble_block H hH q

/-! ## The five unrecorded certificate cases -/

/-- The critical action theorem in the raw-permutation form used by the
local orbit lemma. -/
theorem criticalAction_permutationTransitive (i : CriticalActionKind) :
    PermutationSubgroupTransitive (mixtureAction (.inl i)) := by
  change PermutationSubgroupTransitive (criticalActionSubgroup i)
  intro x y
  obtain ⟨g,hg⟩ := criticalAction_transitive i x y
  exact ⟨g,g.property,hg⟩

/-- The regular cyclic-four action used by the positive width-four route is
transitive on its literal four points. -/
theorem cyclicFour_transitive :
    PermutationSubgroupTransitive (mixtureAction (.inr none)) := by
  change ∀ x y : ZMod 4,
    ∃ u : Equiv.Perm (ZMod 4),
      u ∈ BinaryCarrierOriginalCyclicFourHall.cyclicFourAction.range ∧
        u x = y
  intro x y
  let a : Multiplicative (ZMod 4) := Multiplicative.ofAdd (y - x)
  refine ⟨BinaryCarrierOriginalCyclicFourHall.cyclicFourAction a,
    ⟨a,rfl⟩,?_⟩
  simp [BinaryCarrierOriginalCyclicFourHall.cyclicFourAction, a]


end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitCell

end
