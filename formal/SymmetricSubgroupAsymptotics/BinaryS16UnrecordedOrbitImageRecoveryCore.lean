import SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageAccessor

/-!
# Turning a one-cell image computation into a source-orbit image theorem

The image accessor computes the restriction of the physical target on a
one-cell block in its routed mixture chart.  This small wrapper is the common
last step used by all five unrecorded certificate branches: once that routed
chart is identified with the exact source chart, the target restriction is
literally the original source restriction image.
-/

set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageRecoveryCore

open SymmetricSubgroupAsymptotics
open BinaryCarrierProfileTransport
open BinaryS16UnrecordedOrbitCell
open BinaryS16UnrecordedOrbitImageAccessor

variable {N : ℕ}
variable (H : Subgroup (Equiv.Perm (Fin (2 * N))))
variable (hH : BinaryS16CanonicalCarrierProfile.ResidualSector H)

/-- A one-cell routed block whose displayed chart is an exact source chart
has the same complete restriction image in the physical target and in the
source subgroup.  The equality of point sets is retained explicitly, so the
statement is ready for cross-subgroup reconstruction. -/
theorem targetOrbitImage_eq_sourceOrbitImage_of_uniqueCell
    {G : Subgroup (Equiv.Perm (Fin (2 * N)))}
    (hG : OrbitProfileFullOn mixtureAction
      (BinaryS16FusionNaturalPointChart.pointChart H hH) G)
    (q : Occurrence H hH) (c : (RouteSlot H hH q).Cells)
    (hunique : ∀ d : (RouteSlot H hH q).Cells, d = c)
    (htrans : PermutationSubgroupTransitive
      (mixtureAction ((RouteSlot H hH q).color c)))
    (e : mixturePoints ((RouteSlot H hH q).color c) ≃ q.1.orbit)
    (he : relabelSubgroup e
        (mixtureAction ((RouteSlot H hH q).color c)) =
      OrbitProfileFromOrbits.orbitImage H q.1)
    (hpoint : ∀ y,
      ((e y : q.1.orbit) : Fin (2 * N)) =
        BinaryS16FusionNaturalPointChart.assemble H hH
          ⟨q,BinaryS16FusionNaturalPointChart.slotChart H hH q ⟨c,y⟩⟩) :
    ∃ p : OrbitProfileFromOrbits.Orbit G, ∃ hp : p.orbit = q.1.orbit,
      relabelSubgroup (Equiv.setCongr hp)
          (OrbitProfileFromOrbits.orbitImage G p) =
        OrbitProfileFromOrbits.orbitImage H q.1 := by
  obtain ⟨z,hz,chart,himage,hchart⟩ :=
    targetOrbitImage_eq_sourceBlockAction_of_uniqueCell
      H hH hG q c hunique htrans
  have hchartEq : chart = e := by
    apply Equiv.ext
    intro y
    apply Subtype.ext
    exact (hchart y).trans (hpoint y).symm
  refine ⟨Quotient.mk'' z,hz,?_⟩
  subst chart
  exact himage.trans he

end SymmetricSubgroupAsymptotics.BinaryS16UnrecordedOrbitImageRecoveryCore

end
