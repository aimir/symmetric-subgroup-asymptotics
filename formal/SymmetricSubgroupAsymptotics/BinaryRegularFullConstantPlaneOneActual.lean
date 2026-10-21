import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantOriginalCoordinateRows
import SymmetricSubgroupAsymptotics.BinaryPairCoordinateCentralCapacity
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! The selected plane capacity applies to the SAME original normal
subgroup and original pair kernel. Actual top-centre elements map
injectively to the two checked candidates; arbitrary outer offsets stay. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneOneActual
local instance planeOneActualFactPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev K := BinaryRegularFullConstantPlaneOne.K
abbrev A := BinaryRegularFullConstantPlaneOne.plane.space
private abbrev Allowed := {i : Fin 2 // ∀ j : Fin 12,
  BinaryRegularFullConstantPlaneOne.candidateAction i (K.inclusion (Pi.single j 1))-
    K.inclusion (Pi.single j 1)∈A}

theorem original_central_capacity_le
    {H : Subgroup (Equiv.Perm (Fin 16))} (E : BinaryPairFrame H (Fin 8))
    (hzero : H=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space) :
    binaryCentralJointDisplacementCapacity E.originalCoordinateRepresentation K.space A≤16 := by
  obtain ⟨u,hu⟩ := BinaryRegularFullConstantOriginalCoordinateRows.BinaryPairFrame.exists_actual_six_coordinate_rows
    E hzero hH hK
  let f : binaryFixedDisplacements E.originalCoordinateRepresentation K.space A →
      binaryCoordinateFixedDisplacements K BinaryRegularFullConstantPlaneOne.action A := fun v =>
    ⟨v.val,v.property.1,fun i => by rw [←hu];exact v.property.2 (u i)⟩
  have hf : Function.Injective f := by
    intro v z he
    exact Subtype.ext (congrArg
      (fun x : binaryCoordinateFixedDisplacements K BinaryRegularFullConstantPlaneOne.action A => x.val) he)
  have hfixed : Nat.card (binaryFixedDisplacements E.originalCoordinateRepresentation K.space A)≤16 :=
    (Nat.card_le_card_of_injective f hf).trans BinaryRegularFullConstantPlaneOne.fixed_card_le
  have hchoose (g : binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K.space A) :
      ∃ i : Fin 2,E.canonicalPointLabels.permCongrHom g.val.val=BinaryRegularFullConstantPlaneOne.candidate i := by
    rcases BinaryRegularFullConstantTopCenter.canonical_regular_center_cases E hzero hH hK g.val g.property.1 with
      he | he
    · exact ⟨0,he⟩
    · exact ⟨1,he⟩
  choose index hindex using hchoose
  let t : binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K.space A → Allowed := fun g =>
    ⟨index g,by
      intro j
      have he : E.originalCoordinateRepresentation g.val=BinaryRegularFullConstantPlaneOne.candidateAction (index g) := by
        rw [E.originalCoordinateRepresentation_canonical,hindex]
        rfl
      rw [←he]
      exact g.property.2 _ ⟨Pi.single j 1,rfl⟩⟩
  have ht : Function.Injective t := by
    intro g z he
    apply Subtype.ext
    apply Subtype.ext
    apply E.canonicalPointLabels.permCongrHom.injective
    have hi : index g=index z := congrArg (fun x : Allowed => x.val) he
    exact (hindex g).trans ((congrArg BinaryRegularFullConstantPlaneOne.candidate hi).trans (hindex z).symm)
  have htop : Nat.card (binaryCentralTrivialDisplacements E.originalCoordinateRepresentation K.space A)≤1 :=
    (Nat.card_le_card_of_injective t ht).trans BinaryRegularFullConstantPlaneOne.allowed_card_le
  exact (Nat.mul_le_mul hfixed htop).trans (by decide)

namespace BinaryPairFrame
variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : SymmetricSubgroupAsymptotics.BinaryPairFrame U (Fin 16))
    (E : SymmetricSubgroupAsymptotics.BinaryPairFrame F.top.range (Fin 8))
include F E

theorem original_normal_quotient_center_capacity_le
    (hzero : F.top.range=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=K.space)
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)
    (hA : (F.ambientAxis N).map E.originalCoordinateEquiv.toLinearMap≤A) :
    Nat.card N*Nat.card (Subgroup.center (U ⧸ N))≤16 := by
  have hwhole : F.ambientAxis F.top.ker=F.kernelSpace := by
    apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
    rintro v ⟨a,rfl⟩
    exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=K.space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    rwa [hwhole] at hS
  exact (F.kernel_center_card_mul_le_original_coordinate_central_capacity E N hN K.space A hspace hA).trans
    (original_central_capacity_le E hzero hH hK)

end BinaryPairFrame
end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneOneActual
