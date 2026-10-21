import SymmetricSubgroupAsymptotics.BinaryRegularFullConstantPlaneOneActual
import Mathlib.Data.Finite.Card

/-! The selected top test kills the actual central top component, rather
than merely bounding its number of possible values. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegularFullConstantCentralTopTrivial
local instance fullConstantCentralTopTrivialPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
private abbrev Allowed := {i : Fin 2 // ∀ j : Fin 12,
  BinaryRegularFullConstantPlaneOne.candidateAction i
    (BinaryRegularFullConstantPlaneOne.K.inclusion (Pi.single j 1))-
      BinaryRegularFullConstantPlaneOne.K.inclusion (Pi.single j 1)∈
        BinaryRegularFullConstantPlaneOne.plane.space}
private theorem zero_allowed : ∀ j : Fin 12,
    BinaryRegularFullConstantPlaneOne.candidateAction 0
      (BinaryRegularFullConstantPlaneOne.K.inclusion (Pi.single j 1))-
        BinaryRegularFullConstantPlaneOne.K.inclusion (Pi.single j 1)∈
          BinaryRegularFullConstantPlaneOne.plane.space := by
  simp only [BinaryCoordinateSpace.mem_iff]
  decide +kernel
private theorem candidate_zero : BinaryRegularFullConstantPlaneOne.candidate 0=1 := by
  ext x
  revert x
  decide +kernel

theorem actual_central_top_eq_one
    {H : Subgroup (Equiv.Perm (Fin 16))} (E : BinaryPairFrame H (Fin 8))
    (hzero : H=E.splitAffineAction)
    (hH : E.top.range=Subgroup.closure (Set.range BinaryMenuCayley8T3.generators))
    (hK : E.kernelSpace=BinaryRegularSixCanonicalGenerators.K.space)
    (t : H) (ht : t∈Subgroup.center H)
    (hdisp : ∀ v,v∈BinaryRegularFullConstantPlaneOne.K.space →
      E.originalCoordinateRepresentation t v-v∈BinaryRegularFullConstantPlaneOne.plane.space) : t=1 := by
  have hchoose : ∃ i : Fin 2,E.canonicalPointLabels.permCongrHom t.val=
      BinaryRegularFullConstantPlaneOne.candidate i := by
    rcases BinaryRegularFullConstantTopCenter.canonical_regular_center_cases E hzero hH hK t ht with he|he
    · exact ⟨0,he⟩
    · exact ⟨1,he⟩
  obtain ⟨i,hi⟩ := hchoose
  have ha : ∀ j : Fin 12,
      BinaryRegularFullConstantPlaneOne.candidateAction i
        (BinaryRegularFullConstantPlaneOne.K.inclusion (Pi.single j 1))-
          BinaryRegularFullConstantPlaneOne.K.inclusion (Pi.single j 1)∈
            BinaryRegularFullConstantPlaneOne.plane.space := by
    intro j
    have he : E.originalCoordinateRepresentation t=BinaryRegularFullConstantPlaneOne.candidateAction i := by
      rw [E.originalCoordinateRepresentation_canonical,hi]
      rfl
    rw [←he]
    exact hdisp _ ⟨Pi.single j 1,rfl⟩
  letI : Subsingleton Allowed := Finite.card_le_one_iff_subsingleton.mp
    BinaryRegularFullConstantPlaneOne.allowed_card_le
  have hz : i=0 := congrArg (fun z : Allowed => z.val)
    (Subsingleton.elim (⟨i,ha⟩ : Allowed) ⟨0,zero_allowed⟩)
  apply Subtype.ext
  apply E.canonicalPointLabels.permCongrHom.injective
  change E.canonicalPointLabels.permCongrHom t.val=
    E.canonicalPointLabels.permCongrHom (1 : Equiv.Perm (Fin 16))
  rw [map_one]
  simpa only [hz,candidate_zero] using hi
end SymmetricSubgroupAsymptotics.BinaryRegularFullConstantCentralTopTrivial
