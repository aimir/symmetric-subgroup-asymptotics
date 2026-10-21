import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule
import SymmetricSubgroupAsymptotics.BinaryPairOriginalCoordinateRepresentation
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces

/-! A reversible original-coordinate chart counts the same actual pair
kernel. No original source/action enumeration is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w r d : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w)) (E : BinaryPairFrame F.top.range (Fin r))
include F E

omit E in
theorem original_ambientAxis_kernel : F.ambientAxis F.top.ker=F.kernelSpace := by
  apply le_antisymm (F.ambientAxis_le_kernelSpace F.top.ker)
  rintro v ⟨a,rfl⟩
  exact (F.bits_mem_ambientAxis F.top.ker a.toMul).mpr a.toMul.property

theorem kernelSpace_card_of_original_coordinate_state
    (C : BinaryCoordinateSpace (r+r) d)
    (hS : (E.originalCoordinateSubrepresentation (F.axisNaturalSubrepresentation F.top.ker)).toSubmodule=C.space) :
    Nat.card F.kernelSpace=2^d := by
  have hspace : F.kernelSpace.map E.originalCoordinateEquiv.toLinearMap=C.space := by
    change (F.ambientAxis F.top.ker).map E.originalCoordinateEquiv.toLinearMap=_ at hS
    simpa only [F.original_ambientAxis_kernel] using hS
  have he := Nat.card_congr (E.originalCoordinateEquiv.submoduleMap F.kernelSpace).toEquiv
  rw [hspace,C.card] at he
  exact he
end SymmetricSubgroupAsymptotics.BinaryPairFrame
