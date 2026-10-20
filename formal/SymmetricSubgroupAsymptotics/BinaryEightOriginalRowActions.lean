import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T3
import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T22
import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces
import SymmetricSubgroupAsymptotics.InvariantKernelSmallStabilizer

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions

abbrev regularH := Subgroup.closure (Set.range BinaryMenuCayley8T3.generators)
def regularRow (i : Fin 8) : regularH :=
  ⟨BinaryMenuCayley8T3.certificate.toCayley.elements i,
    (BinaryMenuCayley8T3.certificate.toCayley.mem_closure_iff _).mpr ⟨i, rfl⟩⟩
theorem regularRow_bijective : Function.Bijective regularRow := by
  constructor
  · intro i j h
    exact BinaryMenuCayley8T3.certificate.elements_injective BinaryMenuCayley8T3.rows_injective (congrArg Subtype.val h)
  · intro g
    obtain ⟨i, hi⟩ := (BinaryMenuCayley8T3.certificate.toCayley.mem_closure_iff (g : Equiv.Perm (Fin 8))).mp g.property
    exact ⟨i, Subtype.ext hi⟩
def regularRho : Representation (ZMod 2) regularH (Fin 8 → ZMod 2) := (binaryPermutationRepresentation 8).comp regularH.subtype
abbrev heisenbergH := Subgroup.closure (Set.range BinaryMenuCayley8T22.generators)
def heisenbergRow (i : Fin 32) : heisenbergH :=
  ⟨BinaryMenuCayley8T22.certificate.toCayley.elements i,
    (BinaryMenuCayley8T22.certificate.toCayley.mem_closure_iff _).mpr ⟨i, rfl⟩⟩
theorem heisenbergRow_bijective : Function.Bijective heisenbergRow := by
  constructor
  · intro i j h
    exact BinaryMenuCayley8T22.certificate.elements_injective BinaryMenuCayley8T22.rows_injective (congrArg Subtype.val h)
  · intro g
    obtain ⟨i, hi⟩ := (BinaryMenuCayley8T22.certificate.toCayley.mem_closure_iff (g : Equiv.Perm (Fin 8))).mp g.property
    exact ⟨i, Subtype.ext hi⟩
def heisenbergRho : Representation (ZMod 2) heisenbergH (Fin 8 → ZMod 2) := (binaryPermutationRepresentation 8).comp heisenbergH.subtype

end SymmetricSubgroupAsymptotics.BinaryEightOriginalRowActions
