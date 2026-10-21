import SymmetricSubgroupAsymptotics.BinaryMenuCayley8T31
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryData

/-! The same literal8T31 action, retaining its certified64 permutation
rows and original generators. No action or module classification is added. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31CoordinateAction

abbrev H := Subgroup.closure (Set.range BinaryMenuCayley8T31.generators)
abbrev V := Fin 8 → ZMod 2
def generators : Fin 3 → H := closureGenerators BinaryMenuCayley8T31.generators
def rho : Representation (ZMod 2) H V := (binaryPermutationRepresentation 8).comp H.subtype

def row (i : Fin 64) : H :=
  ⟨BinaryMenuCayley8T31.certificate.toCayley.elements i,
    (BinaryMenuCayley8T31.certificate.toCayley.mem_closure_iff _).mpr ⟨i, rfl⟩⟩

def rowEquiv : Fin 64 ≃ H := Equiv.ofBijective row (by
  constructor
  · intro i j h
    exact BinaryMenuCayley8T31.certificate.elements_injective
      BinaryMenuCayley8T31.rows_injective (congrArg Subtype.val h)
  · intro g
    obtain ⟨i, hi⟩ :=
      (BinaryMenuCayley8T31.certificate.toCayley.mem_closure_iff g.val).mp g.property
    exact ⟨i, Subtype.ext hi⟩)

end SymmetricSubgroupAsymptotics.BinaryEightTop31CoordinateAction
