import SymmetricSubgroupAsymptotics.BinaryCoordinateSpaces

/-! The generic linear step stays opaque when applied to large literal
operators; only displayed coordinate-basis displacements are needed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem binaryCoordinate_displacement_mem_of_basis
    {w d : ℕ} (C : BinaryCoordinateSpace w d)
    (L : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))
    (R : Submodule (ZMod 2) (Fin w → ZMod 2))
    (hbasis : ∀ j,L (C.inclusion (Pi.single j 1))-C.inclusion (Pi.single j 1)∈R)
    (v : Fin w → ZMod 2) (hv : v∈C.space) : L v-v∈R := by
  have hle : C.space≤R.comap (L-LinearMap.id) := C.le_of_basis_mem _ hbasis
  have hm := hle hv
  change (L-(LinearMap.id : (Fin w → ZMod 2) →ₗ[ZMod 2] (Fin w → ZMod 2))) v∈R at hm
  simpa only [LinearMap.sub_apply,LinearMap.id_apply] using hm
end SymmetricSubgroupAsymptotics
