import SymmetricSubgroupAsymptotics.BinaryEightTop31ProperFLinear

/-! The enlarged selected kernel cut for the constant-line denominator.
Its mixed commutator envelope is the actual five-dimensional layer,
while the original lift offsets remain unrestricted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31ProperF26Linear
open BinaryEightTop31CoordinateAction
open BinaryRegularEightNaturalRegistry (chart26 chart37 chart45)
private theorem positive : ∀ (g : Fin 3) j,
    rho (generators g) (chart37.inclusion (Pi.single j 1)) ∈ chart37.space := by decide +kernel
private theorem negative : ∀ (g : Fin 3) j,
    rho (generators g)⁻¹ (chart37.inclusion (Pi.single j 1)) ∈ chart37.space := by decide +kernel

def envelope : Subrepresentation rho := chart37.subrepresentationOfGenerators
  rho generators (closureGenerators_full _) positive negative
private theorem displacement_basis : ∀ (r : Fin 64) j,
    rho (row r) (chart26.inclusion (Pi.single j 1))-
      chart26.inclusion (Pi.single j 1) ∈ chart37.space := by decide +kernel

theorem layer_displacement (r : H) (v : V) (hv : v ∈ chart26.space) :
    rho r v-v ∈ chart37.space := by
  obtain ⟨i,rfl⟩ := rowEquiv.surjective r
  let d : V →ₗ[ZMod 2] V := rho (row i)-LinearMap.id
  exact (chart26.le_of_basis_mem (chart37.space.comap d) (displacement_basis i)) hv

theorem envelope_le_layer : chart37.space ≤ chart26.space :=
  chart37.le_of_basis_mem _ (by decide +kernel)
theorem layer_le_kernel : chart26.space ≤ chart45.space :=
  chart26.le_of_basis_mem _ (by decide +kernel)
theorem flip_displacement (v : V) :
    rho BinaryEightTop31ProperFLinear.z v-v ∈ chart37.space :=
  BinaryEightTop31ProperFLinear.envelope_le_layer
    (BinaryEightTop31ProperFLinear.flip_displacement v)
end SymmetricSubgroupAsymptotics.BinaryEightTop31ProperF26Linear
