import SymmetricSubgroupAsymptotics.BinaryEightTop31CoordinateAction
import SymmetricSubgroupAsymptotics.BinaryRegularEightNaturalRegistryCharts
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry

/-! A selected proper-F template under the literal31 top. Its five-
dimensional layer and four-dimensional commutator envelope are certified
on actual original generators/rows. The central flip is an explicit
DERIVED word, which later justifies its zero-offset original lift. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.BinaryEightTop31ProperFLinear
open BinaryEightTop31CoordinateAction
open BinaryRegularEightNaturalRegistry (chart9 chart37 chart45)

def centralWord : DerivedGeneratorWord (Fin 3) :=
  .mul (.comm 1 0) (.conj 2 (.comm 1 0))
def z : H := centralWord.eval generators

theorem z_derived : z ∈ commutator H := centralWord.eval_mem_commutator generators
private theorem z_points : ∀ i : Fin 8,
    (z : Equiv.Perm (Fin 8)) i = BinaryMenuCayley8T3.generators 2 i := by
  decide +kernel
theorem z_coe : (z : Equiv.Perm (Fin 8)) = BinaryMenuCayley8T3.generators 2 :=
  Equiv.ext z_points
private theorem z_commutes_rows : ∀ r : Fin 64, z * row r = row r * z := by
  intro r
  apply Subtype.ext
  revert r
  decide +kernel
theorem z_central : z ∈ Subgroup.center H := by
  apply Subgroup.mem_center_iff.mpr
  intro t
  obtain ⟨r,rfl⟩ := rowEquiv.surjective t
  exact (z_commutes_rows r).symm

private theorem envelope_positive : ∀ (g : Fin 3) j,
    rho (generators g) (chart9.inclusion (Pi.single j 1)) ∈ chart9.space := by
  decide +kernel
private theorem envelope_negative : ∀ (g : Fin 3) j,
    rho (generators g)⁻¹ (chart9.inclusion (Pi.single j 1)) ∈ chart9.space := by
  decide +kernel

def envelope : Subrepresentation rho := chart9.subrepresentationOfGenerators
  rho generators (closureGenerators_full _) envelope_positive envelope_negative

private theorem layer_displacement_basis : ∀ (r : Fin 64) j,
    rho (row r) (chart37.inclusion (Pi.single j 1)) -
      chart37.inclusion (Pi.single j 1) ∈ chart9.space := by
  decide +kernel

theorem layer_displacement (r : H) (v : V) (hv : v ∈ chart37.space) :
    rho r v-v ∈ chart9.space := by
  obtain ⟨i,rfl⟩ := rowEquiv.surjective r
  let d : V →ₗ[ZMod 2] V := rho (row i) - LinearMap.id
  exact (chart37.le_of_basis_mem (chart9.space.comap d)
    (layer_displacement_basis i)) hv

private theorem envelope_in_layer_basis : ∀ j : Fin 4,
    chart9.inclusion (Pi.single j 1) ∈ chart37.space := by decide +kernel
theorem envelope_le_layer : chart9.space ≤ chart37.space :=
  chart9.le_of_basis_mem _ envelope_in_layer_basis

private theorem flip_displacement_points : ∀ v : V, rho z v-v ∈ chart9.space := by
  decide +kernel
theorem flip_displacement (v : V) : rho z v-v ∈ chart9.space :=
  flip_displacement_points v

private theorem faithful_rows : ∀ r : Fin 64,
    (∀ j : Fin 5, rho (row r) (chart37.inclusion (Pi.single j 1)) =
      chart37.inclusion (Pi.single j 1)) → (row r : Equiv.Perm (Fin 8)) = 1 := by
  decide +kernel

theorem layer_faithful (r : H)
    (hr : ∀ v, v ∈ chart37.space → rho r v = v) : r = 1 := by
  obtain ⟨i,rfl⟩ := rowEquiv.surjective r
  apply Subtype.ext
  apply faithful_rows i
  intro j
  exact hr _ ⟨_,rfl⟩

/-- The full original augmentation kernel has exactly the pair-constant
space fixed by the selected central flip. -/
theorem flip_fixed_kernel : ∀ v : V,
    v ∈ chart45.space → (rho z v = v ↔ v ∈ chart9.space) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.BinaryEightTop31ProperFLinear
