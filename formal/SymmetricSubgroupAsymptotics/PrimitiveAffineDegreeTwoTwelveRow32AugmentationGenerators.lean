import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.BinaryCoordinateRegistry
import SymmetricSubgroupAsymptotics.BinaryInvariantCyclicGeneratorBound
import SymmetricSubgroupAsymptotics.PermutationFunctionSelfDual
import Mathlib.Algebra.CharP.Two

/-!
# Two generators for row 32's literal three-block augmentation sum

The three four-point blocks are `[0,3,6,9]`, `[4,7,10,1]`, and
`[8,11,2,5]`; the third original generator cycles these displayed labels.
The two vectors supported at `{0,9}` and `{0,6}` generate the sum of the
three augmentation hyperplanes. Nine short original-group orbit sums
certify this, with no group or invariant-submodule enumeration.

This proves the critical numerator's generator bound. It does not yet
assert the uniform nonfixed bound for every row-32 subquotient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev Top := Row32Top
abbrev ModuleSpace := Fin 12 → ZMod 2

def ambient (i : Fin 3) : Top :=
  ⟨row32Generators i, Subgroup.subset_closure (Set.mem_range_self i)⟩

theorem ambient_full : Subgroup.closure (Set.range ambient) = ⊤ := by
  apply top_unique
  rintro ⟨x, hx⟩ htop
  clear htop
  induction hx using Subgroup.closure_induction with
  | mem y hy => obtain ⟨i, rfl⟩ := hy; exact Subgroup.subset_closure ⟨i, rfl⟩
  | one => exact Subgroup.one_mem _
  | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => exact Subgroup.inv_mem _ hx

def representation : Representation (ZMod 2) Top ModuleSpace :=
  permutationFunctionRepresentation (ZMod 2) Top (Fin 12)

/-- Original point labels, aligned by the actual cubic generator. -/
def point : Fin 3 → Fin 4 → Fin 12 :=
  ![![0, 3, 6, 9], ![4, 7, 10, 1], ![8, 11, 2, 5]]

theorem point_bijective : Function.Bijective (fun p : Fin 3 × Fin 4 ↦ point p.1 p.2) := by
  decide +kernel

def cycle : Equiv.Perm (Fin 3) where
  toFun := ![1, 2, 0]
  invFun := ![2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem cubic_point : ∀ i j, ambient 2 • point i j = point (cycle i) j := by
  decide +kernel

private abbrev projection9 (j : Fin 9) : (Fin 9 → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 9 ↦ ZMod 2) j

private abbrev projection12 (j : Fin 12) : ModuleSpace →ₗ[ZMod 2] ZMod 2 :=
  LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin 12 ↦ ZMod 2) j

private def inclusion : (Fin 9 → ZMod 2) →ₗ[ZMod 2] ModuleSpace :=
  LinearMap.pi (![
    projection9 0 + projection9 1 + projection9 2,
    projection9 5, projection9 7, projection9 0,
    projection9 3 + projection9 4 + projection9 5,
    projection9 8, projection9 1, projection9 3,
    projection9 6 + projection9 7 + projection9 8,
    projection9 2, projection9 4, projection9 6] :
    Fin 12 → ((Fin 9 → ZMod 2) →ₗ[ZMod 2] ZMod 2))

private def coordinates : ModuleSpace →ₗ[ZMod 2] (Fin 9 → ZMod 2) :=
  LinearMap.pi (![projection12 3, projection12 6, projection12 9,
    projection12 7, projection12 10, projection12 1,
    projection12 11, projection12 2, projection12 5] :
    Fin 9 → (ModuleSpace →ₗ[ZMod 2] ZMod 2))

def chart : BinaryCoordinateSpace 12 9 where
  inclusion := inclusion
  coordinates := coordinates
  left_inverse := by
    intro v
    funext i
    fin_cases i <;> rfl

private theorem binary_block_eq_iff (a b c d : ZMod 2) :
    b + c + d = a ↔ a + b + c + d = 0 := by
  rw [show a + b + c + d = a + (b + c + d) by ac_rfl, CharTwo.add_eq_zero]
  exact eq_comm

/-- The chart is exactly the sum of the three literal augmentation spaces. -/
theorem chart_mem_iff (v : ModuleSpace) : v ∈ chart.space ↔
    v 0 + v 3 + v 6 + v 9 = 0 ∧
    v 4 + v 7 + v 10 + v 1 = 0 ∧
    v 8 + v 11 + v 2 + v 5 = 0 := by
  rw [chart.mem_iff]
  constructor
  · intro h
    have h0 := congrFun h (0 : Fin 12)
    have h4 := congrFun h (4 : Fin 12)
    have h8 := congrFun h (8 : Fin 12)
    change v 3 + v 6 + v 9 = v 0 at h0
    change v 7 + v 10 + v 1 = v 4 at h4
    change v 11 + v 2 + v 5 = v 8 at h8
    exact ⟨(binary_block_eq_iff _ _ _ _).mp h0,
      (binary_block_eq_iff _ _ _ _).mp h4,
      (binary_block_eq_iff _ _ _ _).mp h8⟩
  · rintro ⟨h0, h4, h8⟩
    have h0' := (binary_block_eq_iff _ _ _ _).mpr h0
    have h4' := (binary_block_eq_iff _ _ _ _).mpr h4
    have h8' := (binary_block_eq_iff _ _ _ _).mpr h8
    funext i
    fin_cases i <;> dsimp [chart, inclusion, coordinates]
    all_goals first | rfl | exact h0' | exact h4' | exact h8'

private theorem positive : ∀ i j,
    representation (ambient i) (chart.inclusion (Pi.single j 1)) ∈ chart.space := by
  decide +kernel

private theorem negative : ∀ i j,
    representation (ambient i)⁻¹ (chart.inclusion (Pi.single j 1)) ∈ chart.space := by
  decide +kernel

/-- The original-top action on the actual nine-dimensional augmentation sum. -/
def augmentation : Subrepresentation representation :=
  chart.subrepresentationOfGenerators representation ambient ambient_full positive negative

theorem augmentation_space : augmentation.toSubmodule = chart.space := rfl

def seed : Fin 2 → ModuleSpace :=
  ![chart.inclusion (Pi.single 2 1), chart.inclusion (Pi.single 1 1)]

private def orbitTerms : Fin 9 → List (Top × Fin 2) := ![
  [(ambient 0, 1), (1, 0)], [(1, 1)], [(1, 0)],
  [(ambient 2 * ambient 0, 1), (ambient 2, 0)], [(ambient 2, 1)], [(ambient 2, 0)],
  [(ambient 2 ^ 2 * ambient 0, 1), (ambient 2 ^ 2, 0)],
  [(ambient 2 ^ 2, 1)], [(ambient 2 ^ 2, 0)]]

private theorem basis_eq : ∀ j, chart.inclusion (Pi.single j 1) =
    ((orbitTerms j).map (fun t ↦ representation t.1 (seed t.2))).sum := by
  decide +kernel

/-- Nine checked sparse identities establish the full orbit-span equality. -/
theorem augmentation_eq_seed_orbits : augmentation.toSubmodule =
    ⨆ i, binaryOrbitSpan representation (seed i) := by
  apply le_antisymm
  · change chart.space ≤ _
    apply chart.le_of_basis_mem
    intro j
    rw [basis_eq j]
    apply list_sum_mem
    intro v hv
    obtain ⟨t, _ht, rfl⟩ := List.mem_map.mp hv
    exact (le_iSup (fun i ↦ binaryOrbitSpan representation (seed i)) t.2)
      (Submodule.subset_span ⟨t.1, rfl⟩)
  · apply iSup_le
    intro i
    apply binaryOrbitSpan_le representation augmentation
    change seed i ∈ chart.space
    fin_cases i <;> exact ⟨_, rfl⟩

theorem augmentation_generated_two :
    RepresentationGeneratedBy augmentation.toRepresentation 2 :=
  representationGeneratedBy_of_iSup_binaryOrbitSpan
    representation augmentation 2 seed augmentation_eq_seed_orbits

/-- This bound applies to any target representation, and therefore to the
actual C₃ type once it occurs as the head target in the structural argument. -/
theorem augmentation_hom_finrank_le_two_mul
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (sigma : Representation (ZMod 2) Top W) :
    Module.finrank (ZMod 2) (augmentation.toRepresentation.IntertwiningMap sigma) ≤
      2 * Module.finrank (ZMod 2) W := by
  obtain ⟨v, hv⟩ := augmentation_generated_two
  rw [(Representation.IntertwiningMap.equivLinearMapAsModule
    augmentation.toRepresentation sigma).finrank_eq]
  have h := moduleHom_finrank_le_generators (k := ZMod 2) (R := (ZMod 2)[Top])
    (M := augmentation.toRepresentation.asModule) (A := sigma.asModule) v hv
  simpa only [Fintype.card_fin, sigma.asModuleEquiv.finrank_eq] using h

end PrimitiveAffineDegreeTwoTwelveRow32AugmentationGenerators
end SymmetricSubgroupAsymptotics

end
