import SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.GroupTheory.NoncommCoprod

/-! The actual central determinant split in GL3(F3). In particular the
simple normal determinant kernel may coexist with a central involution;
no unique-minimal-normal claim is made. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups

local instance standardCentralDetPrimeThree : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev determinantThree : GeneralThree 3 →* (ZMod 3)ˣ := Matrix.GeneralLinearGroup.det
abbrev determinantKernelThree : Subgroup (GeneralThree 3) := determinantThree.ker
abbrev scalarThree : (ZMod 3)ˣ →* GeneralThree 3 := Matrix.GeneralLinearGroup.scalar (Fin 3)

theorem scalarThree_det (u : (ZMod 3)ˣ) : determinantThree (scalarThree u) = u := by
  simpa only [determinantThree, scalarThree, Matrix.GeneralLinearGroup.det_scalar,
    Fintype.card_fin] using units_three_cube u

theorem scalarThree_central (u : (ZMod 3)ˣ) : scalarThree u ∈ Subgroup.center (GeneralThree 3) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

theorem determinantThree_surjective : Function.Surjective determinantThree :=
  fun u => ⟨scalarThree u, scalarThree_det u⟩

/-- Multiply the actual determinant-one matrix by its actual scalar factor. -/
def determinantProduct : determinantKernelThree × (ZMod 3)ˣ →* GeneralThree 3 :=
  determinantKernelThree.subtype.noncommCoprod scalarThree (fun k u =>
    Subgroup.mem_center_iff.mp (scalarThree_central u) k.val)

theorem determinantProduct_injective : Function.Injective determinantProduct := by
  rintro ⟨x, u⟩ ⟨y, v⟩ h
  have hu : u = v := by
    have hd := congrArg determinantThree h
    change determinantThree (x.val * scalarThree u) =
      determinantThree (y.val * scalarThree v) at hd
    rw [map_mul, map_mul, scalarThree_det, scalarThree_det] at hd
    have hx : determinantThree x.val = 1 := x.property
    have hy : determinantThree y.val = 1 := y.property
    simpa only [hx, hy, one_mul] using hd
  subst v
  apply Prod.ext
  · apply Subtype.ext
    change x.val * scalarThree u = y.val * scalarThree u at h
    exact mul_right_cancel h
  · rfl

theorem determinantProduct_surjective : Function.Surjective determinantProduct := by
  intro g
  let k : determinantKernelThree := ⟨g * (scalarThree (determinantThree g))⁻¹, by
    change determinantThree (g * (scalarThree (determinantThree g))⁻¹) = 1
    rw [map_mul, map_inv, scalarThree_det, mul_inv_cancel]⟩
  refine ⟨(k, determinantThree g), ?_⟩
  change (g * (scalarThree (determinantThree g))⁻¹) *
    scalarThree (determinantThree g) = g
  simp only [inv_mul_cancel_right]

/-- A genuine central direct product, retaining the original matrix map. -/
def determinantProductEquiv : determinantKernelThree × (ZMod 3)ˣ ≃* GeneralThree 3 :=
  MulEquiv.ofBijective determinantProduct
    ⟨determinantProduct_injective, determinantProduct_surjective⟩

theorem card_units_three : Nat.card (ZMod 3)ˣ = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_determinantKernelThree : Nat.card determinantKernelThree = 5616 := by
  have h := Nat.card_congr determinantProductEquiv.toEquiv
  rw [Nat.card_prod, card_units_three, card_GL_three] at h
  omega

theorem card_SL_three : Nat.card (SpecialThree 3) = 5616 := by
  rw [Nat.card_congr (specialLinearKerEquiv 3).toEquiv]
  exact card_determinantKernelThree

theorem simple_determinantKernelThree (h : PublishedSimplicity) :
    IsSimpleGroup determinantKernelThree := by
  letI : IsSimpleGroup (SpecialThree 3) := simple_SL_three h
  exact (specialLinearKerEquiv 3).symm.isSimpleGroup

theorem card_determinant_quotient : Nat.card (GeneralThree 3 ⧸ determinantKernelThree) = 2 := by
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    determinantThree determinantThree_surjective).toEquiv]
  exact card_units_three

end SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
