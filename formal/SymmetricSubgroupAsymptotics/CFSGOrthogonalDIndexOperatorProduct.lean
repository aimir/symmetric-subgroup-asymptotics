import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
import SymmetricSubgroupAsymptotics.CFSGSkewDisjointRangeRank

/-! Characteristic-free operator facts for the intrinsic root-product
test. Commutation and disjoint images kill the mixed product directly;
no factor two is cancelled. The existing skew-range rank theorem is
reused unchanged. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOperatorProduct
open CFSGAlternatingPairOperator
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pairOperator_skew (B : LinearMap.BilinForm K V)
    (hs : ∀ x y, B x y = B y x) (u v x y : V) :
    B (pairOperator B u v x) y = -B x (pairOperator B u v y) := by
  simp only [pairOperator_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hs x u, hs x v]
  ring

theorem smul_pairOperator_skew (B : LinearMap.BilinForm K V)
    (hs : ∀ x y, B x y = B y x) (a : K) (u v x y : V) :
    B ((a • pairOperator B u v) x) y = -B x ((a • pairOperator B u v) y) := by
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [pairOperator_skew B hs]
  ring

theorem commuting_disjoint_ranges_comp_zero (A C : V →ₗ[K] V)
    (hc : A.comp C = C.comp A)
    (hd : Disjoint (LinearMap.range A) (LinearMap.range C)) : A.comp C = 0 := by
  apply LinearMap.ext
  intro x
  change A (C x) = 0
  apply hd.le_bot
  refine ⟨⟨C x, rfl⟩, ⟨A x, ?_⟩⟩
  exact (LinearMap.congr_fun hc x).symm

theorem id_add_comp_sub_id_of_comp_zero (A C : V →ₗ[K] V)
    (hz : A.comp C = 0) :
    ((LinearMap.id : V →ₗ[K] V) + A).comp ((LinearMap.id : V →ₗ[K] V) + C) -
      (LinearMap.id : V →ₗ[K] V) = A + C := by
  change ((1 + A) * (1 + C) - 1 : Module.End K V) = A + C
  change A * C = 0 at hz
  simp only [add_mul, mul_add, one_mul, mul_one, hz, add_zero]
  abel

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexOperatorProduct
