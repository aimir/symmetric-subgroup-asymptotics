import SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator

/-! Skew pair operators and literal mixed-zero products control
orthogonality of their actual image subspaces. No incidence or polar
recognition theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem pairOperator_skew (B : LinearMap.BilinForm K V)
    (hs : ∀ x y, B x y = B y x) (u v x y : V) :
    B (pairOperator B u v x) y = -B x (pairOperator B u v y) := by
  simp only [pairOperator_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [hs x u, hs x v]
  ring

theorem mixed_zero_orthogonal_ranges (B : LinearMap.BilinForm K V) (A C : V →ₗ[K] V)
    (hskew : ∀ x y, B (A x) y = -B x (A y)) (hzero : A.comp C = 0)
    (u : V) (hu : u ∈ LinearMap.range A) (v : V) (hv : v ∈ LinearMap.range C) :
    B u v = 0 := by
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨y, rfl⟩ := hv
  have hz : A (C y) = 0 := LinearMap.congr_fun hzero y
  rw [hskew, hz, map_zero, neg_zero]

end SymmetricSubgroupAsymptotics.CFSGAlternatingPairOperator
