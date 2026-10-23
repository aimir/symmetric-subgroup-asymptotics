import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoParameters

/-! Exact ray and polarization coordinates in the additive Hermitian
two-by-two carrier. Diagonal axes and normalized rank-one rays generate
the whole group. The same displayed polarization identity supplies the
first-entry and crossed off-diagonal equations for scalar-centroid
reconstruction, also in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
variable {K : Type*} [Field K]

def axis0 (sigma : K ≃+* K) (a : K) (ha : sigma a = a) : parameters sigma :=
  ⟨!![a, 0; 0, 0], by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Hermitian, Matrix.of_apply, ha]⟩

def axis1 (sigma : K ≃+* K) (a : K) (ha : sigma a = a) : parameters sigma :=
  ⟨!![0, 0; 0, a], by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Hermitian, Matrix.of_apply, ha]⟩

theorem norm_fixed (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a) (x : K) :
    sigma (x * sigma x) = x * sigma x := by
  rw [map_mul, hsigma]
  exact mul_comm _ _

def ray (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a) (x : K) : parameters sigma :=
  ⟨!![1, x; sigma x, x * sigma x], by
    intro i j
    fin_cases i <;> fin_cases j
    · exact map_one sigma
    · exact hsigma x
    · rfl
    · exact norm_fixed sigma hsigma x⟩

theorem ray_eq_rankOne (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a) (x : K) :
    (ray sigma hsigma x).val = rankOne sigma 1 ![1, sigma x] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ray, rankOne, Matrix.of_apply, hsigma, mul_comm]

theorem tracePair_fixed (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a) (x y : K) :
    sigma (x * sigma y + y * sigma x) = x * sigma y + y * sigma x := by
  rw [map_add, map_mul, map_mul, hsigma, hsigma]
  ring

theorem ray_polar (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a) (x y : K) :
    ray sigma hsigma (x + y) - ray sigma hsigma x - ray sigma hsigma y + ray sigma hsigma 0 =
      axis1 sigma (x * sigma y + y * sigma x) (tracePair_fixed sigma hsigma x y) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ray, axis1, Matrix.of_apply, map_add, map_zero] <;> ring

theorem ray_decomposition (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (A : parameters sigma) :
    A = axis0 sigma (A.val 0 0) (A.property 0 0) + ray sigma hsigma (A.val 0 1) -
      ray sigma hsigma 0 +
      axis1 sigma (A.val 1 1 - A.val 0 1 * sigma (A.val 0 1))
        (by rw [map_sub, A.property 1 1, norm_fixed sigma hsigma]) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [axis0, axis1, ray, Matrix.of_apply, map_zero]
  all_goals first | exact (A.property 1 0).symm | ring

theorem eq_top_of_axes_rays (sigma : K ≃+* K) (hsigma : ∀ a, sigma (sigma a) = a)
    (P : AddSubgroup (parameters sigma))
    (h0 : ∀ (a : K) (ha : sigma a = a), axis0 sigma a ha ∈ P)
    (h1 : ∀ (a : K) (ha : sigma a = a), axis1 sigma a ha ∈ P)
    (hray : ∀ x, ray sigma hsigma x ∈ P) : P = ⊤ := by
  apply top_unique
  intro A _
  rw [ray_decomposition sigma hsigma A]
  exact P.add_mem (P.sub_mem (P.add_mem (h0 _ _) (hray _)) (hray _)) (h1 _ _)

end SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoRankOne
