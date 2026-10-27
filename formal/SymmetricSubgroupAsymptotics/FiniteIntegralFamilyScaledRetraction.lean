import SymmetricSubgroupAsymptotics.FiniteIntegralFamilySplitRealization

/-! A finite actual integral spanning family with coordinates scaled by
an integer d gives a genuine retraction up to d. Scalar extension is
injective whenever d becomes invertible. In particular d=2 suffices for
odd-characteristic B/D realizations; source spanning and coordinates
remain explicit, proved inputs of this generic algebraic lemma. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
namespace SymmetricSubgroupAsymptotics.FiniteIntegralFamilyScaledRetraction
variable {J M N : Type*} [Fintype J] [DecidableEq J]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M →ₗ[ℤ] N) (v : J → M) (c : N →ₗ[ℤ] (J → ℤ)) (d : ℤ)

def retraction : N →ₗ[ℤ] M := (Fintype.linearCombination ℤ v).comp c

theorem coordinates_combination
    (hcoord : ∀ j, c (f (v j)) = d • Pi.single j 1) (a : J → ℤ) :
    c (f (Fintype.linearCombination ℤ v a)) = d • a := by
  rw [Fintype.linearCombination_apply]
  simp only [map_sum, map_smulₛₗ, RingHom.id_apply, hcoord]
  funext j
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

theorem retraction_spec (hspan : Submodule.span ℤ (Set.range v) = ⊤)
    (hcoord : ∀ j, c (f (v j)) = d • Pi.single j 1) (x : M) :
    retraction v c (f x) = d • x := by
  obtain ⟨a, ha⟩ := FiniteIntegralFamilySplitRealization.combination_surjective v hspan x
  have ha' : Fintype.linearCombination ℤ v a = x := ha
  rw [← ha']
  change Fintype.linearCombination ℤ v
    (c (f (Fintype.linearCombination ℤ v a))) = d • _
  rw [coordinates_combination f v c d hcoord]
  exact (Fintype.linearCombination ℤ v).toAddMonoidHom.map_zsmul d a

theorem retraction_comp (hspan : Submodule.span ℤ (Set.range v) = ⊤)
    (hcoord : ∀ j, c (f (v j)) = d • Pi.single j 1) :
    (retraction v c).comp f = d • LinearMap.id :=
  LinearMap.ext (retraction_spec f v c d hspan hcoord)

theorem baseChange_retraction_spec (hspan : Submodule.span ℤ (Set.range v) = ⊤)
    (hcoord : ∀ j, c (f (v j)) = d • Pi.single j 1)
    (K : Type*) [CommRing K] (x : K ⊗[ℤ] M) :
    (retraction v c).baseChange K (f.baseChange K x) = d • x := by
  have h := congrArg (fun F : M →ₗ[ℤ] M => F.baseChange K)
    (retraction_comp f v c d hspan hcoord)
  change ((retraction v c).comp f).baseChange K =
    (d • (LinearMap.id : M →ₗ[ℤ] M)).baseChange K at h
  let bc : (M →ₗ[ℤ] M) →+ (K ⊗[ℤ] M →ₗ[K] K ⊗[ℤ] M) :=
    { toFun := fun F => F.baseChange K
      map_zero' := by exact LinearMap.baseChange_zero
      map_add' := fun F G => LinearMap.baseChange_add F G }
  have hs := bc.map_zsmul d (LinearMap.id : M →ₗ[ℤ] M)
  change (d • (LinearMap.id : M →ₗ[ℤ] M)).baseChange K =
    d • (LinearMap.id : M →ₗ[ℤ] M).baseChange K at hs
  rw [LinearMap.baseChange_id] at hs
  rw [LinearMap.baseChange_comp, hs] at h
  exact LinearMap.congr_fun h x

theorem baseChange_injective (hspan : Submodule.span ℤ (Set.range v) = ⊤)
    (hcoord : ∀ j, c (f (v j)) = d • Pi.single j 1)
    (K : Type*) [Field K] (hd : (d : K) ≠ 0) :
    Function.Injective (f.baseChange K) := by
  have hleft : Function.LeftInverse
      (fun y => (d : K)⁻¹ • (retraction v c).baseChange K y) (f.baseChange K) := by
    intro x
    change (d : K)⁻¹ • (retraction v c).baseChange K (f.baseChange K x) = x
    rw [baseChange_retraction_spec f v c d hspan hcoord]
    rw [← Int.cast_smul_eq_zsmul K]
    simp only [smul_smul, inv_mul_cancel₀ hd, one_smul]
  exact hleft.injective

end SymmetricSubgroupAsymptotics.FiniteIntegralFamilyScaledRetraction
