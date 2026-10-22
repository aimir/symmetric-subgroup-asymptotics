import SymmetricSubgroupAsymptotics.CFSGMatrixFlagSubgroups
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! A complete flag is intrinsic to an actual unipotent action once
its original sparse words test every upper entry. This generic engine
is discharged by concrete C roots in its application. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer
variable {I : Type*} [Fintype I] [DecidableEq I] {K : Type*} [Field K]
variable {G : Type*} [Group G] {m : ℕ}

def flagPrefix (e : I ≃ Fin m) (k : ℕ) : Submodule K (I → K) where
  carrier := {v | ∀ i, k ≤ (e i).val → v i = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := by intro v w hv hw i hi; simp only [Pi.add_apply, hv i hi, hw i hi, add_zero]
  smul_mem' := by intro a v hv i hi; simp only [Pi.smul_apply, hv i hi, smul_zero]

variable (e : I ≃ Fin m) (rho : G →* Matrix I I K) (U : Subgroup G)
variable (hupper : ∀ u ∈ U, (rho u).BlockTriangular e)
variable (hdiag : ∀ u ∈ U, ∀ i, rho u i i = 1)
variable (htest : ∀ i j, e i < e j → ∃ u ∈ U, ∀ v : I → K, (rho u *ᵥ v - v) i = v j)

include hupper hdiag htest

theorem mem_flagPrefix_succ_iff (k : ℕ) (v : I → K) :
    v ∈ flagPrefix (K := K) e (k + 1) ↔
      ∀ u ∈ U, rho u *ᵥ v - v ∈ flagPrefix (K := K) e k := by
  constructor
  · intro hv u hu i hi
    have he : (rho u *ᵥ v) i = v i := by
      change (∑ j, rho u i j * v j) = v i
      calc
        _ = rho u i i * v i := by
          apply Finset.sum_eq_single i
          · intro j _ hji
            have hne : e j ≠ e i := e.injective.ne hji
            rcases lt_or_gt_of_ne hne with hj | hj
            · rw [hupper u hu hj, zero_mul]
            · have hz : v j = 0 := hv j (by have hi' : k ≤ (e i).val := hi; change (e i).val < (e j).val at hj; omega)
              rw [hz, mul_zero]
          · intro hni
            exact False.elim (hni (Finset.mem_univ i))
        _ = v i := by rw [hdiag u hu i, one_mul]
    change (rho u *ᵥ v) i - v i = 0
    rw [he, sub_self]
  · intro hv j hj
    have hk : k < m := by have hlt := (e j).isLt; omega
    let i : I := e.symm ⟨k, hk⟩
    have hei : e i = ⟨k, hk⟩ := e.apply_symm_apply _
    have hij : e i < e j := by rw [hei]; change k < (e j).val; omega
    obtain ⟨u, hu, hmove⟩ := htest i j hij
    have h := hv u hu i (by rw [hei])
    rw [hmove] at h
    exact h

theorem normalizer_preserves_flagPrefix (A : G) (hA : A ∈ Subgroup.normalizer (U : Set G)) :
    ∀ k (v : I → K), v ∈ flagPrefix (K := K) e k → rho A *ᵥ v ∈ flagPrefix (K := K) e k := by
  intro k
  induction k with
  | zero =>
    intro v hv
    have hz : v = 0 := funext fun i => hv i (Nat.zero_le _)
    rw [hz, Matrix.mulVec_zero]
    exact (flagPrefix (K := K) e 0).zero_mem
  | succ k ih =>
    intro v hv
    apply (mem_flagPrefix_succ_iff e rho U hupper hdiag htest k _).mpr
    intro u hu
    have hconj : A⁻¹ * u * A ∈ U := (Subgroup.mem_normalizer_iff''.mp hA u).mp hu
    have hm := (mem_flagPrefix_succ_iff e rho U hupper hdiag htest k v).mp hv (A⁻¹ * u * A) hconj
    have h := ih (rho (A⁻¹ * u * A) *ᵥ v - v) hm
    have he : A * (A⁻¹ * u * A) = u * A := by simp only [← mul_assoc, mul_inv_cancel, one_mul]
    have hact : rho A *ᵥ (rho (A⁻¹ * u * A) *ᵥ v) = rho u *ᵥ (rho A *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, ← map_mul, he, map_mul, ← Matrix.mulVec_mulVec]
    simpa only [Matrix.mulVec_sub, hact] using h

theorem normalizer_upper (A : G) (hA : A ∈ Subgroup.normalizer (U : Set G)) :
    (rho A).BlockTriangular e := by
  intro i j hij
  have hv : Pi.single j (1 : K) ∈ flagPrefix (K := K) e ((e j).val + 1) := by
    intro k hk
    have hkj : k ≠ j := by intro he; subst k; omega
    exact Pi.single_eq_of_ne hkj 1
  have h := normalizer_preserves_flagPrefix e rho U hupper hdiag htest A hA
    ((e j).val + 1) (Pi.single j 1) hv i (by change (e j).val < (e i).val at hij; omega)
  change (rho A *ᵥ Pi.single j 1) i = 0 at h
  rw [Matrix.mulVec_single_one] at h
  exact h

end SymmetricSubgroupAsymptotics.CFSGMatrixFlagNormalizer
