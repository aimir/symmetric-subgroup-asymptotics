import SymmetricSubgroupAsymptotics.CFSGOrthogonalBFlipProduct
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBGenerationMonomialShortAction

/-! The actual product of B-coordinate flips is a monomial unit. Its
middle weight is retained, including the sign needed by the quadratic
short-root coefficient. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
open CFSGOrthogonalBSerreMatrices CFSGTypeAMonomialMatrices
open CFSGOrthogonalBGenerationShortArrays CFSGOrthogonalBGenerationMonomialShortAction
variable (K : Type) [Field K]

def oppositionPermutation (r : ℕ) : Equiv.Perm (Index (r+1)) :=
  Equiv.sumCongr (Equiv.sumComm (Fin (r+1)) (Fin (r+1))) (Equiv.refl Unit)

def oppositionWeight (r : ℕ) : Index (r+1) → K :=
  Sum.elim (fun _ => -1) (fun _ => (-1)^(r+1))

@[simp] theorem oppositionWeight_square (r : ℕ) (x : Index (r+1)) :
    oppositionWeight K r x * oppositionWeight K r x = 1 := by
  cases x with
  | inl b => simp [oppositionWeight]
  | inr b =>
    simp only [oppositionWeight, Sum.elim_inr]
    rw [← mul_pow]
    simp

theorem oppositionWeight_ne_zero (r : ℕ) (x : Index (r+1)) :
    oppositionWeight K r x ≠ 0 := by
  intro h
  have hh := oppositionWeight_square K r x
  rw [h, zero_mul] at hh
  exact zero_ne_one hh

theorem opposition_monomial (r : ℕ) :
    ((opposition K r).val : Mat K (r+1)) =
      monomial (oppositionPermutation r) (oppositionWeight K r) := by
  ext x y
  have hc : ((opposition K r).val : Mat K (r+1)) x y =
      (((opposition K r).val : Mat K (r+1)) *ᵥ Pi.single y 1) x := by
    simp [Matrix.col_apply]
  rw [hc]
  cases y with
  | inl b =>
    rw [opposition_spatial]
    cases x with
    | inl a =>
      cases a <;> cases b <;>
        simp [monomial_apply, oppositionPermutation, oppositionWeight, Pi.single_apply,
          eq_comm] <;> split_ifs <;> simp
    | inr a => simp [monomial_apply, oppositionPermutation, oppositionWeight]
  | inr b =>
    cases b
    rw [opposition_middle]
    cases x <;>
      simp [monomial_apply, oppositionPermutation, oppositionWeight]

theorem opposition_short_conjugation (r : ℕ) (b : Fin (r+1) ⊕ Fin (r+1)) (a : K) :
    (opposition K r).val * shortUnit K (r+1) b a * (opposition K r).val⁻¹ =
      shortUnit K (r+1) b.swap (-(-1:K)^(r+1) * a) := by
  let c : K := (-1)^(r+1)
  have hc : c*c=1 := by dsimp [c]; rw [← mul_pow]; simp
  apply short_conjugation (opposition K r).val (oppositionPermutation r)
    (oppositionWeight K r) (opposition_monomial K r) b b.swap (-c) a
  · rfl
  · cases b <;> rfl
  · cases b <;> rfl
  · exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  · cases b <;> exact neg_ne_zero.mpr one_ne_zero
  · change (-1:K) = -c*c
    rw [neg_mul, hc]
  · change c = -c*(-1)
    ring

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBCoordinateFlip
