import SymmetricSubgroupAsymptotics.CFSGHermitianTransverseCorrection
import Mathlib.Tactic.Module

/-! The transverse correction parametrizes the ENTIRE joint
perpendicular when the usual head/middle decomposition is available.
Its actual coordinate caller proves that decomposition; no dimension or
perpendicular-lattice hypothesis replaces the range equality. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGHermitianTransverseCorrection
open CFSGTwistedAUnitaryParameters CFSGHermitianOrthogonalSpan
variable {K I V : Type*} [Field K] [Fintype I] [AddCommGroup V] [Module K V]

theorem correction_range_eq_joint (sigma : K ≃+* K) (H : Matrix I I K)
    (e w : I → K) (j : V →ₗ[K] (I → K)) (pi : (I → K) →ₗ[K] V)
    (ell : (I → K) → K) (hc : hermitianPair sigma H w e ≠ 0)
    (hee : hermitianPair sigma H e e = 0) (hej : ∀ z, hermitianPair sigma H e (j z) = 0)
    (hdecomp : ∀ x, hermitianPair sigma H e x = 0 → x = ell x • e + j (pi x)) :
    (correction sigma H e w j).range =
      (pairRightLinear sigma H e).ker ⊓ (pairRightLinear sigma H w).ker := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    exact ⟨correction_orthogonal_to sigma H e w e j hee hej v,
      correction_orthogonal sigma H e w j hc v⟩
  · intro x hx
    have hdx := hdecomp x hx.1
    have hform := congrArg (pairRightLinear sigma H w) hdx
    change hermitianPair sigma H w x = hermitianPair sigma H w (ell x • e + j (pi x)) at hform
    rw [hermitianPair_add_right] at hform
    have hs := hermitianPair_smul sigma H 1 (ell x) w e
    simp only [one_smul, map_one, one_mul] at hs
    rw [hs] at hform
    have heq : ell x * hermitianPair sigma H w e + hermitianPair sigma H w (j (pi x)) = 0 :=
      hform.symm.trans hx.2
    have hcoeff : ell x = -(hermitianPair sigma H w e)⁻¹ * hermitianPair sigma H w (j (pi x)) := by
      apply mul_right_cancel₀ hc
      calc
        ell x * hermitianPair sigma H w e = -hermitianPair sigma H w (j (pi x)) :=
          add_eq_zero_iff_eq_neg.mp heq
        _ = (-(hermitianPair sigma H w e)⁻¹ * hermitianPair sigma H w (j (pi x))) *
            hermitianPair sigma H w e := by field_simp [hc] <;> ring
    refine ⟨pi x, ?_⟩
    rw [correction_apply]
    calc
      _ = ell x • e + j (pi x) := by rw [hcoeff]; module
      _ = x := hdx.symm

end SymmetricSubgroupAsymptotics.CFSGHermitianTransverseCorrection
