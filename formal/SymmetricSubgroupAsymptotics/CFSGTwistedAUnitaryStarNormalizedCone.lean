import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarAxisImages
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoConeSemilinear

/-! Actual ORIGINAL unitary star stabilizers satisfy the normalized
cone semilinear classification. Every input of the generic theorem is
discharged: original point-root covariance gives the cone, the centroid
gives the base-field map, its actual lift gives tau, and the distinct
original image points give the invertible axis change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGHermitianTwoByTwoRankOne

def unitaryStarNormalizedAut (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s)
    (D : (Matrix (Fin 2) (Fin 2) (q.Extension 2))ˣ) :
    parameters (definingFieldAutomorphism q 2) ≃+ parameters (definingFieldAutomorphism q 2) :=
  (unitaryStarCoefficientAut q s t ht htc f hinc).trans
    (coefficientCongruence (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z) D)

theorem exists_unitaryStar_normalized_cone_semilinear (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    ∃ tau : q.Extension 2 ≃+* q.Extension 2,
      ∃ hcomm : Function.Commute (definingFieldAutomorphism q 2) tau,
      ∃ (D : (Matrix (Fin 2) (Fin 2) (q.Extension 2))ˣ) (a b : q.Extension 2)
        (ha : definingFieldAutomorphism q 2 a = a) (hb : definingFieldAutomorphism q 2 b = b),
        a ≠ 0 ∧ b ≠ 0 ∧
        unitaryStarNormalizedAut q s t ht htc f hinc D
          (axis0 (definingFieldAutomorphism q 2) 1 (map_one _)) = axis0 (definingFieldAutomorphism q 2) a ha ∧
        unitaryStarNormalizedAut q s t ht htc f hinc D
          (axis1 (definingFieldAutomorphism q 2) 1 (map_one _)) = axis1 (definingFieldAutomorphism q 2) b hb ∧
        ((∀ x, offDiagonalImageHom (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z)
            (unitaryStarNormalizedAut q s t ht htc f hinc D) x =
          offDiagonalImageHom (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z)
            (unitaryStarNormalizedAut q s t ht htc f hinc D) 1 * tau x) ∨
         (∀ x, offDiagonalImageHom (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z)
            (unitaryStarNormalizedAut q s t ht htc f hinc D) x =
          offDiagonalImageHom (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z)
            (unitaryStarNormalizedAut q s t ht htc f hinc D) 1 * tau (definingFieldAutomorphism q 2 x))) := by
  obtain ⟨tau, hcomm, hscalar⟩ := exists_unitaryStar_extension_semilinear q s t ht htc f hinc
  obtain ⟨a, b, ha, hb, ha0, hb0, v, w, hdet, hE0, hE1⟩ := exists_unitaryStar_axis_images q s t ht htc f hinc
  obtain ⟨D, hD0, hD1⟩ := exists_rankOne_axis_normalization (definingFieldAutomorphism q 2)
    (fun z => extension_two_pow_twice q z) (unitaryStarCoefficientAut q s t ht htc f hinc)
    a b ha hb v w hdet hE0 hE1
  have hS (c : q.Extension 2) (hc : definingFieldAutomorphism q 2 c = c)
      (A : parameters (definingFieldAutomorphism q 2)) :
      unitaryStarNormalizedAut q s t ht htc f hinc D
        (fixedScaleHom (definingFieldAutomorphism q 2) c hc A) =
      fixedScaleHom (definingFieldAutomorphism q 2) (tau c)
        (automorphism_fixed_of_commute (definingFieldAutomorphism q 2) tau hcomm c hc)
        (unitaryStarNormalizedAut q s t ht htc f hinc D A) := by
    change coefficientCongruence (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z) D
      (unitaryStarCoefficientAut q s t ht htc f hinc (fixedScaleHom _ c hc A)) =
      fixedScaleHom (definingFieldAutomorphism q 2) (tau c)
        (automorphism_fixed_of_commute (definingFieldAutomorphism q 2) tau hcomm c hc)
        (coefficientCongruence (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z) D
          (unitaryStarCoefficientAut q s t ht htc f hinc A))
    rw [hscalar, coefficientCongruence_fixedScale]
  have hC (A : parameters (definingFieldAutomorphism q 2)) (hA : A.val.det = 0) :
      (unitaryStarNormalizedAut q s t ht htc f hinc D A).val.det = 0 :=
    coefficientCongruence_det_zero (definingFieldAutomorphism q 2) (fun z => extension_two_pow_twice q z) D _
      (unitaryStarCoefficientAut_preserves_cone q s t ht htc f hinc A hA)
  refine ⟨tau, hcomm, D, a, b, ha, hb, ha0, hb0, hD0, hD1, ?_⟩
  exact normalized_cone_offDiagonal_semilinear (definingFieldAutomorphism q 2) tau
    (fun z => extension_two_pow_twice q z) hcomm (unitaryStarNormalizedAut q s t ht htc f hinc D)
    hS hC a b ha hb ha0 hb0 hD0 hD1

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
