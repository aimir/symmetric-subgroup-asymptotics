import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarNormalizedCone
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoSemilinearVector
import SymmetricSubgroupAsymptotics.CFSGHermitianTwoByTwoUndoCongruence

/-! A literal original-model star stabilizer induces a quadratic-field
semilinear map on its two-dimensional point vectors. The scalar field,
cone preservation, axis normalization and coefficient reconstruction
are all derived from the original automorphism; none is a callback. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGHermitianTwoByTwoRankOne

theorem exists_unitaryStar_semilinear_vectors (q : CFSG.PrimePower) (s : ℕ)
    (t : q.Extension 2) (ht : t ≠ 0) (htc : t ∈ centralParameters q (s + 1))
    (f : MulAut (CFSG.Models.TwistedA (s + 3) q))
    (hinc : ∀ P : unitarySingularPoints q s,
      (unitarySingularPointActionHom q s f P).val ≤ starPlane q s ↔ P.val ≤ starPlane q s) :
    ∃ theta : q.Extension 2 ≃+* q.Extension 2,
      Function.Commute (definingFieldAutomorphism q 2) theta ∧
      ∃ L : (Fin 2 → q.Extension 2) →ₛₗ[theta.toRingHom] (Fin 2 → q.Extension 2),
        Function.Injective L ∧ ∃ (c : q.Extension 2)
          (hc : definingFieldAutomorphism q 2 c = c), c ≠ 0 ∧ ∀ v,
          unitaryStarCoefficientAut q s t ht htc f hinc
            (rankOneParameter (definingFieldAutomorphism q 2)
              (fun z => extension_two_pow_twice q z) 1 (map_one _) v) =
            rankOneParameter (definingFieldAutomorphism q 2)
              (fun z => extension_two_pow_twice q z) c hc (L v) := by
  obtain ⟨tau, hcomm, hscalar⟩ := exists_unitaryStar_extension_semilinear q s t ht htc f hinc
  obtain ⟨a, b, ha, hb, ha0, hb0, v, w, hdet, hE0, hE1⟩ :=
    exists_unitaryStar_axis_images q s t ht htc f hinc
  obtain ⟨D, hD0, hD1⟩ := exists_rankOne_axis_normalization (definingFieldAutomorphism q 2)
    (fun z => extension_two_pow_twice q z) (unitaryStarCoefficientAut q s t ht htc f hinc)
    a b ha hb v w hdet hE0 hE1
  let E := unitaryStarNormalizedAut q s t ht htc f hinc D
  have hS (c : q.Extension 2) (hc : definingFieldAutomorphism q 2 c = c)
      (A : parameters (definingFieldAutomorphism q 2)) :
      E (fixedScaleHom (definingFieldAutomorphism q 2) c hc A) =
      fixedScaleHom (definingFieldAutomorphism q 2) (tau c)
        (automorphism_fixed_of_commute (definingFieldAutomorphism q 2) tau hcomm c hc) (E A) := by
    change coefficientCongruence (definingFieldAutomorphism q 2)
      (fun z => extension_two_pow_twice q z) D
      (unitaryStarCoefficientAut q s t ht htc f hinc (fixedScaleHom _ c hc A)) =
      fixedScaleHom (definingFieldAutomorphism q 2) (tau c)
        (automorphism_fixed_of_commute (definingFieldAutomorphism q 2) tau hcomm c hc)
        (coefficientCongruence (definingFieldAutomorphism q 2)
          (fun z => extension_two_pow_twice q z) D (unitaryStarCoefficientAut q s t ht htc f hinc A))
    rw [hscalar, coefficientCongruence_fixedScale]
  have hC (A : parameters (definingFieldAutomorphism q 2)) (hA : A.val.det = 0) :
      (E A).val.det = 0 :=
    coefficientCongruence_det_zero (definingFieldAutomorphism q 2)
      (fun z => extension_two_pow_twice q z) D _
      (unitaryStarCoefficientAut_preserves_cone q s t ht htc f hinc A hA)
  let gamma := offDiagonalImageHom (definingFieldAutomorphism q 2)
    (fun z => extension_two_pow_twice q z) E 1
  have hgamma : gamma * definingFieldAutomorphism q 2 gamma = a * b := by
    have hh := normalized_cone_offDiagonal_norm (definingFieldAutomorphism q 2) tau
      (fun z => extension_two_pow_twice q z) hcomm E hS hC a b ha hb ha0 hb0 hD0 hD1 1
    simpa only [CFSGQuadraticNormAdditiveRigidity.norm, map_one, one_mul, mul_one] using hh
  have hoff := normalized_cone_offDiagonal_semilinear (definingFieldAutomorphism q 2) tau
    (fun z => extension_two_pow_twice q z) hcomm E hS hC a b ha hb ha0 hb0 hD0 hD1
  obtain ⟨theta, htheta, L, hL, hR⟩ := exists_normalized_cone_vector_map
    (definingFieldAutomorphism q 2) tau (fun z => extension_two_pow_twice q z)
    hcomm E hS hC a b gamma ha hb ha0 hb0 hD0 hD1 hgamma hoff
  let c : q.Extension 2 := theta 1 / a
  have hc : definingFieldAutomorphism q 2 c = c := by
    change definingFieldAutomorphism q 2 (theta 1 / a) = theta 1 / a
    rw [map_div₀, map_one, map_one, ha]
  have hc0 : c ≠ 0 := div_ne_zero (by rw [map_one]; exact one_ne_zero) ha0
  have hR1 (z : Fin 2 → q.Extension 2) :
      ((unitaryStarCoefficientAut q s t ht htc f hinc).trans
        (coefficientCongruence (definingFieldAutomorphism q 2)
          (fun y => extension_two_pow_twice q y) D))
        (rankOneParameter (definingFieldAutomorphism q 2)
          (fun y => extension_two_pow_twice q y) 1 (map_one _) z) =
      rankOneParameter (definingFieldAutomorphism q 2)
        (fun y => extension_two_pow_twice q y) c hc (L z) := hR 1 (map_one _) z
  obtain ⟨M, hM, hMR⟩ := undo_congruence_rankOne (definingFieldAutomorphism q 2) theta
    (fun z => extension_two_pow_twice q z) (unitaryStarCoefficientAut q s t ht htc f hinc)
    D L hL c hc hR1
  exact ⟨theta, htheta, M, hM, c, hc, hc0, hMR⟩

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
