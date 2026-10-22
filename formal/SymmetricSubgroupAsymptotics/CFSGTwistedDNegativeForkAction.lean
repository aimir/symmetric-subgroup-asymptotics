import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction
import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedFixedRoots
import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedRootImages
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDOrthogonalRootCommutation

/-! The negative paired root at parameter one creates an untouched
negative pivot from a positive pivot. The full quadratic cross term is
retained; no interpolation in the coefficient field is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeForkAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDPairedRootImages CFSGOrthogonalDForkPairAction

theorem negative_one_val (s : ℕ) (q : CFSG.PrimePower) :
    ((pairedNaturalRoot s q true 1).val : Mat (q.Extension 2) (s + 4)) =
      (forkPair (q.Extension 2) (s + 2) 1 1 : Mat (q.Extension 2) (s + 4)).transpose := by
  let K := q.Extension 2
  have ht (i : Fin (s + 4)) :
      (rootTransvection K (s + 4) false i 1 : Mat K (s + 4)).transpose =
        (rootTransvection K (s + 4) true i 1 : Mat K (s + 4)) := by
    simp only [rootTransvection_val, rootMatrix, Bool.false_eq_true, if_false, if_true,
      one_smul, Matrix.transpose_add, Matrix.transpose_one, negative]
  have hc := CFSGOrthogonalDOrthogonalRootCommutation.rootElement_commute K (s + 4)
    (by omega) (pen (s + 2)) (last (s + 2)) (pen_ne_last (s + 2))
    (CFSGTwistedDPairedFixedRoots.fork_cartan_zero s) true true 1 1
  have hcm := congrArg (fun g : elementaryRootGroup K (s + 4) => (g.val : Mat K (s + 4))) hc.eq
  change ((rootTransvection K (s + 4) true (pen (s + 2)) 1 *
      rootTransvection K (s + 4) true (last (s + 2)) (1 ^ q.order) : (Mat K (s + 4))ˣ) :
        Mat K (s + 4)) = _
  rw [one_pow]
  change ((rootTransvection K (s + 4) true (pen (s + 2)) 1 *
      rootTransvection K (s + 4) true (last (s + 2)) 1 : (Mat K (s + 4))ˣ) :
        Mat K (s + 4)) =
    (((rootTransvection K (s + 4) false (pen (s + 2)) 1 *
      rootTransvection K (s + 4) false (last (s + 2)) 1 : (Mat K (s + 4))ˣ) :
        Mat K (s + 4))).transpose
  simp only [Units.val_mul]
  rw [Matrix.transpose_mul, ht, ht]
  exact hcm

theorem negative_one_pen (s : ℕ) (q : CFSG.PrimePower)
    (v : Index (s + 4) → q.Extension 2) :
    (((pairedNaturalRoot s q true 1).val : Mat (q.Extension 2) (s + 4)) *ᵥ v)
        (Sum.inr (pen (s + 2))) =
      v (Sum.inr (pen (s + 2))) - v (Sum.inr (last (s + 2))) -
        v (Sum.inl (last (s + 2))) - v (Sum.inl (pen (s + 2))) := by
  rw [negative_one_val, forkPair_val]
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, Function.update_apply, Pi.zero_apply,
    one_mul, mul_one, Sum.inr.injEq, pen_ne_last (s + 2), if_true, if_false]
  abel <;> simp only [zero_add]

end SymmetricSubgroupAsymptotics.CFSGTwistedDNegativeForkAction
