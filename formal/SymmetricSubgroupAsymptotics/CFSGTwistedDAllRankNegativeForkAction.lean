import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDForkPairAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDTerminalRootCommutation

/-! The exact negative paired-root action at parameter one, uniformly
in low ranks and every characteristic. The quadratic cross term is retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankNegativeForkAction
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDRelativeElementaryGroup CFSGOrthogonalDForkPairAction

theorem negative_one_val (n : ℕ) (q : CFSG.PrimePower) :
    (pairedRoot n q true 1 : Mat (q.Extension 2) (n + 2)) =
      (forkPair (q.Extension 2) n 1 1 : Mat (q.Extension 2) (n + 2)).transpose := by
  let K := q.Extension 2
  have ht (i : Fin (n + 2)) :
      (rootTransvection K (n + 2) false i 1 : Mat K (n + 2)).transpose =
        (rootTransvection K (n + 2) true i 1 : Mat K (n + 2)) := by
    simp only [rootTransvection_val, rootMatrix, Bool.false_eq_true, if_false, if_true,
      one_smul, Matrix.transpose_add, Matrix.transpose_one, negative]
  have hc := CFSGOrthogonalDTerminalRootCommutation.rootTransvection_commute K n true true 1 1
  have hcm := congrArg (fun g : (Mat K (n + 2))ˣ => (g : Mat K (n + 2))) hc.eq
  change ((rootTransvection K (n + 2) true (pen n) 1 *
      rootTransvection K (n + 2) true (last n) (CFSGSerreOrdinaryTwists.definingFieldAutomorphism q 2 1) : (Mat K (n + 2))ˣ) : Mat K (n + 2)) = _
  rw [map_one]
  simp only [forkPair, Units.val_mul]
  rw [Matrix.transpose_mul, ht, ht]
  exact hcm

theorem negative_one_pen (n : ℕ) (q : CFSG.PrimePower)
    (v : Index (n + 2) → q.Extension 2) :
    ((pairedRoot n q true 1 : Mat (q.Extension 2) (n + 2)) *ᵥ v) (Sum.inr (pen n)) =
      v (Sum.inr (pen n)) - v (Sum.inr (last n)) -
        v (Sum.inl (last n)) - v (Sum.inl (pen n)) := by
  rw [negative_one_val, forkPair_val]
  simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.single_mulVec]
  simp only [Pi.add_apply, Pi.sub_apply, Function.update_apply, Pi.zero_apply,
    one_mul, mul_one, Sum.inr.injEq, pen_ne_last n, if_true, if_false]
  abel <;> simp only [zero_add]

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankNegativeForkAction
