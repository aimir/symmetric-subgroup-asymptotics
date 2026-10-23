import SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankWeylCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedForkRoots

/-! The actual paired Weyl word transports every disjoint chain root
into its smaller fork root, including the rank-three-to-rank-two block. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankConjugateFork
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDAllRankPairedWeyl CFSGTwistedDAllRankWeylCoordinates
open CFSGTwistedDA2MatrixWitness

theorem conjugation_positive (n : ℕ) (q : CFSG.PrimePower)
    (i : Fin (n + 2)) (hp : i ≠ pen n) (hl : i ≠ last n)
    (a : q.Extension 2) :
    (((weyl n q).val * (chain (q.Extension 2) (n + 2) i (pen n) hp (-a)).val *
      (weyl n q).val⁻¹) : Mat (q.Extension 2) (n + 2)) =
      1 + Matrix.single (Sum.inl i) (Sum.inr (pen n)) a -
        Matrix.single (Sum.inl (pen n)) (Sum.inr i) a := by
  rw [CFSGTwistedDRetainedForkRoots.chain_val]
  have h := CFSGOrthogonalDGenerationMonomialAction.conjugation_two_entry
    (weyl n q).val (pairedPermutation n) (pairedWeights (q.Extension 2) n)
    (weyl_monomial n q) (Sum.inl i) (Sum.inl (pen n))
    (Sum.inr (pen n)) (Sum.inr i) (-a)
    (pairedWeights_ne_zero _ _ _) (pairedWeights_ne_zero _ _ _)
  simpa only [permutation_symm_eq, permutation_positive, permutation_negative,
    hp, hl, if_false, if_true, weights_positive, weights_negative,
    one_mul, neg_one_mul, div_one, div_neg, neg_neg] using h

theorem conjugation_negative (n : ℕ) (q : CFSG.PrimePower)
    (i : Fin (n + 2)) (hp : i ≠ pen n) (hl : i ≠ last n)
    (a : q.Extension 2) :
    (((weyl n q).val * (chain (q.Extension 2) (n + 2) (pen n) i
      (Ne.symm hp) (-a)).val * (weyl n q).val⁻¹) : Mat (q.Extension 2) (n + 2)) =
      1 + Matrix.single (Sum.inr (pen n)) (Sum.inl i) a -
        Matrix.single (Sum.inr i) (Sum.inl (pen n)) a := by
  rw [CFSGTwistedDRetainedForkRoots.chain_val]
  have h := CFSGOrthogonalDGenerationMonomialAction.conjugation_two_entry
    (weyl n q).val (pairedPermutation n) (pairedWeights (q.Extension 2) n)
    (weyl_monomial n q) (Sum.inl (pen n)) (Sum.inl i)
    (Sum.inr i) (Sum.inr (pen n)) (-a)
    (pairedWeights_ne_zero _ _ _) (pairedWeights_ne_zero _ _ _)
  simpa only [permutation_symm_eq, permutation_positive, permutation_negative,
    hp, hl, if_false, if_true, weights_positive, weights_negative,
    one_mul, neg_one_mul, div_one, div_neg, neg_neg] using h

end SymmetricSubgroupAsymptotics.CFSGTwistedDAllRankConjugateFork
