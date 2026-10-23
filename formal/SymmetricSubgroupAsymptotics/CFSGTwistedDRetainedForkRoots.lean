import SymmetricSubgroupAsymptotics.CFSGTwistedDPairedWeylCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedChainLift
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationMonomialAction

/-! A retained chain root, conjugated by the actual paired Weyl word,
gives the terminal fork root of the smaller split-D block. Both signs
and all fixed-field parameters are retained in the same original
Derived preimage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedForkRoots
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDPairedWeyl CFSGTwistedDPairedWeylMonomial
open CFSGTwistedDPairedWeylCoordinates CFSGTwistedDFixedChainLift
open CFSGTwistedDA2MatrixWitness CFSGOrthogonalDGenerationSLDouble
open CFSGTwistedDDerivedPairedRoots CFSGTwistedA2FixedField

theorem chain_val (K : Type) [Field K] (r : ℕ) (i j : Fin r)
    (hij : i ≠ j) (a : K) :
    ((chain K r i j hij a).val : Mat K r) =
      1 + Matrix.single (Sum.inl i) (Sum.inl j) a -
        Matrix.single (Sum.inr j) (Sum.inr i) a := by
  change (doubleHom K r (CFSGTypeAElementaryMatrices.elementary hij a) : Mat K r) = _
  rw [doubleHom_elementary_val]
  simp only [chainMatrix, smul_sub, Matrix.smul_single, smul_eq_mul, mul_one]
  abel

theorem conjugation_positive (s : ℕ) (q : CFSG.PrimePower)
    (i : Fin (s + 4)) (hp : i ≠ pen (s + 2)) (hl : i ≠ last (s + 2))
    (a : q.Extension 2) :
    (((pairedWeyl s q * chain (q.Extension 2) (s + 4) i (pen (s + 2)) hp (-a) *
      (pairedWeyl s q)⁻¹).val) : Mat (q.Extension 2) (s + 4)) =
      1 + Matrix.single (Sum.inl i) (Sum.inr (pen (s + 2))) a -
        Matrix.single (Sum.inl (pen (s + 2))) (Sum.inr i) a := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [chain_val]
  have h := CFSGOrthogonalDGenerationMonomialAction.conjugation_two_entry
    (pairedWeyl s q).val (pairedPermutation s) (pairedWeights (q.Extension 2) s)
    (pairedWeyl_monomial s q) (Sum.inl i) (Sum.inl (pen (s + 2)))
    (Sum.inr (pen (s + 2))) (Sum.inr i) (-a)
    (pairedWeights_ne_zero _ _ _) (pairedWeights_ne_zero _ _ _)
  simpa only [permutation_symm_eq, permutation_positive, permutation_negative,
    hp, hl, if_false, if_true, weights_positive, weights_negative,
    one_mul, neg_one_mul, div_one, div_neg, neg_neg] using h

theorem conjugation_negative (s : ℕ) (q : CFSG.PrimePower)
    (i : Fin (s + 4)) (hp : i ≠ pen (s + 2)) (hl : i ≠ last (s + 2))
    (a : q.Extension 2) :
    (((pairedWeyl s q * chain (q.Extension 2) (s + 4) (pen (s + 2)) i
      (Ne.symm hp) (-a) * (pairedWeyl s q)⁻¹).val) : Mat (q.Extension 2) (s + 4)) =
      1 + Matrix.single (Sum.inr (pen (s + 2))) (Sum.inl i) a -
        Matrix.single (Sum.inr i) (Sum.inl (pen (s + 2))) a := by
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
  rw [chain_val]
  have h := CFSGOrthogonalDGenerationMonomialAction.conjugation_two_entry
    (pairedWeyl s q).val (pairedPermutation s) (pairedWeights (q.Extension 2) s)
    (pairedWeyl_monomial s q) (Sum.inl (pen (s + 2))) (Sum.inl i)
    (Sum.inr i) (Sum.inr (pen (s + 2))) (-a)
    (pairedWeights_ne_zero _ _ _) (pairedWeights_ne_zero _ _ _)
  simpa only [permutation_symm_eq, permutation_positive, permutation_negative,
    hp, hl, if_false, if_true, weights_positive, weights_negative,
    one_mul, neg_one_mul, div_one, div_neg, neg_neg] using h

theorem chain_mem (s : ℕ) (q : CFSG.PrimePower) (i j : Fin (s + 3))
    (hij : i ≠ j) (a : fixedField q) :
    chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
      ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2) ∈
      naturalDerivedPreimage s q := by
  rw [← fixedChainLift_elementary s q i j hij a]
  exact fixedChainLift_mem s q _

theorem conjugate_chain_mem (s : ℕ) (q : CFSG.PrimePower)
    (i j : Fin (s + 3)) (hij : i ≠ j) (a : fixedField q) :
    pairedWeyl s q * chain (q.Extension 2) (s + 4) i.castSucc j.castSucc
      ((Fin.castSucc_injective (s + 3)).ne hij) (a : q.Extension 2) *
      (pairedWeyl s q)⁻¹ ∈ naturalDerivedPreimage s q :=
  (naturalDerivedPreimage s q).mul_mem
    ((naturalDerivedPreimage s q).mul_mem (pairedWeyl_mem s q)
      (chain_mem s q i j hij a)) ((naturalDerivedPreimage s q).inv_mem (pairedWeyl_mem s q))

end SymmetricSubgroupAsymptotics.CFSGTwistedDRetainedForkRoots
