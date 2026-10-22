import SymmetricSubgroupAsymptotics.CFSGSerreQuadraticPositiveCollectingWord
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckCollectingPairCubes
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPositivePGroup

/-! Actual adjacent positive collecting words over the rationals.
Original Serre/Geck facts discharge every input; coefficient transport
is still required before using this word identity at bad primes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalPositiveCollecting
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGGeckSerreRepresentation
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckRationalAdjointStrings CFSGNormTwoGeckParameterizedWeyl
open CFSGNormTwoGeckRationalWeylCollecting CFSGNormTwoGeckCollectingPairCubes
open CFSGNormTwoGeckPositivePGroup
variable {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem adjacent_word (i j : Fin r) (hij : cartan b s i j= -1) (a : ℚ) :
    canonicalRoot (realizationData A hs hp b s) ℚ false i 1*
      canonicalRoot (realizationData A hs hp b s) ℚ false j a*
      (canonicalRoot (realizationData A hs hp b s) ℚ false i 1)⁻¹*
      (canonicalRoot (realizationData A hs hp b s) ℚ false j a)⁻¹=
      canonicalWeyl (realizationData A hs hp b s) ℚ i*
        canonicalRoot (realizationData A hs hp b s) ℚ false j a*
        (canonicalWeyl (realizationData A hs hp b s) ℚ i)⁻¹ := by
  apply CFSGSerreQuadraticPositiveCollectingWord.positive_commutator_word
    (realizationData A hs hp b s) i j
    ⁅fieldRoot (realizationData A hs hp b s) ℚ false i,
      fieldRoot (realizationData A hs hp b s) ℚ false j⁆
    (collecting_pair_commute A hs hp b s i j hij)
  · simpa only [one_smul] using conjugate_adjacent A hs hp b s i j hij (1:ℚ)
  · simpa only [parameterWeyl,canonicalWeyl,Units.val_one,inv_one] using
      weyl_conjugate_adjacent A hs hp b s i j hij

theorem adjacent_conjugate_mem_positive (i j : Fin r) (hij : cartan b s i j= -1) (a : ℚ) :
    canonicalWeyl (realizationData A hs hp b s) ℚ i*
      canonicalRoot (realizationData A hs hp b s) ℚ false j a*
      (canonicalWeyl (realizationData A hs hp b s) ℚ i)⁻¹∈rootGroup A hs hp b s ℚ false := by
  rw [←adjacent_word A hs hp b s i j hij a]
  have hi : canonicalRoot (realizationData A hs hp b s) ℚ false i 1∈
      rootGroup A hs hp b s ℚ false := Subgroup.subset_closure ⟨(i,1),rfl⟩
  have hj : canonicalRoot (realizationData A hs hp b s) ℚ false j a∈
      rootGroup A hs hp b s ℚ false := Subgroup.subset_closure ⟨(j,a),rfl⟩
  exact (rootGroup A hs hp b s ℚ false).mul_mem
    ((rootGroup A hs hp b s ℚ false).mul_mem
      ((rootGroup A hs hp b s ℚ false).mul_mem hi hj)
      ((rootGroup A hs hp b s ℚ false).inv_mem hi))
    ((rootGroup A hs hp b s ℚ false).inv_mem hj)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckRationalPositiveCollecting
