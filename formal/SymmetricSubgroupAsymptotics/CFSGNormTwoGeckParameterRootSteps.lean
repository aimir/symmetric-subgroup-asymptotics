import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPairingUnitColumns

/-! Arbitrary-parameter columns on the actual two-root strings. The
negative columns are obtained from the same integral opposition, rather
than a presentation or a named finite-group identification. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterRootSteps
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoRootNeighbors CFSGNormTwoRootStrings CFSGNormTwoGeckFieldRootSteps
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterTripleColumns CFSGNormTwoGeckFieldOppositionColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem positive_zero_step (K : Type*) [CommRing K] (i : Fin r) (j : Roots A) (t : K)
    (hj : j≠negativeIndex A hs hp (s i))
    (ha : (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j∉
      Set.range (rootPairing A hs hp).root) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        Pi.single (.inr j) 1 := by
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_zero_step A hs hp b s K i j hj ha,second_other A hs hp b s K i j hj,
    smul_zero,add_zero]

theorem positive_fixed_of_pairing (K : Type*) [CommRing K] (i : Fin r)
    (j : Roots A) (t : K)
    (h1 : integerPairing A (s i:Roots A).val j.val≠ -1)
    (h2 : integerPairing A (s i:Roots A).val j.val≠ -2) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        Pi.single (.inr j) 1 := by
  apply positive_zero_step A hs hp b s K i j t
  · intro hj
    apply h2
    rw [hj,CFSGNormTwoGeckColumns.negative_val,map_neg,(s i:Roots A).property]
  · rw [root_add_mem_iff]
    exact h1

theorem positive_add_of_root (K : Type*) [CommRing K] (i : Fin r)
    (j k : Roots A) (t : K)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        Pi.single (.inr j) 1+t • Pi.single (.inr k) 1 := by
  have hj : j≠negativeIndex A hs hp (s i) := by
    intro hj
    have hc := pairing_of_root_add A hs hp hk
    rw [hj,CFSGNormTwoGeckColumns.negative_val,map_neg,(s i:Roots A).property] at hc
    norm_num at hc
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_add_step A hs hp b s K i j k hk,second_other A hs hp b s K i j hj,
    smul_zero,add_zero]

theorem negative_fixed_of_pairing (K : Type*) [CommRing K] (i : Fin r)
    (j : Roots A) (t : K)
    (h1 : integerPairing A (s i:Roots A).val j.val≠1)
    (h2 : integerPairing A (s i:Roots A).val j.val≠2) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        Pi.single (.inr j) 1 := by
  have hn1 : integerPairing A (s i:Roots A).val
      (negativeIndex A hs hp j).val≠ -1 := by
    rw [CFSGNormTwoGeckColumns.negative_val,map_neg]
    omega
  have hn2 : integerPairing A (s i:Roots A).val
      (negativeIndex A hs hp j).val≠ -2 := by
    rw [CFSGNormTwoGeckColumns.negative_val,map_neg]
    omega
  rw [CFSGNormTwoGeckParameterTripleColumns.negative_val,←Matrix.mulVec_mulVec,
    ←Matrix.mulVec_mulVec,omega_root,
    positive_fixed_of_pairing A hs hp b s K i (negativeIndex A hs hp j) t hn1 hn2,
    omega_root,CFSGNormTwoRootNegation.negative_negative]

theorem negative_sub_of_root (K : Type*) [CommRing K] (i : Fin r)
    (j k : Roots A) (t : K)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr k) 1=
        Pi.single (.inr k) 1+t • Pi.single (.inr j) 1 := by
  have hback : (rootPairing A hs hp).root (negativeIndex A hs hp j)=
      (rootPairing A hs hp).root (s i)+
        (rootPairing A hs hp).root (negativeIndex A hs hp k) := by
    rw [CFSGNormTwoRootNegation.root_negative,CFSGNormTwoRootNegation.root_negative,hk]
    abel
  rw [CFSGNormTwoGeckParameterTripleColumns.negative_val,←Matrix.mulVec_mulVec,
    ←Matrix.mulVec_mulVec,omega_root,
    positive_add_of_root A hs hp b s K i (negativeIndex A hs hp k)
      (negativeIndex A hs hp j) t hback,
    Matrix.mulVec_add,Matrix.mulVec_smul,omega_root,omega_root,
    CFSGNormTwoRootNegation.negative_negative,CFSGNormTwoRootNegation.negative_negative]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterRootSteps
