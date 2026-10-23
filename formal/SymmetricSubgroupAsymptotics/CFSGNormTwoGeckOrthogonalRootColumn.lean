import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterTripleColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNeighbors

/-! An actual quadratic simple-root unit fixes every root column
orthogonal to its simple root. The norm-two sum criterion excludes a
step; this is an integral root argument, not a root enumeration or a
large-field polynomial separation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalRootColumn
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckFieldRootSteps CFSGNormTwoGeckFieldRootColumns
open CFSGNormTwoGeckParameterTripleColumns CFSGNormTwoRootNeighbors
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem positive_fixes_orthogonal_column (K : Type*) [CommRing K]
    (i : Fin r) (j : Roots A) (hij : integerPairing A (s i : Roots A).val j.val=0) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K false i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (Sum.inr j) 1=
        Pi.single (Sum.inr j) 1 := by
  have hne : j≠negativeIndex A hs hp (s i) := by
    intro he
    have hh := hij
    rw [he,CFSGNormTwoGeckColumns.negative_val,map_neg,(s i : Roots A).property] at hh
    norm_num at hh
  have hadd : (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j∉
      Set.range (rootPairing A hs hp).root := by
    rw [root_add_mem_iff A hs hp,hij]
    decide
  simp only [canonicalRoot_val,Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    root_zero_step A hs hp b s K i j hne hadd,second_other A hs hp b s K i j hne,
    smul_zero,add_zero]

theorem negative_fixes_orthogonal_column (K : Type*) [CommRing K]
    (i : Fin r) (j : Roots A) (hij : integerPairing A (s i : Roots A).val j.val=0) (t : K) :
    (canonicalRoot (realizationData A hs hp b s) K true i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (Sum.inr j) 1=
        Pi.single (Sum.inr j) 1 := by
  have hneg : integerPairing A (s i : Roots A).val (negativeIndex A hs hp j).val=0 := by
    rw [CFSGNormTwoGeckColumns.negative_val,map_neg,hij,neg_zero]
  rw [CFSGNormTwoGeckParameterTripleColumns.negative_val,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,
    CFSGNormTwoGeckFieldOppositionColumns.omega_root,
    positive_fixes_orthogonal_column A hs hp b s K i _ hneg t,
    CFSGNormTwoGeckFieldOppositionColumns.omega_root,
    CFSGNormTwoRootNegation.negative_negative]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalRootColumn
