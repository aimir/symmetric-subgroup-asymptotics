import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOpposition
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNegation

/-! The actual integral opposition fixes each Cartan coordinate and
permutes root coordinates by the actual root negation, over every ring. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOppositionColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckFieldOpposition CFSGGeckIntegralMatrices
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base)

theorem omega_cartan (K : Type*) [CommRing K] (i : b.support) :
    fieldOmega A hs hp b K*ᵥPi.single (.inl i) 1=Pi.single (.inl i) 1 := by
  rw [Matrix.mulVec_single_one]
  ext (j|j) <;> simp [fieldOmega,Omega,Matrix.one_apply,Pi.single_apply,eq_comm]

theorem omega_root (K : Type*) [CommRing K] (i : Roots A) :
    fieldOmega A hs hp b K*ᵥPi.single (.inr i) 1=
      Pi.single (.inr (negativeIndex A hs hp i)) 1 := by
  rw [Matrix.mulVec_single_one]
  ext (j|j) <;> simp [fieldOmega,Omega,negativeIndex,Pi.single_apply,eq_comm]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldOppositionColumns
