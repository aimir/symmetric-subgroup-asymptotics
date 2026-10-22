import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootSteps
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylRootStrings

/-! Unit columns selected by the actual integer root pairing, with all
zero and root-step conditions discharged from the norm-two geometry. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPairingUnitColumns
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoRootNeighbors CFSGNormTwoRootStrings CFSGNormTwoGeckFieldRootSteps
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem unit_fixed_of_pairing (K : Type*) [CommRing K] (i : Fin r) (k : Roots A)
    (h1 : integerPairing A (s i:Roots A).val k.val≠ -1)
    (h2 : integerPairing A (s i:Roots A).val k.val≠ -2) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr k) 1=Pi.single (.inr k) 1 := by
  apply unit_zero_step A hs hp b s K i k
  · intro hk
    apply h2
    rw [hk,negative_val,map_neg,(s i:Roots A).property]
  · rw [root_add_mem_iff]
    exact h1

theorem unit_add_of_root (K : Type*) [CommRing K] (i : Fin r) (j k : Roots A)
    (hk : (rootPairing A hs hp).root k=(rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j) :
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
      Pi.single (.inr j) 1+Pi.single (.inr k) 1 := by
  apply unit_add_step A hs hp b s K i j k _ hk
  intro hj
  have hc := pairing_of_root_add A hs hp hk
  rw [hj,negative_val,map_neg,(s i:Roots A).property] at hc
  norm_num at hc

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPairingUnitColumns
