import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedTorus
import SymmetricSubgroupAsymptotics.CFSGNormTwoPairingBounds

/-! Actual diagonal rank-one tori on the full original Geck space.
The integer norm-two root classification discharges every column; no
generic split torus, eigenbasis or good-prime hypothesis is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalTorus
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoPairingBounds CFSGNormTwoRootNeighbors
open CFSGNormTwoGeckParameterizedTorus
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def weight (i : Fin r) : b.support⊕Roots A→ℤ
  | .inl _=>0
  | .inr k=>integerPairing A (s i:Roots A).val k.val

theorem torus_root (K : Type*) [Field K] (i : Fin r) (t : Kˣ) (k : Roots A) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr k) 1=
        (t:K)^(integerPairing A (s i:Roots A).val k.val) • Pi.single (.inr k) 1 := by
  by_cases heq : k=s i
  · subst k
    simpa only [(s i:Roots A).property,zpow_ofNat] using
      (torus_triple A hs hp b s K i t).2.1
  by_cases hneg : k=negativeIndex A hs hp (s i)
  · subst k
    simpa only [negative_val,map_neg,(s i:Roots A).property,zpow_neg,zpow_ofNat,inv_pow]
      using (torus_triple A hs hp b s K i t).2.2
  have hopp : (s i:Roots A).val≠ -k.val := by
    intro h
    apply hneg
    apply Subtype.ext
    rw [negative_val,h,neg_neg]
  rcases root_pairing_interior A hs hp (s i:Roots A) k (Ne.symm heq) hopp with h|h|h
  · obtain ⟨l,hl⟩ := (root_add_mem_iff A hs hp (s i) k).mpr h
    simpa only [h,zpow_neg,zpow_one] using (torus_pair A hs hp b s K i k l t hl).1
  · simpa only [h,zpow_zero,one_smul] using torus_fixed A hs hp b s K i k t h
  · obtain ⟨l,hl⟩ := (root_sub_mem_iff A hs hp (s i) k).mpr h
    have hkl : (rootPairing A hs hp).root k=
        (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root l := by
      rw [hl]
      abel
    simpa only [h,zpow_one] using (torus_pair A hs hp b s K i l k t hkl).2

theorem torus_column (K : Type*) [Field K] (i : Fin r) (t : Kˣ)
    (k : b.support⊕Roots A) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single k 1=
        (t:K)^(weight A hs hp b s i k) • Pi.single k 1 := by
  cases k with
  | inl k=>simpa only [weight,zpow_zero,one_smul] using torus_cartan A hs hp b s K i t k
  | inr k=>exact torus_root A hs hp b s K i t k

theorem torus_diagonal (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)=
      Matrix.diagonal (fun k=>(t:K)^(weight A hs hp b s i k)) := by
  ext j k
  have hh := congrFun (torus_column A hs hp b s K i t k) j
  by_cases hj : j=k
  · subst j
    simpa [Matrix.mulVec_single_one,Pi.single_apply,Matrix.diagonal_apply] using hh
  · simpa [Matrix.mulVec_single_one,Pi.single_apply,Matrix.diagonal_apply,hj,Ne.symm hj] using hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckDiagonalTorus
