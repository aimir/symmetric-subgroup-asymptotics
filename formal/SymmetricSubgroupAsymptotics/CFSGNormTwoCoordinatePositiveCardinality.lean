import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateHeightFactorEquiv
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightPartition
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveHeightNormalForm

/-! Exact cardinality of the ACTUAL Geck positive subgroup in every
coefficient field: one independent field parameter for each ORIGINAL
positive lattice root. The proof telescopes genuine bijective height
factorizations and the finite-height root partition, without a named
exceptional root census or source-recognition hypothesis. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoCoordinatePositiveRootGenerators CFSGNormTwoCoordinateRootHeightFiltration
open CFSGNormTwoCoordinateRootHeightQuotient CFSGNormTwoCoordinateRootHeightBound
open CFSGNormTwoCoordinateExactHeightLayer CFSGNormTwoCoordinateHeightFactorEquiv
open CFSGNormTwoCoordinatePositiveHeightPartition CFSGNormTwoCoordinatePositiveHeightNormalForm

private theorem telescope_cardinality (q : ℕ) (a f : ℕ→ℕ)
    (hf : ∀n,f n=q^(a n)*f (n+1)) (m : ℕ) :
    f 0=q^(∑n∈Finset.range m,a n)*f m := by
  induction m with
  | zero=>simp
  | succ m ih=>
    calc
      f 0=q^(∑n∈Finset.range m,a n)*f m := ih
      _=q^(∑n∈Finset.range m,a n)*(q^(a m)*f (m+1)) := by rw [hf m]
      _=q^(∑n∈Finset.range (m+1),a n)*f (m+1) := by
        rw [Finset.sum_range_succ,pow_add,mul_assoc]

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]

theorem positive_card (K : Type) [Field K] :
    Nat.card (PositiveGroup A hd hs hp ho K)=Nat.card K ^ Nat.card (PositiveRoot A) := by
  let f : ℕ→ℕ := fun n=>Nat.card (heightTailInPositive A hd hs hp ho K ((n:ℤ)+1))
  let a : ℕ→ℕ := fun n=>Nat.card (ExactHeightRoot A ((n:ℤ)+1))
  have hstep : ∀n,f n=Nat.card K^(a n)*f (n+1) := by
    intro n
    have hn : (((n+1:ℕ):ℤ)+1)=((n:ℤ)+1)+1 := by omega
    simpa only [f,a,hn] using heightTail_card_step A hd hs hp ho K ((n:ℤ)+1) (by omega)
  have hfirst : f 0=Nat.card (PositiveGroup A hd hs hp ho K) := by
    change Nat.card ((heightTail A hd hs hp ho K 1).subgroupOf (PositiveGroup A hd hs hp ho K))=_
    rw [heightTail_one_eq_positive,Subgroup.subgroupOf_self,Subgroup.card_top]
  have hlast : f (rootHeightBound A)=1 := by
    change Nat.card ((heightTail A hd hs hp ho K ((rootHeightBound A:ℤ)+1)).subgroupOf
      (PositiveGroup A hd hs hp ho K))=1
    rw [final_heightTail_eq_bot,Subgroup.bot_subgroupOf,Subgroup.card_bot]
  have ht := telescope_cardinality (Nat.card K) a f hstep (rootHeightBound A)
  simpa only [hfirst,hlast,mul_one,a,positive_height_sum_card A] using ht

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinatePositiveCardinality
