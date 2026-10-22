import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylCharTwoRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldRootSteps
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootStepCoordinates
import SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoSingerBlocks

/-! The first actual A2 three-root Singer block inside the original Geck
matrices. Roots are constructed by the norm-two addition criterion, and
all unit/Weyl columns are proved on those SAME roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerFirstBlock
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootNeighbors
open CFSGNormTwoGeckColumns CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoGeckFieldRootSteps CFSGNormTwoRootStepCoordinates
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def singerOperator (K : Type*) [CommRing K] (i j : Fin r) :
    Module.End K (b.support⊕Roots A→K) :=
  Matrix.toLinAlgEquiv' (((canonicalRoot (realizationData A hs hp b s) K false i 1)*
    canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalWeyl (realizationData A hs hp b s) K j : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ) :
        Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)

private theorem singer_apply (K : Type*) [CommRing K] (i j : Fin r) (v : b.support⊕Roots A→K) :
    singerOperator A hs hp b s K i j v=
      (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
        ((canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
          ((canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥv)) := by
  change ((canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*ᵥv=_
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]

private theorem unit_fixed (K : Type*) [CommRing K] (i : Fin r) (k : Roots A)
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

theorem singer_first_block (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (k : Roots A) (hik : integerPairing A (s i:Roots A).val k.val= -1)
    (hjk : integerPairing A (s j:Roots A).val k.val=0) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
  obtain ⟨l,hl⟩ := (root_add_mem_iff A hs hp (s i) k).mpr hik
  have hlv := root_add_val A hs hp hl
  have hil : integerPairing A (s i:Roots A).val l.val=1 := by
    rw [hlv,map_add,(s i:Roots A).property,hik];norm_num
  have hjl : integerPairing A (s j:Roots A).val l.val= -1 := by
    rw [hlv,map_add,integer_symmetric A hs (s j:Roots A).val (s i:Roots A).val,hij,hjk];norm_num
  obtain ⟨m,hm⟩ := (root_add_mem_iff A hs hp (s j) l).mpr hjl
  have hmv := root_add_val A hs hp hm
  have him : integerPairing A (s i:Roots A).val m.val=0 := by
    rw [hmv,map_add,hij,hil];norm_num
  have hjm : integerPairing A (s j:Roots A).val m.val=1 := by
    rw [hmv,map_add,(s j:Roots A).property,hjl];norm_num
  have rl0 := reflection_fixed A hs hp (s j) k hjk
  have rl1 := reflection_add A hs hp hik hl
  have rl2 := reflection_add A hs hp hjl hm
  have rm0 := reflection_fixed A hs hp (s i) m him
  have rm1 : (rootPairing A hs hp).reflectionPerm (s j) m=l := by
    rw [←rl2,RootPairing.reflectionPerm_self]
  have rm2 : (rootPairing A hs hp).reflectionPerm (s i) l=k := by
    rw [←rl1,RootPairing.reflectionPerm_self]
  have hf0 : singerOperator A hs hp b s K i j (Pi.single (.inr k) 1)=Pi.single (.inr l) 1 := by
    rw [singer_apply,weyl_root_column,rl0,weyl_root_column,rl1]
    exact unit_fixed A hs hp b s K i l (by omega) (by omega)
  have hf1 : singerOperator A hs hp b s K i j (Pi.single (.inr l) 1)=Pi.single (.inr m) 1 := by
    rw [singer_apply,weyl_root_column,rl2,weyl_root_column,rm0]
    exact unit_fixed A hs hp b s K i m (by omega) (by omega)
  have hf2 : singerOperator A hs hp b s K i j (Pi.single (.inr m) 1)=
      Pi.single (.inr k) 1+Pi.single (.inr l) 1 := by
    rw [singer_apply,weyl_root_column,rm1,weyl_root_column,rm2]
    apply unit_add_step A hs hp b s K i k l
    · intro hk
      rw [hk,negative_val,map_neg,(s i:Roots A).property] at hik
      norm_num at hik
    · exact hl
  exact (CFSGCharacteristicTwoSingerBlocks.first_companion_seven
    (singerOperator A hs hp b s K i j) (Pi.single (.inr k) 1) (Pi.single (.inr l) 1)
      (Pi.single (.inr m) 1) hf0 hf1 hf2).1

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerFirstBlock
