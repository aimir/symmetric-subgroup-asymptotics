import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerFirstBlock
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPairingUnitColumns

/-! The second actual A2 three-root Singer block. The roots and every
column are bound to the same norm-two lattice and integral Geck word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerSecondBlock
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoRootNeighbors
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoRootStepCoordinates
open CFSGNormTwoGeckSingerFirstBlock CFSGNormTwoGeckPairingUnitColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

private theorem singer_apply (K : Type*) [CommRing K] (i j : Fin r)
    (v : b.support⊕Roots A→K) :
    singerOperator A hs hp b s K i j v=
      (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
        ((canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
          ((canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥv)) := by
  change ((canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*ᵥv=_
  rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]

theorem singer_second_block (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (l : Roots A) (hil : integerPairing A (s i:Roots A).val l.val= -1)
    (hjl : integerPairing A (s j:Roots A).val l.val=1) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr l) 1)=Pi.single (.inr l) 1 := by
  obtain ⟨m,hm⟩ := (root_sub_mem_iff A hs hp (s j) l).mpr hjl
  have hmv : m.val=l.val-(s j:Roots A).val := by
    ext t
    have ht := congrFun hm t
    change (m.val t:ℚ)=(l.val t:ℚ)-((s j:Roots A).val t:ℚ) at ht
    exact_mod_cast ht
  obtain ⟨k,hk⟩ := (root_add_mem_iff A hs hp (s i) l).mpr hil
  have hkv := root_add_val A hs hp hk
  have him : integerPairing A (s i:Roots A).val m.val=0 := by
    rw [hmv,map_sub,hil,hij];norm_num
  have hjm : integerPairing A (s j:Roots A).val m.val= -1 := by
    rw [hmv,map_sub,hjl,(s j:Roots A).property];norm_num
  have hik : integerPairing A (s i:Roots A).val k.val=1 := by
    rw [hkv,map_add,(s i:Roots A).property,hil];norm_num
  have hjk : integerPairing A (s j:Roots A).val k.val=0 := by
    rw [hkv,map_add,integer_symmetric A hs (s j:Roots A).val (s i:Roots A).val,hij,hjl];norm_num
  have rlm := reflection_sub A hs hp hjl hm
  have rml : (rootPairing A hs hp).reflectionPerm (s j) m=l := by
    rw [←rlm,RootPairing.reflectionPerm_self]
  have rlk := reflection_add A hs hp hil hk
  have rkl : (rootPairing A hs hp).reflectionPerm (s i) k=l := by
    rw [←rlk,RootPairing.reflectionPerm_self]
  have hf0 : singerOperator A hs hp b s K i j (Pi.single (.inr l) 1)=Pi.single (.inr m) 1 := by
    rw [singer_apply,weyl_root_column,rlm,weyl_root_column,reflection_fixed A hs hp (s i) m him]
    exact unit_fixed_of_pairing A hs hp b s K i m (by omega) (by omega)
  have hf1 : singerOperator A hs hp b s K i j (Pi.single (.inr m) 1)=Pi.single (.inr k) 1 := by
    rw [singer_apply,weyl_root_column,rml,weyl_root_column,rlk]
    exact unit_fixed_of_pairing A hs hp b s K i k (by omega) (by omega)
  have hf2 : singerOperator A hs hp b s K i j (Pi.single (.inr k) 1)=
      Pi.single (.inr l) 1+Pi.single (.inr k) 1 := by
    rw [singer_apply,weyl_root_column,reflection_fixed A hs hp (s j) k hjk,weyl_root_column,rkl]
    exact unit_add_of_root A hs hp b s K i l k hk
  exact (CFSGCharacteristicTwoSingerBlocks.second_companion_seven
    (singerOperator A hs hp b s K i j) (Pi.single (.inr l) 1) (Pi.single (.inr m) 1)
      (Pi.single (.inr k) 1) hf0 hf1 hf2).1

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerSecondBlock
