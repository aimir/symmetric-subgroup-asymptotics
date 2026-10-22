import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerFirstBlock
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckPairingUnitColumns
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoRootNegation
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalColumns
import SymmetricSubgroupAsymptotics.CFSGCharacteristicTwoA2SingerAdjointBlock

/-! Binding the eight A2-adjoint columns to the actual lattice Geck word.
The sum root and both negative strings are original norm-two roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerAdjoint
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoRootStepCoordinates
open CFSGNormTwoGeckSingerFirstBlock CFSGNormTwoGeckPairingUnitColumns
open CFSGNormTwoGeckFieldWeylCartan CFSGNormTwoRootNegation
open CFSGNormTwoGeckOrthogonalColumns CFSGNormTwoGeckFieldRootSteps
open CFSGNormTwoGeckFieldRootColumns
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

def adjointColumns (K : Type*) [CommRing K] (i j : Fin r) (gamma : Roots A) :
    Fin 8→(b.support⊕Roots A→K) :=
  ![Pi.single (.inl (s i)) 1,Pi.single (.inl (s j)) 1,
    Pi.single (.inr (s i:Roots A)) 1,Pi.single (.inr (s j:Roots A)) 1,
    Pi.single (.inr gamma) 1,Pi.single (.inr (negativeIndex A hs hp (s i))) 1,
    Pi.single (.inr (negativeIndex A hs hp (s j))) 1,
    Pi.single (.inr (negativeIndex A hs hp gamma)) 1]

theorem singer_adjoint_seven (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (gamma : Roots A)
    (hg : (rootPairing A hs hp).root gamma=
      (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root (s j))
    (z : Fin 8) :
    ((singerOperator A hs hp b s K i j)^7) (adjointColumns A hs hp b s K i j gamma z)=
      adjointColumns A hs hp b s K i j gamma z := by
  have hji : integerPairing A (s j:Roots A).val (s i:Roots A).val= -1 := by
    rw [integer_symmetric A hs];exact hij
  have hgv := root_add_val A hs hp hg
  have hig : integerPairing A (s i:Roots A).val gamma.val=1 := by
    rw [hgv,map_add,(s i:Roots A).property,hij];norm_num
  have hng : integerPairing A (s i:Roots A).val (negativeIndex A hs hp gamma).val= -1 := by
    rw [negative_val,map_neg,hig]
  have hnb : integerPairing A (s i:Roots A).val (negativeIndex A hs hp (s j)).val=1 := by
    rw [negative_val,map_neg,hij];norm_num
  have hcij : b.cartanMatrix (s i) (s j)= -1 := by
    rw [←integerPairing_eq_cartan A hs hp b];exact hij
  have hcji : b.cartanMatrix (s j) (s i)= -1 := by
    rw [←integerPairing_eq_cartan A hs hp b];exact hji
  have riaj := reflection_add A hs hp hij hg
  have rjai : (rootPairing A hs hp).reflectionPerm (s j) (s i)=gamma := by
    apply reflection_add A hs hp hji
    simpa only [add_comm] using hg
  have riag : (rootPairing A hs hp).reflectionPerm (s i) gamma=(s j:Roots A) := by
    rw [←riaj,RootPairing.reflectionPerm_self]
  have rjag : (rootPairing A hs hp).reflectionPerm (s j) gamma=(s i:Roots A) := by
    rw [←rjai,RootPairing.reflectionPerm_self]
  have riaa : (rootPairing A hs hp).reflectionPerm (s i) (s i)=negativeIndex A hs hp (s i) := rfl
  have rjbb : (rootPairing A hs hp).reflectionPerm (s j) (s j)=negativeIndex A hs hp (s j) := rfl
  have rinna : (rootPairing A hs hp).reflectionPerm (s i) (negativeIndex A hs hp (s i))=(s i:Roots A) := by
    rw [←riaa,RootPairing.reflectionPerm_self]
  have rjnnb : (rootPairing A hs hp).reflectionPerm (s j) (negativeIndex A hs hp (s j))=(s j:Roots A) := by
    rw [←rjbb,RootPairing.reflectionPerm_self]
  have hsub (x y : b.support⊕Roots A→K) : x-y=x+y := by
    ext z
    exact CharTwo.sub_eq_add (x z) (y z)
  have hadd (x : b.support⊕Roots A→K) : x+x=0 := by
    ext z
    exact CharTwo.add_self_eq_zero (x z)
  have habs2 : |(2:ℤ)|=2 := by decide
  have habs1 : |(-1:ℤ)|=1 := by decide
  have wa := weyl_cartan_general A hs hp b s K i (s i)
  have wb := weyl_cartan_general A hs hp b s K j (s j)
  have wab := weyl_cartan_general A hs hp b s K i (s j)
  have wba := weyl_cartan_general A hs hp b s K j (s i)
  simp only [RootPairing.Base.cartanMatrix_apply_same,habs2,Int.cast_ofNat,
    CharP.ofNat_eq_zero K 2,zero_smul,sub_zero] at wa wb
  simp only [hcij,hcji,habs1,Int.cast_one,one_smul,
    hsub] at wab wba
  have ua := unit_cartan A hs hp b s K i
  simp only [CharP.ofNat_eq_zero K 2,zero_smul,add_zero] at ua
  have ub := unit_cartan_general A hs hp b s K i (s j)
  simp only [hcij,habs1,Int.cast_one,one_smul] at ub
  have uab := unit_add_of_root A hs hp b s K i (s j) gamma hg
  have ung : (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
        Pi.single (.inr (negativeIndex A hs hp gamma)) 1=
        Pi.single (.inr (negativeIndex A hs hp gamma)) 1+
          Pi.single (.inr (negativeIndex A hs hp (s j))) 1 := by
    apply unit_add_of_root A hs hp b s K i
    rw [CFSGNormTwoRootNegation.root_negative,CFSGNormTwoRootNegation.root_negative,hg]
    abel
  have ug := unit_fixed_of_pairing A hs hp b s K i gamma (by omega) (by omega)
  have unb := unit_fixed_of_pairing A hs hp b s K i (negativeIndex A hs hp (s j)) (by omega) (by omega)
  apply CFSGCharacteristicTwoA2SingerAdjointBlock.singer_seven
    (singerOperator A hs hp b s K i j) (adjointColumns A hs hp b s K i j gamma)
  · change singerOperator A hs hp b s K i j (Pi.single (.inl (s i)) 1)=
      Pi.single (.inl (s j)) 1+Pi.single (.inr (s i:Roots A)) 1
    rw [singer_apply,wba]
    simp only [Matrix.mulVec_add,wa,wab,ua,ub]
    calc
      _=(Pi.single (.inl (s i)) 1+Pi.single (.inl (s i)) 1)+
          (Pi.single (.inl (s j)) 1+Pi.single (.inr (s i:Roots A)) 1) := by abel
      _=_ := by rw [hadd,zero_add]
  · change singerOperator A hs hp b s K i j (Pi.single (.inl (s j)) 1)=
      Pi.single (.inl (s i)) 1+Pi.single (.inl (s j)) 1+Pi.single (.inr (s i:Roots A)) 1
    rw [singer_apply,wb,wab,Matrix.mulVec_add,ub,ua]
    abel
  · change singerOperator A hs hp b s K i j (Pi.single (.inr (s i:Roots A)) 1)=
      Pi.single (.inr (s j:Roots A)) 1+Pi.single (.inr gamma) 1
    rw [singer_apply,weyl_root_column,rjai,weyl_root_column,riag,uab]
  · change singerOperator A hs hp b s K i j (Pi.single (.inr (s j:Roots A)) 1)=
      Pi.single (.inr (negativeIndex A hs hp (s j))) 1+Pi.single (.inr (negativeIndex A hs hp gamma)) 1
    rw [singer_apply,weyl_root_column,rjbb,weyl_root_column,reflection_negative,riaj,ung]
    abel
  · change singerOperator A hs hp b s K i j (Pi.single (.inr gamma) 1)=
      Pi.single (.inl (s i)) 1+Pi.single (.inr (s i:Roots A)) 1+
        Pi.single (.inr (negativeIndex A hs hp (s i))) 1
    rw [singer_apply,weyl_root_column,rjag,weyl_root_column,riaa,unit_negative]
    abel
  · change singerOperator A hs hp b s K i j (Pi.single (.inr (negativeIndex A hs hp (s i))) 1)=
      Pi.single (.inr (negativeIndex A hs hp (s j))) 1
    rw [singer_apply,weyl_root_column,reflection_negative,rjai,weyl_root_column,reflection_negative,riag,unb]
  · change singerOperator A hs hp b s K i j (Pi.single (.inr (negativeIndex A hs hp (s j))) 1)=
      Pi.single (.inr gamma) 1
    rw [singer_apply,weyl_root_column,rjnnb,weyl_root_column,riaj,ug]
  · change singerOperator A hs hp b s K i j (Pi.single (.inr (negativeIndex A hs hp gamma)) 1)=
      Pi.single (.inr (s i:Roots A)) 1
    rw [singer_apply,weyl_root_column,reflection_negative,rjag,weyl_root_column,rinna,unit_positive]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerAdjoint
