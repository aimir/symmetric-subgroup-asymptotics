import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerSecondBlock
import SymmetricSubgroupAsymptotics.CFSGNormTwoA2WeightCases

/-! Actual Singer power-seven columns for each of the seven weights
outside the six A2 roots. Successor columns remain in the same word. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerOutside
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoRootStepCoordinates
open CFSGNormTwoGeckSingerFirstBlock CFSGNormTwoGeckSingerSecondBlock
open CFSGNormTwoGeckPairingUnitColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

private theorem reflected_pair (i j k : Roots A) :
    integerPairing A i.val ((rootPairing A hs hp).reflectionPerm j k).val=
      integerPairing A i.val k.val-integerPairing A j.val k.val*integerPairing A i.val j.val := by
  simp only [reflection_val,map_sub,map_smul,smul_eq_mul,integer_symmetric A hs k.val j.val]

private theorem successor_fixed {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (x y : M) (hx : (f^7) x=x) (hxy : f x=y) : (f^7) y=y := by
  have hh := DFunLike.congr_fun ((Commute.refl f).pow_left 7).eq x
  change (f^7) (f x)=f ((f^7) x) at hh
  simpa only [hx,hxy] using hh

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

theorem singer_weight_one_neg_one (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (k : Roots A) (hik : integerPairing A (s i:Roots A).val k.val=1)
    (hjk : integerPairing A (s j:Roots A).val k.val= -1) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
  let x := (rootPairing A hs hp).reflectionPerm (s i) k
  have hix : integerPairing A (s i:Roots A).val x.val= -1 := by
    rw [reflected_pair,(s i:Roots A).property,hik];norm_num
  have hjx : integerPairing A (s j:Roots A).val x.val=0 := by
    rw [reflected_pair,integer_symmetric A hs (s j:Roots A).val (s i:Roots A).val,hij,hik,hjk];norm_num
  have hx := singer_first_block A hs hp b s K i j hij x hix hjx
  apply successor_fixed _ _ _ hx
  rw [singer_apply,weyl_root_column,reflection_fixed A hs hp (s j) x hjx,weyl_root_column]
  change (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
    (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
    Pi.single (.inr ((rootPairing A hs hp).reflectionPerm (s i)
      ((rootPairing A hs hp).reflectionPerm (s i) k))) 1=_
  rw [RootPairing.reflectionPerm_self]
  exact unit_fixed_of_pairing A hs hp b s K i k (by omega) (by omega)

theorem singer_weight_zero_one (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (k : Roots A) (hik : integerPairing A (s i:Roots A).val k.val=0)
    (hjk : integerPairing A (s j:Roots A).val k.val=1) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
  let x := (rootPairing A hs hp).reflectionPerm (s j) k
  have hix : integerPairing A (s i:Roots A).val x.val=1 := by
    rw [reflected_pair,hij,hik,hjk];norm_num
  have hjx : integerPairing A (s j:Roots A).val x.val= -1 := by
    rw [reflected_pair,(s j:Roots A).property,hjk];norm_num
  have hx := singer_weight_one_neg_one A hs hp b s K i j hij x hix hjx
  apply successor_fixed _ _ _ hx
  rw [singer_apply,weyl_root_column]
  change (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
    (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
    ((canonicalWeyl (realizationData A hs hp b s) K i : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inr ((rootPairing A hs hp).reflectionPerm (s j)
        ((rootPairing A hs hp).reflectionPerm (s j) k))) 1)=_
  rw [RootPairing.reflectionPerm_self,weyl_root_column,reflection_fixed A hs hp (s i) k hik]
  exact unit_fixed_of_pairing A hs hp b s K i k (by omega) (by omega)

theorem singer_weight_zero_neg_one (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (k : Roots A) (hik : integerPairing A (s i:Roots A).val k.val=0)
    (hjk : integerPairing A (s j:Roots A).val k.val= -1) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
  let x := (rootPairing A hs hp).reflectionPerm (s j) k
  have hix : integerPairing A (s i:Roots A).val x.val= -1 := by
    rw [reflected_pair,hij,hik,hjk];norm_num
  have hjx : integerPairing A (s j:Roots A).val x.val=1 := by
    rw [reflected_pair,(s j:Roots A).property,hjk];norm_num
  have hx := singer_second_block A hs hp b s K i j hij x hix hjx
  apply successor_fixed _ _ _ hx
  rw [singer_apply,weyl_root_column]
  change (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
    (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
    ((canonicalWeyl (realizationData A hs hp b s) K i : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inr ((rootPairing A hs hp).reflectionPerm (s j)
        ((rootPairing A hs hp).reflectionPerm (s j) k))) 1)=_
  rw [RootPairing.reflectionPerm_self,weyl_root_column,reflection_fixed A hs hp (s i) k hik]
  exact unit_fixed_of_pairing A hs hp b s K i k (by omega) (by omega)

theorem singer_weight_one_zero (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (k : Roots A) (hik : integerPairing A (s i:Roots A).val k.val=1)
    (hjk : integerPairing A (s j:Roots A).val k.val=0) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inr k) 1)=Pi.single (.inr k) 1 := by
  let l := (rootPairing A hs hp).reflectionPerm (s i) k
  let x := (rootPairing A hs hp).reflectionPerm (s j) l
  have hil : integerPairing A (s i:Roots A).val l.val= -1 := by
    rw [reflected_pair,(s i:Roots A).property,hik];norm_num
  have hjl : integerPairing A (s j:Roots A).val l.val=1 := by
    rw [reflected_pair,integer_symmetric A hs (s j:Roots A).val (s i:Roots A).val,hij,hik,hjk];norm_num
  have hix : integerPairing A (s i:Roots A).val x.val=0 := by
    rw [reflected_pair,hil,hjl,hij];norm_num
  have hjx : integerPairing A (s j:Roots A).val x.val= -1 := by
    rw [reflected_pair,(s j:Roots A).property,hjl];norm_num
  have hx := singer_weight_zero_neg_one A hs hp b s K i j hij x hix hjx
  apply successor_fixed _ _ _ hx
  rw [singer_apply,weyl_root_column]
  change (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
    (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
    ((canonicalWeyl (realizationData A hs hp b s) K i : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
      Pi.single (.inr ((rootPairing A hs hp).reflectionPerm (s j)
        ((rootPairing A hs hp).reflectionPerm (s j) l))) 1)=_
  rw [RootPairing.reflectionPerm_self,weyl_root_column]
  change (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
    (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
    Pi.single (.inr ((rootPairing A hs hp).reflectionPerm (s i)
      ((rootPairing A hs hp).reflectionPerm (s i) k))) 1=_
  rw [RootPairing.reflectionPerm_self]
  exact unit_fixed_of_pairing A hs hp b s K i k (by omega) (by omega)

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerOutside
