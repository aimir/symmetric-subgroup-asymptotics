import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerAdjoint
import SymmetricSubgroupAsymptotics.CFSGLinearFixedComplement

/-! Every Cartan column of the actual Singer word has order dividing
seven: its complement to the two A2 Cartan columns is fixed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerCartan
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckSingerFirstBlock CFSGNormTwoGeckFieldRootSteps
open CFSGNormTwoGeckFieldRootColumns CFSGNormTwoGeckFieldWeylCartan
open CFSGNormTwoGeckOrthogonalColumns CFSGNormTwoGeckSingerAdjoint
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem singer_cartan_seven (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1)
    (gamma : Roots A)
    (hg : (rootPairing A hs hp).root gamma=
      (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root (s j))
    (k : b.support) :
    ((singerOperator A hs hp b s K i j)^7) (Pi.single (.inl k) 1)=Pi.single (.inl k) 1 := by
  let x : b.support⊕Roots A→K := Pi.single (.inl k) 1
  let u : b.support⊕Roots A→K := Pi.single (.inl (s i)) 1
  let v : b.support⊕Roots A→K := Pi.single (.inl (s j)) 1
  let e : b.support⊕Roots A→K := Pi.single (.inr (s i:Roots A)) 1
  let a : K := ((|b.cartanMatrix (s i) k|:ℤ):K)
  let c : K := ((|b.cartanMatrix (s j) k|:ℤ):K)
  let p : Module.End K (b.support⊕Roots A→K) := Matrix.toLinAlgEquiv'
    (canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
  let q : Module.End K (b.support⊕Roots A→K) := Matrix.toLinAlgEquiv'
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
  let t : Module.End K (b.support⊕Roots A→K) := Matrix.toLinAlgEquiv'
    (canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
  have hsub (x y : b.support⊕Roots A→K) : x-y=x+y := by
    ext z
    exact CharTwo.sub_eq_add (x z) (y z)
  have habs2 : |(2:ℤ)|=2 := by decide
  have habs1 : |(-1:ℤ)|=1 := by decide
  have hcij : b.cartanMatrix (s i) (s j)= -1 := by
    rw [←integerPairing_eq_cartan A hs hp b];exact hij
  have hcji : b.cartanMatrix (s j) (s i)= -1 := by
    rw [←integerPairing_eq_cartan A hs hp b,integer_symmetric A hs];exact hij
  have hpx : p x=x+a • e := unit_cartan_general A hs hp b s K i k
  have hpu : p u=u := by
    simpa only [CharP.ofNat_eq_zero K 2,zero_smul,add_zero] using unit_cartan A hs hp b s K i
  have hpv : p v=v+e := by
    simpa only [hcij,habs1,Int.cast_one,one_smul] using
      unit_cartan_general A hs hp b s K i (s j)
  have hqx : q x=x+a • u := by
    simpa only [hsub] using weyl_cartan_general A hs hp b s K i k
  have hqu : q u=u := by
    simpa only [RootPairing.Base.cartanMatrix_apply_same,habs2,Int.cast_ofNat,
      CharP.ofNat_eq_zero K 2,zero_smul,sub_zero] using weyl_cartan_general A hs hp b s K i (s i)
  have hqv : q v=v+u := by
    simpa only [hcij,habs1,Int.cast_one,one_smul,hsub] using
      weyl_cartan_general A hs hp b s K i (s j)
  have htx : t x=x+c • v := by
    simpa only [hsub] using weyl_cartan_general A hs hp b s K j k
  have htu : t u=u+v := by
    simpa only [hcji,habs1,Int.cast_one,one_smul,hsub] using
      weyl_cartan_general A hs hp b s K j (s i)
  have htv : t v=v := by
    simpa only [RootPairing.Base.cartanMatrix_apply_same,habs2,Int.cast_ofNat,
      CharP.ofNat_eq_zero K 2,zero_smul,sub_zero] using weyl_cartan_general A hs hp b s K j (s j)
  have hc := CFSGLinearFixedComplement.complement_fixed p q t x u v e a c
    hpx hpu hpv hqx hqu hqv htx htu htv
  have hfix : singerOperator A hs hp b s K i j (x-c • u-a • v)=x-c • u-a • v := by
    change ((canonicalRoot (realizationData A hs hp b s) K false i 1 : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K))*ᵥ
      (x-c • u-a • v)=_
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
    exact hc
  have hu : ((singerOperator A hs hp b s K i j)^7) u=u :=
    singer_adjoint_seven A hs hp b s K i j hij gamma hg 0
  have hv : ((singerOperator A hs hp b s K i j)^7) v=v :=
    singer_adjoint_seven A hs hp b s K i j hij gamma hg 1
  exact CFSGLinearFixedComplement.power_fixed_of_complement
    (singerOperator A hs hp b s K i j) 7 x u v a c hfix hu hv

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckSingerCartan
