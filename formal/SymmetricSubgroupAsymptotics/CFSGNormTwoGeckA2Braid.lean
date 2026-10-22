import SymmetricSubgroupAsymptotics.CFSGNormTwoA2ReflectionCube
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckFieldWeylCartan
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalColumns
import SymmetricSubgroupAsymptotics.CFSGLinearA2ReflectionCube

/-! The actual adjacent Geck Weyl words satisfy the A2 braid cube in
characteristic two. Every root and Cartan column is proved directly. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckA2Braid
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckWeylCharTwoRoots CFSGNormTwoGeckFieldWeylCartan
open CFSGNormTwoGeckOrthogonalColumns
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

theorem cartan_cube (K : Type*) [CommRing K] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1) (k : b.support) :
    (((canonicalWeyl (realizationData A hs hp b s) K i : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*
      (canonicalWeyl (realizationData A hs hp b s) K j : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K))^3)*ᵥPi.single (.inl k) 1=
        Pi.single (.inl k) 1 := by
  let q : Module.End K (b.support⊕Roots A→K) := Matrix.toLinAlgEquiv'
    (canonicalWeyl (realizationData A hs hp b s) K i : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
  let t : Module.End K (b.support⊕Roots A→K) := Matrix.toLinAlgEquiv'
    (canonicalWeyl (realizationData A hs hp b s) K j : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)
  let x : b.support⊕Roots A→K := Pi.single (.inl k) 1
  let u : b.support⊕Roots A→K := Pi.single (.inl (s i)) 1
  let v : b.support⊕Roots A→K := Pi.single (.inl (s j)) 1
  let a : K := ((|b.cartanMatrix (s i) k|:ℤ):K)
  let c : K := ((|b.cartanMatrix (s j) k|:ℤ):K)
  have habs2 : |(2:ℤ)|=2 := by decide
  have habs1 : |(-1:ℤ)|=1 := by decide
  have hcij : b.cartanMatrix (s i) (s j)= -1 := by
    rw [←integerPairing_eq_cartan A hs hp b];exact hij
  have hcji : b.cartanMatrix (s j) (s i)= -1 := by
    rw [←integerPairing_eq_cartan A hs hp b,integer_symmetric A hs];exact hij
  have hqx : q x=x-a • u := weyl_cartan_general A hs hp b s K i k
  have htx : t x=x-c • v := weyl_cartan_general A hs hp b s K j k
  have hqu' : q u=u-(2:K) • u := by
    simpa only [RootPairing.Base.cartanMatrix_apply_same,habs2,Int.cast_ofNat] using
      weyl_cartan_general A hs hp b s K i (s i)
  have hqu : q u= -u := by rw [hqu'];module
  have htv' : t v=v-(2:K) • v := by
    simpa only [RootPairing.Base.cartanMatrix_apply_same,habs2,Int.cast_ofNat] using
      weyl_cartan_general A hs hp b s K j (s j)
  have htv : t v= -v := by rw [htv'];module
  have hqv : q v=v-u := by
    simpa only [hcij,habs1,Int.cast_one,one_smul] using
      weyl_cartan_general A hs hp b s K i (s j)
  have htu : t u=u-v := by
    simpa only [hcji,habs1,Int.cast_one,one_smul] using
      weyl_cartan_general A hs hp b s K j (s i)
  have hh := CFSGLinearA2ReflectionCube.cube q t x u v a c hqx hqu hqv htx htu htv
  have he : Matrix.toLinAlgEquiv'
      (((canonicalWeyl (realizationData A hs hp b s) K i : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) K)*
        (canonicalWeyl (realizationData A hs hp b s) K j : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) K))^3)=(q*t)^3 := by
    rw [map_pow,map_mul]
  calc
    _=((q*t)^3) x := congrArg (fun f : Module.End K (b.support⊕Roots A→K)=>f x) he
    _=x := hh

theorem canonical_weyl_product_cube (K : Type*) [CommRing K] [CharP K 2] (i j : Fin r)
    (hij : integerPairing A (s i:Roots A).val (s j:Roots A).val= -1) :
    (canonicalWeyl (realizationData A hs hp b s) K i*
      canonicalWeyl (realizationData A hs hp b s) K j)^3=1 := by
  apply Units.ext
  change (((canonicalWeyl (realizationData A hs hp b s) K i : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*
    (canonicalWeyl (realizationData A hs hp b s) K j : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K))^3)=1
  apply Matrix.ext_of_mulVec_single
  intro z
  rw [Matrix.one_mulVec]
  rcases z with k|k
  · exact cartan_cube A hs hp b s K i j hij k
  · simp only [pow_succ,pow_zero,Matrix.one_mul,←Matrix.mulVec_mulVec,weyl_root_column,
      CFSGNormTwoA2ReflectionCube.adjacent_reflection_cube A hs hp (s i) (s j) hij]

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckA2Braid
