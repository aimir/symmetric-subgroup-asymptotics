import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedWeylPairs

/-! Literal rank-one torus words and their columns. The quotient of the
parameterized Weyl words fixes every Cartan column and is diagonal on
each actual root string, without dividing by a Cartan integer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedTorus
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing CFSGNormTwoGeckColumns
open CFSGNormTwoGeckIntegralRealization CFSGSerreQuadraticMatrix
open CFSGNormTwoGeckParameterizedWeyl CFSGNormTwoGeckParameterizedWeylPairs
variable {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℤ) (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    [Fintype (Roots A)] [DecidableEq (Roots A)] [(rootPairing A hs hp).IsIrreducible]
    (b : (rootPairing A hs hp).Base) {r : ℕ} (s : Fin r≃b.support)

def parameterTorus (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ :=
  parameterWeyl A hs hp b s K i t*(parameterWeyl A hs hp b s K i 1)⁻¹

theorem torus_weyl_column (K : Type*) [Field K] (i : Fin r) (t : Kˣ)
    (v : b.support⊕Roots A→K) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥ
        ((parameterWeyl A hs hp b s K i 1 : Matrix
          (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥv)=
      (parameterWeyl A hs hp b s K i t : Matrix
        (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥv := by
  rw [Matrix.mulVec_mulVec]
  have hh : parameterTorus A hs hp b s K i t*parameterWeyl A hs hp b s K i 1=
      parameterWeyl A hs hp b s K i t := by
    simp only [parameterTorus,mul_assoc,inv_mul_cancel,mul_one]
  exact congrArg (fun u : (Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)ˣ=>
    (u : Matrix (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥv) hh

theorem torus_triple (K : Type*) [Field K] (i : Fin r) (t : Kˣ) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl (s i)) 1=
        Pi.single (.inl (s i)) 1 ∧
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (s i:Roots A)) 1=
        (t:K)^2 • Pi.single (.inr (s i:Roots A)) 1 ∧
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr (negativeIndex A hs hp (s i))) 1=
        ((t:K)⁻¹)^2 • Pi.single (.inr (negativeIndex A hs hp (s i))) 1 := by
  have h1 := parameterWeyl_triple A hs hp b s K i (1:Kˣ)
  have ht := parameterWeyl_triple A hs hp b s K i t
  constructor
  · have hh := torus_weyl_column A hs hp b s K i t (Pi.single (.inl (s i)) 1)
    rw [h1.1,ht.1,Matrix.mulVec_neg] at hh
    exact neg_injective hh
  · constructor
    · have hh := torus_weyl_column A hs hp b s K i t
        (Pi.single (.inr (negativeIndex A hs hp (s i))) 1)
      simpa only [h1.2.2,ht.2.2,Units.val_one,one_pow,one_smul] using hh
    · have hh := torus_weyl_column A hs hp b s K i t
        (Pi.single (.inr (s i:Roots A)) 1)
      simpa only [h1.2.1,ht.2.1,Units.val_one,inv_one,one_pow,one_smul] using hh

theorem torus_cartan (K : Type*) [Field K] (i : Fin r) (t : Kˣ) (j : b.support) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inl j) 1=
        Pi.single (.inl j) 1 := by
  have hh := torus_weyl_column A hs hp b s K i t (Pi.single (.inl j) 1)
  rw [parameterWeyl_cartan,parameterWeyl_cartan,Matrix.mulVec_sub,Matrix.mulVec_smul,
    (torus_triple A hs hp b s K i t).1] at hh
  have hc := congrArg (fun v : b.support⊕Roots A→K=>
    v+((|b.cartanMatrix (s i) j|:ℤ):K) • Pi.single (.inl (s i)) 1) hh
  simpa only [sub_add_cancel] using hc

theorem torus_pair (K : Type*) [Field K] (i : Fin r) (j k : Roots A) (t : Kˣ)
    (hk : (rootPairing A hs hp).root k=
      (rootPairing A hs hp).root (s i)+(rootPairing A hs hp).root j) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        (t:K)⁻¹ • Pi.single (.inr j) 1 ∧
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr k) 1=
        (t:K) • Pi.single (.inr k) 1 := by
  have h1 := parameterWeyl_pair A hs hp b s K i j k (1:Kˣ) hk
  have ht := parameterWeyl_pair A hs hp b s K i j k t hk
  constructor
  · have hh := torus_weyl_column A hs hp b s K i t (Pi.single (.inr k) 1)
    simp only [h1.2,ht.2,Units.val_one,inv_one,neg_smul,one_smul,Matrix.mulVec_neg] at hh
    exact neg_injective hh
  · have hh := torus_weyl_column A hs hp b s K i t (Pi.single (.inr j) 1)
    simpa only [h1.1,ht.1,Units.val_one,one_smul] using hh

theorem torus_fixed (K : Type*) [Field K] (i : Fin r) (j : Roots A) (t : Kˣ)
    (hj : integerPairing A (s i:Roots A).val j.val=0) :
    (parameterTorus A hs hp b s K i t : Matrix
      (b.support⊕Roots A) (b.support⊕Roots A) K)*ᵥPi.single (.inr j) 1=
        Pi.single (.inr j) 1 := by
  have hh := torus_weyl_column A hs hp b s K i t (Pi.single (.inr j) 1)
  rw [parameterWeyl_fixed A hs hp b s K i j 1 hj,
    parameterWeyl_fixed A hs hp b s K i j t hj] at hh
  exact hh

end SymmetricSubgroupAsymptotics.CFSGNormTwoGeckParameterizedTorus
