import SymmetricSubgroupAsymptotics.CFSGSignedCartanReflections
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Literal Cartan-column transport for products of matrix units. The only
generator input is its explicit original Cartan column formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGCartanColumnTransport
open CFSGSignedCartanReflections
variable {I J R K : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R] [CommRing K]

def embed (e : I≃J) : (I→K)→ₗ[K](J⊕R→K) where
  toFun := fun x=>Sum.elim (x∘e.symm) 0
  map_add' := by intro x y;funext j;cases j <;> simp
  map_smul' := by intro a x;funext j;cases j <;> simp

theorem embed_single (e : I≃J) (j : I) :
    embed (R:=R) (K:=K) e (Pi.single j 1)=Pi.single (.inl (e j)) 1 := by
  funext k
  cases k with
  | inl k=>
    change (Pi.single j (1:K) : I→K) (e.symm k)=
      (Pi.single (Sum.inl (e j) : J⊕R) (1:K) : J⊕R→K) (Sum.inl k : J⊕R)
    by_cases hk : k=e j
    · subst k
      rw [e.symm_apply_apply]
      simp [Pi.single_apply]
    · have he : e.symm k≠j := by
        intro h
        exact hk ((congrArg e h).symm.trans (e.apply_symm_apply k)).symm
      simp [hk,he]
  | inr k=>simp [embed]

theorem step_column (A : Matrix I I ℤ) (i j : I) :
    ((Int.castRingHom K).mapMatrix (cartanStep A i))*ᵥPi.single j 1=
      Pi.single j 1-((|A i j|:ℤ):K) • Pi.single i 1 := by
  funext k
  simp only [Matrix.mulVec_single_one,Matrix.col_apply]
  change ((cartanStep A i k j : ℤ):K)=
    ((Pi.single j (1:K) : I→K)-((|A i j|:ℤ):K) • (Pi.single i (1:K) : I→K)) k
  by_cases hkj : k=j <;> by_cases hki : k=i <;>
    simp [cartanStep,Matrix.one_apply,Pi.single_apply,hkj,hki]

theorem generator_action (A : Matrix I I ℤ) (e : I≃J)
    (M : I→(Matrix (J⊕R) (J⊕R) K)ˣ)
    (hcol : ∀i j,(M i : Matrix (J⊕R) (J⊕R) K)*ᵥPi.single (.inl (e j)) 1=
      Pi.single (.inl (e j)) 1-((|A i j|:ℤ):K) • Pi.single (.inl (e i)) 1)
    (i : I) (x : I→K) :
    (M i : Matrix (J⊕R) (J⊕R) K)*ᵥembed e x=
      embed e (((Int.castRingHom K).mapMatrix (cartanStep A i))*ᵥx) := by
  have hh : (M i : Matrix (J⊕R) (J⊕R) K).mulVecLin.comp (embed e)=
      (embed e).comp (((Int.castRingHom K).mapMatrix (cartanStep A i)).mulVecLin) := by
    apply (Pi.basisFun K I).ext
    intro j
    simp only [LinearMap.comp_apply,Pi.basisFun_apply,Matrix.mulVecLin_apply,
      embed_single,step_column,map_sub,map_smul]
    exact hcol i j
  exact LinearMap.congr_fun hh x

def unitWord (M : I→(Matrix (J⊕R) (J⊕R) K)ˣ) : List I→(Matrix (J⊕R) (J⊕R) K)ˣ
  | []=>1
  | i::w=>M i*unitWord M w

theorem word_action (A : Matrix I I ℤ) (e : I≃J)
    (M : I→(Matrix (J⊕R) (J⊕R) K)ˣ)
    (hcol : ∀i j,(M i : Matrix (J⊕R) (J⊕R) K)*ᵥPi.single (.inl (e j)) 1=
      Pi.single (.inl (e j)) 1-((|A i j|:ℤ):K) • Pi.single (.inl (e i)) 1)
    (w : List I) (x : I→K) :
    (unitWord M w : Matrix (J⊕R) (J⊕R) K)*ᵥembed e x=
      embed e (((Int.castRingHom K).mapMatrix (cartanWord A w))*ᵥx) := by
  induction w with
  | nil=>simp only [unitWord,Units.val_one,cartanWord,map_one,Matrix.one_mulVec]
  | cons i w ih=>
    simp only [unitWord,Units.val_mul,cartanWord,map_mul,←Matrix.mulVec_mulVec]
    rw [ih,generator_action A e M hcol]

theorem word_fixes_cartan_of_lattice_identity (A : Matrix I I ℤ) (e : I≃J)
    (ε : I→ℤ) (hε : ∀i,ε i*ε i=1)
    (hA : ∀i j,ε i*|A i j|=A j i*ε j)
    (M : I→(Matrix (J⊕R) (J⊕R) K)ˣ)
    (hcol : ∀i j,(M i : Matrix (J⊕R) (J⊕R) K)*ᵥPi.single (.inl (e j)) 1=
      Pi.single (.inl (e j)) 1-((|A i j|:ℤ):K) • Pi.single (.inl (e i)) 1)
    (w : List I) (hw : latticeWord A w=1) (j : I) :
    (unitWord M w : Matrix (J⊕R) (J⊕R) K)*ᵥPi.single (.inl (e j)) 1=
      Pi.single (.inl (e j)) 1 := by
  rw [←embed_single e j,word_action A e M hcol,
    cartanWord_eq_one_of_latticeWord_eq_one A ε hε hA w hw,map_one,Matrix.one_mulVec]

end SymmetricSubgroupAsymptotics.CFSGCartanColumnTransport
