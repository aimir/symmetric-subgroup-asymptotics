import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateNormalSimpleRootGeneration
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckWeylLatticeLinear

/-! Actual simple-reflection words act transitively on the original
simple-root labels of a connected norm-two coordinate Cartan model.
The adjacent two-reflection identity is proved on the integer lattice,
before any coefficient-field base change. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootOrbit
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGNormTwoLatticeReflections CFSGNormTwoGeckLatticeDegree
open CFSGNormTwoGeckWeylLatticeLinear CFSGNormTwoCoordinateDominantSupport
open CFSGNormTwoCoordinateNormalSimpleRootGeneration

private theorem reflection_pair {V : Type*} [AddCommGroup V]
    (B : LinearMap.BilinForm ℤ V) (a b : V)
    (haa : B a a=2) (hab : B a b= -1) (hba : B b a= -1) :
    reflection B a (reflection B b a)=b := by
  have hinner : reflection B b a=a+b := by
    rw [reflection,hab,neg_one_smul]
    abel
  have hpair : B (a+b) a=1 := by
    simp only [map_add,LinearMap.add_apply,haa,hba]
    norm_num
  rw [hinner,reflection,hpair,one_smul]
  abel

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (hd : ∀i,A i i=2)
    (hs : A.transpose=A) (hp : (rationalMatrix A).PosDef)
    (ho : ∀i j,i≠j→A i j≤0)
    [Fintype (Roots A)] [DecidableEq (Roots A)]
    [(rootPairing A hs hp).IsReduced] [(rootPairing A hs hp).IsIrreducible]
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

theorem adjacent_simple_root_word (i j : Fin r) (hij : A i j= -1) (hji : A j i= -1) :
    wordLinear A hs hp b₀ s₀ [i,j] (s₀ i : Roots A).val=(s₀ j : Roots A).val := by
  have hii : integerPairing A (s₀ i : Roots A).val (s₀ i : Roots A).val=2 :=
    (s₀ i : Roots A).property
  have hij' : integerPairing A (s₀ i : Roots A).val (s₀ j : Roots A).val= -1 := by
    change Matrix.toBilin' A (Pi.single i (1:ℤ)) (Pi.single j (1:ℤ))= -1
    rw [Matrix.toBilin'_single]
    exact hij
  have hji' : integerPairing A (s₀ j : Roots A).val (s₀ i : Roots A).val= -1 := by
    change Matrix.toBilin' A (Pi.single j (1:ℤ)) (Pi.single i (1:ℤ))= -1
    rw [Matrix.toBilin'_single]
    exact hji
  change reflection (integerPairing A) (s₀ i : Roots A).val
    (reflection (integerPairing A) (s₀ j : Roots A).val (s₀ i : Roots A).val)=_
  exact reflection_pair (integerPairing A) _ _ hii hij' hji'

include hd hs hp ho in
theorem exists_word_simple_to_simple (i j : Fin r) :
    ∃w : List (Fin r),wordLinear A hs hp b₀ s₀ w (s₀ i : Roots A).val=(s₀ j : Roots A).val := by
  apply coordinate_cartan_induction A hd hs hp ho
    (fun j=>∃w : List (Fin r),wordLinear A hs hp b₀ s₀ w (s₀ i : Roots A).val=(s₀ j : Roots A).val)
    i j
  · exact ⟨[],rfl⟩
  · intro a b ha hab
    by_cases heq : a=b
    · subst b
      exact ha
    have hba := offdiagonal_nonzero_eq_neg_one A hd hs hp ho b a (Ne.symm heq) hab
    have hab' : A a b= -1 := by
      have he : A a b=A b a := congrFun (congrFun hs b) a
      exact he.trans hba
    obtain ⟨w,hw⟩ := ha
    refine ⟨[a,b]++w,?_⟩
    rw [wordLinear_append]
    change wordLinear A hs hp b₀ s₀ [a,b]
      (wordLinear A hs hp b₀ s₀ w (s₀ i : Roots A).val)=(s₀ b : Roots A).val
    rw [hw]
    exact adjacent_simple_root_word A hd hs hp ho a b hab' hba

end SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateSimpleRootOrbit
