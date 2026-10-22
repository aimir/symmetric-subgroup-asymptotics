import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailLinearExtension
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularRootPlanes
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! The literal all-positive B subspace, its dimension, and the exact
first-axis/tail criterion. No maximal-isotropic orbit is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveSubspace
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBTailCoordinates
variable (K : Type) [Field K]

def positiveEmbedding (n : ℕ) : (Fin n → K) →ₗ[K] (Index n → K) where
  toFun x := Sum.elim (Sum.elim x (fun _=>0)) (fun _=>0)
  map_add' x y := by
    funext i
    rcases i with (i|i)|⟨⟩ <;> simp
  map_smul' a x := by
    funext i
    rcases i with (i|i)|⟨⟩ <;> simp

theorem positiveEmbedding_injective (n : ℕ) : Function.Injective (positiveEmbedding K n) := by
  intro x y h
  funext i
  exact congrFun h (pos n i)

def positiveSubspace (n : ℕ) : Submodule K (Index n → K) := (positiveEmbedding K n).range

theorem positiveSubspace_finrank (n : ℕ) : Module.finrank K (positiveSubspace K n)=n := by
  let e := LinearEquiv.ofInjective (positiveEmbedding K n) (positiveEmbedding_injective K n)
  simpa only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one] using e.finrank_eq.symm

theorem mem_positiveSubspace (n : ℕ) (v : Index n → K) :
    v∈positiveSubspace K n ↔ (∀i,v (neg n i)=0) ∧ v (middle n)=0 := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨fun _=>rfl,rfl⟩
  · rintro ⟨hn,hm⟩
    refine ⟨fun i=>v (pos n i),?_⟩
    funext i
    rcases i with (i|i)|⟨⟩
    · rfl
    · exact (hn i).symm
    · exact hm.symm

theorem positiveSubspace_singular (n : ℕ) :
    ∀v∈positiveSubspace K n,∀w∈positiveSubspace K n,(gram K n).toBilin' v w=0 := by
  rintro v ⟨x,rfl⟩ w ⟨y,rfl⟩
  simp [Matrix.toBilin'_apply,gram,positiveEmbedding,Fintype.sum_sum_type]

theorem first_mem_positiveSubspace (n : ℕ) :
    (Pi.single (pos (n+1) 0) 1 : Index (n+1) → K)∈positiveSubspace K (n+1) := by
  refine ⟨Pi.single 0 1,?_⟩
  funext i
  rcases i with (i|i)|⟨⟩ <;> simp [positiveEmbedding,pos,Pi.single_apply]

theorem mem_positiveSubspace_of_tail (n : ℕ) (v : Index (n+1) → K)
    (hn : v (neg (n+1) 0)=0) (ht : tailRestriction K n v∈positiveSubspace K n) :
    v∈positiveSubspace K (n+1) := by
  rw [mem_positiveSubspace] at ht ⊢
  refine ⟨?_,?_⟩
  · intro i
    refine Fin.cases hn (fun j=>?_) i
    simpa only [tailRestriction,tailIndex] using ht.1 j
  · simpa only [tailRestriction,tailIndex] using ht.2

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBPositiveSubspace
