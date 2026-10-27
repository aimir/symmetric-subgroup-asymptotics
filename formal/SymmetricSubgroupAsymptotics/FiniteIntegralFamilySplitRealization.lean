import SymmetricSubgroupAsymptotics.SplitLinearTensorInjectivity
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Finite integral spanning plus literal coordinate extraction gives a
split injection, surviving EVERY commutative scalar extension. No odd-field,
flatness, rational-dimension or simplicity hypothesis is needed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteIntegralFamilySplitRealization
variable {J M N : Type*} [Fintype J] [DecidableEq J]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M→ₗ[ℤ]N) (v : J→M) (c : N→ₗ[ℤ](J→ℤ))

def combination : (J→ℤ)→ₗ[ℤ]M := Fintype.linearCombination ℤ v

theorem combination_surjective
    (hspan : Submodule.span ℤ (Set.range v)=⊤) :
    Function.Surjective (combination v) := by
  intro x
  have hx : x∈Submodule.span ℤ (Set.range v) := by rw [hspan]; trivial
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
  exact ⟨a,ha⟩

theorem coordinates_combination
    (hcoord : ∀ j,c (f (v j))=Pi.single j 1) (a : J→ℤ) :
    c (f (combination v a))=a := by
  change c (f (Fintype.linearCombination ℤ v a))=a
  rw [Fintype.linearCombination_apply]
  simp only [map_sum,map_smul,hcoord]
  funext j
  simp [Finset.sum_apply,hcoord,Pi.single_apply]

def leftInverse : N→ₗ[ℤ]M := (combination v).comp c

theorem leftInverse_spec (hspan : Submodule.span ℤ (Set.range v)=⊤)
    (hcoord : ∀ j,c (f (v j))=Pi.single j 1) :
    Function.LeftInverse (leftInverse v c) f := by
  intro x
  obtain ⟨a,rfl⟩ := combination_surjective v hspan x
  change combination v (c (f (combination v a)))=combination v a
  rw [coordinates_combination f v c hcoord]

theorem injective (hspan : Submodule.span ℤ (Set.range v)=⊤)
    (hcoord : ∀ j,c (f (v j))=Pi.single j 1) : Function.Injective f :=
  (leftInverse_spec f v c hspan hcoord).injective

theorem baseChange_injective (hspan : Submodule.span ℤ (Set.range v)=⊤)
    (hcoord : ∀ j,c (f (v j))=Pi.single j 1)
    (K : Type*) [CommRing K] : Function.Injective (f.baseChange K) :=
  SplitLinearTensorInjectivity.baseChange_injective f (leftInverse v c)
    (leftInverse_spec f v c hspan hcoord) K

end SymmetricSubgroupAsymptotics.FiniteIntegralFamilySplitRealization
