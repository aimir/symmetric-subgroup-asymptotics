import SymmetricSubgroupAsymptotics.FiniteIntegralFamilySplitRealization

/-! Primitive realization coordinates split the finite source span inside
the source module. In a torsion-free source, this span is saturated.
Global spanning or global realization injectivity is NOT assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteIntegralFamilySaturatedSpan
open FiniteIntegralFamilySplitRealization
variable {J M N : Type*} [Fintype J] [DecidableEq J]
    [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
    (f : M→ₗ[ℤ]N) (v : J→M) (c : N→ₗ[ℤ](J→ℤ))
    (hcoord : ∀ j,c (f (v j))=Pi.single j 1)

def projection : M→ₗ[ℤ]M := (leftInverse v c).comp f

theorem projection_mem (x : M) :
    projection f v c x∈Submodule.span ℤ (Set.range v) := by
  change Fintype.linearCombination ℤ v (c (f x))∈Submodule.span ℤ (Set.range v)
  rw [Fintype.linearCombination_apply]
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

include hcoord

theorem projection_vector (j : J) : projection f v c (v j)=v j := by
  change Fintype.linearCombination ℤ v (c (f (v j)))=v j
  rw [hcoord,Fintype.linearCombination_apply_single]
  exact (Int.cast_smul_eq_zsmul ℤ (1:ℤ) (v j)).trans (one_zsmul (v j))

theorem projection_fix {x : M} (hx : x∈Submodule.span ℤ (Set.range v)) :
    projection f v c x=x := by
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨j,rfl⟩:=hx; exact projection_vector f v c hcoord j
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add,hx,hy]
  | smul a x _ hx => rw [LinearMap.map_smul,hx]

theorem saturated (hcancel : ∀ n : ℕ,n≠0→Function.Injective (fun x : M=>n • x))
    (n : ℕ) (hn : n≠0) (x : M)
    (hx : n • x∈Submodule.span ℤ (Set.range v)) :
    x∈Submodule.span ℤ (Set.range v) := by
  have hp:=projection_fix f v c hcoord hx
  rw [map_nsmul] at hp
  have he:=hcancel n hn hp
  rw [←he]
  exact projection_mem f v c x

end SymmetricSubgroupAsymptotics.FiniteIntegralFamilySaturatedSpan
