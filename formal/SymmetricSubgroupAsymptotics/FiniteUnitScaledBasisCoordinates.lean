import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring

/-! Exact coordinates on a unit-scaled subfamily of a genuine basis.
This does not assume the ambient map supplying the vectors is injective.
Only a literal basis embedding and nonzero scales are used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteUnitScaledBasisCoordinates
variable {J K V : Type*} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
    [AddCommGroup V] [Module ℚ V]
    (b : Module.Basis K ℚ V) (i : J↪K) (u : J→ℚ)

def vector (j : J) : V := u j • b (i j)

def coordinates : V→ₗ[ℚ](J→ℚ) where
  toFun v j:=(u j)⁻¹*b.repr v (i j)
  map_add' v w:=by
    funext j
    change (u j)⁻¹*b.repr (v+w) (i j)=
      (u j)⁻¹*b.repr v (i j)+(u j)⁻¹*b.repr w (i j)
    rw [map_add,Finsupp.add_apply,mul_add]
  map_smul' q v:=by
    funext j
    change (u j)⁻¹*b.repr (q • v) (i j)=q*((u j)⁻¹*b.repr v (i j))
    rw [map_smul,Finsupp.smul_apply,smul_eq_mul]
    ring

variable (hu : ∀j,u j≠0)
include hu

theorem coordinates_vector (j : J) :
    coordinates b i u (vector b i u j)=Pi.single j 1 := by
  funext k
  change (u k)⁻¹*b.repr (u j • b (i j)) (i k)= (Pi.single j (1:ℚ) : J→ℚ) k
  rw [map_smul,Finsupp.smul_apply,Module.Basis.repr_self]
  by_cases hkj : k=j
  · subst k
    simp only [Finsupp.single_eq_same,smul_eq_mul,mul_one,
      inv_mul_cancel₀ (hu j),Pi.single_eq_same]
  · have h : i k≠i j := fun he=>hkj (i.injective he)
    simp only [Finsupp.single_eq_of_ne h,smul_eq_mul,mul_zero,Pi.single_eq_of_ne hkj]

theorem basis_mem_span (j : J) :
    b (i j)∈Submodule.span ℚ (Set.range (vector b i u)) := by
  have hv : vector b i u j∈Submodule.span ℚ (Set.range (vector b i u)) :=
    Submodule.subset_span ⟨j,rfl⟩
  have h := Submodule.smul_mem (Submodule.span ℚ (Set.range (vector b i u))) (u j)⁻¹ hv
  simpa only [vector,smul_smul,inv_mul_cancel₀ (hu j),one_smul] using h

theorem mem_span_of_support (v : V)
    (h : ∀k,b.repr v k≠0→∃j,i j=k) :
    v∈Submodule.span ℚ (Set.range (vector b i u)) := by
  rw [←b.sum_repr v]
  apply Submodule.sum_mem
  intro k hk
  by_cases hz : b.repr v k=0
  · simp only [hz,zero_smul,Submodule.zero_mem]
  · obtain ⟨j,rfl⟩:=h k hz
    exact Submodule.smul_mem _ _ (basis_mem_span b i u hu j)

/-- The actual coordinate map reconstructs precisely on the span of the
scaled subfamily; no ambient/source injectivity is required. -/
theorem reconstruction (v : V)
    (hv : v∈Submodule.span ℚ (Set.range (vector b i u))) :
    Fintype.linearCombination ℚ (vector b i u) (coordinates b i u v)=v := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
  · intro v hv
    obtain ⟨j,rfl⟩:=hv
    rw [coordinates_vector b i u hu]
    simp [Fintype.linearCombination_apply,Pi.single_apply]
  · simp only [map_zero]
  · intro x y _ _ hx hy
    rw [map_add,map_add,hx,hy]
  · intro q x _ hx
    rw [map_smul,map_smul,hx]

end SymmetricSubgroupAsymptotics.FiniteUnitScaledBasisCoordinates
