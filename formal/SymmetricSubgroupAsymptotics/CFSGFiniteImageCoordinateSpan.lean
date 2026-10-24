import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! A finite image-coordinate table proves injectivity on exactly the
span of the displayed source family. It makes no assertion that this
span is the entire source. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGFiniteImageCoordinateSpan
variable {R I M N:Type*} [CommRing R] [Fintype I] [DecidableEq I]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f:M→ₗ[R]N) (v:I→M) (c:N→ₗ[R](I→R))
    (hc:∀i,c (f (v i))=Pi.single i 1)

include hc

theorem coordinates_combination (a:I→R) :
    c (f (Fintype.linearCombination R v a))=a := by
  change c (f (∑i,a i • v i))=a
  rw [map_sum,map_sum]
  simp only [map_smul,hc]
  funext j
  simp [Finset.sum_apply,Pi.single_apply,smul_eq_mul]

theorem injective_on_span : Set.InjOn f (Submodule.span R (Set.range v):Set M) := by
  intro x hx y hy he
  have hr:(Fintype.linearCombination R v).range=Submodule.span R (Set.range v):=
    Fintype.range_linearCombination R v
  have hxr:x∈(Fintype.linearCombination R v).range:=by rw [hr];exact hx
  have hyr:y∈(Fintype.linearCombination R v).range:=by rw [hr];exact hy
  obtain ⟨a,ha⟩:=hxr
  obtain ⟨b,hb⟩:=hyr
  have hab:=congrArg c he
  rw [←ha,←hb,coordinates_combination f v c hc,coordinates_combination f v c hc] at hab
  exact ha.symm.trans ((congrArg (Fintype.linearCombination R v) hab).trans hb)

end SymmetricSubgroupAsymptotics.CFSGFiniteImageCoordinateSpan
