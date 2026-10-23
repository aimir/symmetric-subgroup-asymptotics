import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Fin.VecNotation

/-! The actual independent basis pair of a two-dimensional submodule,
for an arbitrary ambient vector space rather than a function carrier. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearBasis
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]

theorem exists_pair (P : Submodule K V) (hdim : Module.finrank K P = 2) :
    ∃ v ∈ P, ∃ w ∈ P, v ≠ 0 ∧ (∀ c : K, w ≠ c • v) ∧
      Submodule.span K {v, w} = P := by
  let b : Module.Basis (Fin 2) K P := Module.finBasisOfFinrankEq K P hdim
  let v : V := (b 0).val
  let w : V := (b 1).val
  have hv : v ≠ 0 := by
    intro he
    exact b.ne_zero 0 (Subtype.ext he)
  have hnot (c : K) : w ≠ c • v := by
    intro he
    have hh : b 1 = c • b 0 := Subtype.ext he
    have hr := congrArg (fun z : P => b.repr z (1 : Fin 2)) hh
    simp at hr
  refine ⟨v, (b 0).property, w, (b 1).property, hv, hnot, ?_⟩
  have hvs : v ∈ Submodule.span K {v, w} := Submodule.subset_span (Or.inl rfl)
  have hws : w ∈ Submodule.span K {v, w} := Submodule.subset_span (Or.inr rfl)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x (hx | hx)
    · rcases hx with rfl; exact (b 0).property
    · rcases hx with rfl; exact (b 1).property
  · intro x hx
    let x0 : P := ⟨x, hx⟩
    have he : x = b.repr x0 0 • v + b.repr x0 1 • w := by
      have hh := congrArg Subtype.val (b.sum_repr x0).symm
      simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul] using hh
    rw [he]
    exact (Submodule.span K {v, w}).add_mem
      ((Submodule.span K {v, w}).smul_mem _ hvs)
      ((Submodule.span K {v, w}).smul_mem _ hws)

end SymmetricSubgroupAsymptotics.CFSGTwoDimensionalLinearBasis
