import SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexSingularComponents
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! A vector outside a self-orthogonal space cuts out a genuine
codimension-one polar hyperplane, in every characteristic. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def polarHyperplane (Q : QuadraticForm K V) (P : Submodule K V) (u : V) : Submodule K V :=
  P ⊓ (Q.polarBilin u).ker

theorem polarHyperplane_finrank (Q : QuadraticForm K V) (P : Submodule K V)
    (hP : LinearMap.BilinForm.orthogonal Q.polarBilin P = P) (u : V) (hu : u ∉ P) :
    Module.finrank K (polarHyperplane Q P u) + 1 = Module.finrank K P := by
  let phi : Module.Dual K P := (Q.polarBilin u).comp P.subtype
  have hn : phi ≠ 0 := by
    intro hz
    apply hu
    rw [← hP]
    intro x hx
    have hh := congrArg (fun f : Module.Dual K P => f ⟨x, hx⟩) hz
    change Q.polarBilin u x = 0 at hh
    change QuadraticMap.polar Q x u = 0
    rw [QuadraticMap.polar_comm (Q : V → K) x u]
    exact hh
  have he : phi.ker.map P.subtype = polarHyperplane Q P u := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxP, hxk⟩
      exact ⟨⟨x, hxP⟩, hxk, rfl⟩
  have hd := Submodule.finrank_map_subtype_eq P phi.ker
  rw [he] at hd
  rw [hd]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hn

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDIndexTrialityD4PolarHyperplane
