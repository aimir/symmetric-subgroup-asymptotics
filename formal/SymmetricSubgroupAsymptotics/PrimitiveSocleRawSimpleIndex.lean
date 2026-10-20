import SymmetricSubgroupAsymptotics.SemisimpleNormalChart
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Literal inner/outer automorphism groups and the two ordinary simple
index inequalities of Ballester-Bolinches--Esteban-Romero--Jimenez-Seral,
arXiv2203.16976v2, Theorem A(4), p4. No primitive quotient action or
primitive-degree inequality is a field of this input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure

variable (T : Type) [Group T]

def Inner : Subgroup (MulAut T) := (MulAut.conj : T →* MulAut T).range

instance innerNormal : (Inner T).Normal where
  conj_mem := by
    rintro f ⟨t,rfl⟩ a
    refine ⟨a t,?_⟩
    apply MulEquiv.ext
    intro x
    change (a t)*x*(a t)⁻¹=a (t*a.symm x*t⁻¹)
    simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]

abbrev Outer := MulAut T ⧸ Inner T

/-- A value equal to the least proper subgroup index; not an unconstrained
numerical parameter or an imported primitive compression budget. -/
def LeastProperIndex (ell : ℕ) : Prop :=
  (∃ H : Subgroup T,H≠⊤ ∧ H.index=ell) ∧
    ∀ H : Subgroup T,H≠⊤ → ell≤H.index

/-- Exactly the two numerical assertions of Theorem A(4), on an actual
nonabelian finite simple group and its actual least proper index. -/
def PublishedSimpleIndexBounds : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
    ¬ IsMulCommutative S → ∀ ell : ℕ,LeastProperIndex S ell →
      ell^2<Nat.card S ∧ (Nat.card (Outer S) : ℝ)≤3*Real.logb 2 ell

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
