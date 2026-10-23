import SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatCover

/-! A group-generic word-cell closure constructor requiring only that the
actual simple Weyl squares lie in B. No order-four presentation, abstract
Coxeter group, or supplied Bruhat decomposition is needed. The concrete
local left-simple multiplication step remains an explicit obligation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatSquareCover
open CFSGWeylWordBruhatCover
variable {G I : Type*} [Group G]

theorem closure_le_wordCells (B : Subgroup G) (simple : I → G)
    (hsquare : ∀ i,simple i*simple i∈B)
    (hstep : ∀ (i : I) (w : List I) (b : G),b∈B →
      WordCells B simple (simple i*b*wordValue simple w)) :
    ∀ g∈Subgroup.closure ((B:Set G)∪Set.range simple),WordCells B simple g := by
  intro g hg
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨[],1,B.one_mem,1,B.one_mem,by simp [wordValue]⟩
  | mul_left x hx y hy ih =>
    rcases hx with hx|⟨i,rfl⟩
    · exact wordCells_left_borel B simple hx ih
    · exact wordCells_left_simple B simple hstep i ih
  | inv_mul_cancel x hx y hy ih =>
    rcases hx with hx|⟨i,rfl⟩
    · exact wordCells_left_borel B simple (B.inv_mem hx) ih
    · have hinv : (simple i)⁻¹=(simple i*simple i)⁻¹*simple i := by group
      rw [hinv]
      have hh := wordCells_left_borel B simple (B.inv_mem (hsquare i))
        (wordCells_left_simple B simple hstep i ih)
      simpa only [mul_assoc] using hh

end SymmetricSubgroupAsymptotics.CFSGWeylWordBruhatSquareCover
