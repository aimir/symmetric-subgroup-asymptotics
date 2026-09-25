import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
import Mathlib.GroupTheory.Rank

/-! Evaluation on an actual generating set bounds the whole prime
character space, hence every relative head, by the group generator rank. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
variable (p : ℕ) [Fact p.Prime]
variable {G : Type*} [Group G]

theorem primeCharacterRank_le_generators (S : Finset G)
    (hS : Subgroup.closure (S:Set G)=⊤) :
    Module.finrank (ZMod p) (PrimeCharacters p G)≤S.card := by
  let f : PrimeCharacters p G →ₗ[ZMod p] (S → ZMod p) := {
    toFun := fun χ x => χ (Additive.ofMul (x:G))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro χ ψ h
    apply AddMonoidHom.toMultiplicativeRight.injective
    apply MonoidHom.eq_of_eqOn_dense hS
    intro g hg
    exact congrArg Multiplicative.ofAdd (congrFun h ⟨g,hg⟩)
  have h := f.finrank_le_finrank_of_injective hf
  simpa only [Module.finrank_pi,Module.finrank_self,Finset.sum_const,
    Finset.card_univ,Fintype.card_coe,Nat.nsmul_eq_mul,mul_one] using h

theorem primeCharacterRank_le_groupRank [Group.FG G] :
    Module.finrank (ZMod p) (PrimeCharacters p G)≤Group.rank G := by
  obtain ⟨S,hcard,hS⟩ := Group.rank_spec G
  simpa only [hcard] using primeCharacterRank_le_generators p S hS

theorem primeRelativeHead_le_groupRank {A : Type*} [Group A]
    (N : Subgroup A) [N.Normal] [Finite N] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N)≤Group.rank N :=
  (Submodule.finrank_le _).trans (primeCharacterRank_le_groupRank p)

end SymmetricSubgroupAsymptotics
