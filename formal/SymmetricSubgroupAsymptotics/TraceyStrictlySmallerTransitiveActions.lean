import SymmetricSubgroupAsymptotics.TraceyAffineInducedModuleInput
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators
import Mathlib.Algebra.Group.Action.End
import Mathlib.Data.Finite.Perm

/-! Independent strictly-smaller-degree transport for the coarse
transitive ordinary-generator induction. Unlike sharp MN induction, the
hypothesis concerns only faithful transitive actions, has no S3 exception,
and is never supplied by a global Tracey theorem. The actual original
group and degree are retained through its literal permutation image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions

/-- The literal coarse rank statement only at degrees strictly below n. -/
def SmallerTransitiveRankBound (n : ℕ) : Prop :=
  ∀ (k : ℕ), k < n → ∀ J : Subgroup (Equiv.Perm (Fin k)), 2 ≤ k →
    MulAction.IsPretransitive J (Fin k) →
      MarkedC4.genRank J ≤ traceyPermutationGeneratorCeiling k

theorem of_subgroup_generators (n : ℕ)
    (hbelow : ∀ (k : ℕ), k < n → ∀ J : Subgroup (Equiv.Perm (Fin k)), 2 ≤ k →
      MulAction.IsPretransitive J (Fin k) →
        ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
          S.card ≤ traceyPermutationGeneratorCeiling k) :
    SmallerTransitiveRankBound n := by
  intro k hk J hk2 htrans
  obtain ⟨S,hgen,hcard⟩ := hbelow k hk J hk2 htrans
  exact (MarkedC4.genRank_le hgen).trans hcard

theorem rank_of_faithful_transitive_action (n : ℕ) (hbelow : SmallerTransitiveRankBound n)
    (H Y : Type) [Group H] [Finite H] [Finite Y] [MulAction H Y] [FaithfulSMul H Y]
    [MulAction.IsPretransitive H Y] (hY : 2 ≤ Nat.card Y) (hlt : Nat.card Y < n) :
    MarkedC4.genRank H ≤ traceyPermutationGeneratorCeiling (Nat.card Y) := by
  let ePoint := Finite.equivFin Y
  let f : H →* Equiv.Perm (Fin (Nat.card Y)) :=
    ePoint.permCongrHom.toMonoidHom.comp (MulAction.toPermHom H Y)
  have hf : Function.Injective f :=
    ePoint.permCongrHom.injective.comp MulAction.toPerm_injective
  let e : H ≃* f.range := MonoidHom.ofInjective (f := f) hf
  letI : MulAction.IsPretransitive f.range (Fin (Nat.card Y)) := ⟨by
    intro x y
    obtain ⟨h,hh⟩ := MulAction.exists_smul_eq H (ePoint.symm x) (ePoint.symm y)
    refine ⟨⟨f h,h,rfl⟩,?_⟩
    change ePoint (h • ePoint.symm x) = y
    rw [hh,ePoint.apply_symm_apply]⟩
  calc
    MarkedC4.genRank H = MarkedC4.genRank f.range :=
      CoprimeNilpotentProductGenerators.genRank_mulEquiv e
    _ ≤ traceyPermutationGeneratorCeiling (Nat.card Y) :=
      hbelow (Nat.card Y) hlt f.range hY inferInstance

end SymmetricSubgroupAsymptotics.TraceyStrictlySmallerTransitiveActions
