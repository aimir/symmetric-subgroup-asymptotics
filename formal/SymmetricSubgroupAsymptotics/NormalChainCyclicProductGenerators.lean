import SymmetricSubgroupAsymptotics.NormalGeneratingTuplesExtension
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

theorem normal_pairs_of_normal_chain_cyclic_product
    {H C : Type} [Group H] [Finite H] [Group C] [Finite C] [IsCyclic C]
    (hH : ∀ (A B : Subgroup H), A.Normal → B.Normal → A ≤ B ∨ B ≤ A) :
    ∀ N : Subgroup (H × C), N.Normal →
      ∃ x : Fin 2 → H × C, Subgroup.normalClosure (Set.range x)=N := by
  let pi : H × C →* C := MonoidHom.snd H C
  have hpi : Function.Surjective pi := fun c => ⟨(1,c),rfl⟩
  let f : H →* pi.ker :=
    { toFun := fun h => ⟨(h,1),rfl⟩
      map_one' := rfl
      map_mul' := by
        intro a b
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (one_mul (1 : C)).symm }
  have hf : Function.Surjective f := by
    intro x
    refine ⟨x.val.1,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (show x.val.2=1 from x.property).symm
  have hK : ∀ N : Subgroup pi.ker, N.Normal →
      ∃ x : Fin 1 → pi.ker, Subgroup.normalClosure (Set.range x)=N :=
    normal_generating_tuples_of_surjective f hf
      (normal_generating_singletons_of_finite_normal_total hH)
  exact normal_generating_tuples_cyclic_extension pi hpi hK
end SymmetricSubgroupAsymptotics
