import SymmetricSubgroupAsymptotics.CFSGMonsterE6RemoteTernaryEmbedding
import SymmetricSubgroupAsymptotics.PerfectActionTernaryPairPacking
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree

/-! An actual commuting C3×C3 tail strengthens the original Monster
small-action exclusion to33. This concerns the original derived node
centralizer, and assumes neither its order nor whole generating tuple. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMonsterRemoteTailIndex
open CFSG.Models.MonsterConstruction CFSGMonsterE6RemoteTernaryEmbedding
open PerfectTransitiveActionCentralizer

private theorem exists_moved_of_ne_one {X : Type*} (p : Equiv.Perm X) (hp : p≠1) :
    ∃ x, p x≠x := by
  by_contra hh
  push_neg at hh
  apply hp
  ext x
  exact hh x

private theorem action_gap [Finite CFSG.Models.Monster] : FiniteActionGap E6Derived 27 := by
  intro n σ hn
  by_contra hs
  have hex : ∃ g : E6Derived, ∃ x : Fin n, σ g x≠x := by
    by_contra hh
    push_neg at hh
    apply hs
    apply MonoidHom.ext
    intro g
    apply Equiv.ext
    intro x
    exact hh g x
  letI : MulAction E6Derived (Fin n) := MulAction.compHom _ σ
  have hd := card_ge_twentySeven_of_nontrivial_action hex
  simp only [Nat.card_fin] at hd
  omega

/-- Every faithful actual permutation representation of the original
Monster model has degree at least33. -/
theorem card_ge_thirtyThree_of_injective_hom [Finite CFSG.Models.Monster]
    (hn : ¬IsMulCommutative CFSG.Models.Monster)
    {X : Type*} [Finite X] (ρ : CFSG.Models.Monster →* Equiv.Perm X)
    (hρ : Function.Injective ρ) : 33≤Nat.card X := by
  letI : Group.IsPerfect E6Derived := ⟨e6Derived_perfect⟩
  letI : MulAction E6Derived X := MulAction.compHom _ (ρ.comp e6Embedding)
  let a : E6Derived := E6BraidSystemDerivedWords.a
    (E6BraidSystemDerivedImage.imageSystem system)
  have ha : ρ (e6Embedding a)≠1 := by
    intro he
    apply anchor_ne_one hn
    apply e6Embedding_injective
    apply hρ
    simpa only [map_one] using he
  obtain ⟨x,hx⟩ := exists_moved_of_ne_one _ ha
  let f := ρ.comp ternaryEmbedding
  have hf : Function.Injective f := hρ.comp (ternaryEmbedding_injective hn)
  have hP : Nat.card (TernaryIndependentPairEmbedding.P×TernaryIndependentPairEmbedding.P)=9 := by
    norm_num [Nat.card_prod,TernaryIndependentPairEmbedding.P,Nat.card_zmod]
  apply PerfectActionTernaryPairPacking.card_ge_thirtyThree action_gap ⟨a,x,hx⟩ f hf hP
  intro p g y
  have he := (embeddings_commute p g).map ρ
  exact congrArg (fun q : Equiv.Perm X => q y) he.eq

/-- The original faithful coset action supplies the subgroup index. -/
theorem proper_index_ge_thirtyThree [Finite CFSG.Models.Monster]
    [IsSimpleGroup CFSG.Models.Monster]
    (hn : ¬IsMulCommutative CFSG.Models.Monster)
    (H : Subgroup CFSG.Models.Monster) (hH : H≠⊤) : 33≤H.index := by
  let ρ := MulAction.toPermHom CFSG.Models.Monster (CFSG.Models.Monster ⧸ H)
  have hcore : H.normalCore=⊥ := by
    rcases (inferInstance : H.normalCore.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact False.elim (hH (top_unique (ht ▸ H.normalCore_le)))
  have hker : ρ.ker=⊥ := by
    rw [←H.normalCore_eq_ker,hcore]
  have hi : Function.Injective ρ := ρ.ker_eq_bot_iff.mp hker
  simpa only [H.index_eq_card] using card_ge_thirtyThree_of_injective_hom hn ρ hi

end SymmetricSubgroupAsymptotics.CFSGMonsterRemoteTailIndex
