import SymmetricSubgroupAsymptotics.NormalTwoGroupTernaryEigenbasis
import SymmetricSubgroupAsymptotics.RepeatedTernaryEigencharactersCentral
import SymmetricSubgroupAsymptotics.TernaryMonomialRepresentationCard

/-! A faithful irreducible ternary three-dimensional group with a
nonscalar normal two-group is monomial and has order at most48. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.NormalTwoGroupTernaryMonomialBound
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem card_le_fortyEight
    {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    (rho : Representation (ZMod 3) G V) (hf : Function.Injective rho)
    (hrho : Representation.IsIrreducible rho) (hdim : Module.finrank (ZMod 3) V=3)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N)
    (hnonscalar : ∃ n : N,¬∃ a : ZMod 3,rho n.val=a • (1 : Module.End (ZMod 3) V)) :
    Nat.card G≤48 := by
  obtain ⟨b,hb⟩ := NormalTwoGroupTernaryEigenbasis.exists_eigenbasis rho hrho hdim N hN
  choose a ha using hb
  have hn : ∃ (n : N) (t : Fin 3),a n t≠a n 0 := by
    by_contra h
    obtain ⟨n,hn⟩ := hnonscalar
    apply hn
    refine ⟨a n 0,?_⟩
    apply b.ext
    intro i
    have he : a n i=a n 0 := not_not.mp (not_exists.mp (not_exists.mp h n) i)
    simpa only [LinearMap.smul_apply,Module.End.one_apply,he] using ha n i
  have hsep := RepeatedTernaryEigencharactersCentral.separated_of_nonscalar
    rho b N a ha hrho hn
  apply TernaryMonomialRepresentationCard.card_le_fortyEight rho hf b
  exact SeparatedEigenbasisMonomial.normal_action_is_monomial rho b N a ha hsep

end SymmetricSubgroupAsymptotics.NormalTwoGroupTernaryMonomialBound
