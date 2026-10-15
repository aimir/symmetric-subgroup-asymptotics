import SymmetricSubgroupAsymptotics.QuotientSocleRelativeHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightCompleteCatalogue

/-! Reuse the checked all-original-quotient socle family on the fixed
twenty-four literal eight-point tops. The original normal subgroup and
ambient conjugation action are retained. No historical relative-head
registry or its native finite reductions occur in this proof. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
namespace PrimitiveAffineEightTopRelativeHeads

theorem relativeHead_le_two (p : ℕ) [Fact p.Prime] (j : Fin 24)
    (N : Subgroup (DegreeTwoPairedEightSharedTops.interface j).top) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ 2 :=
  primeRelativeHead_le_of_all_quotient_socles p 2
    (DegreeTwoPairedEightCompleteCatalogue.completeRow j).topSocle N

theorem relativeHead_le_two_of_equiv (p : ℕ) [Fact p.Prime] (j : Fin 24)
    {G : Type} [Group G] [Finite G]
    (e : G ≃* (DegreeTwoPairedEightSharedTops.interface j).top)
    (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ 2 := by
  let M := N.map e.toMonoidHom
  letI : M.Normal := Subgroup.Normal.map inferInstance _ e.surjective
  have h := (relativeCharacterAmbientCongr p e N M rfl).finrank_eq
  exact h.symm.le.trans (relativeHead_le_two p j M)

end PrimitiveAffineEightTopRelativeHeads
end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
