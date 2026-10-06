import SymmetricSubgroupAsymptotics.FiniteThreeNormalChainSocleGenerators

/-!
# Quotient rows from a three-point normal chain

A checked three-state normal chain already classifies every normal subgroup
as bottom, middle, or top.  This file performs the dependent transport once:
every normal quotient receives the corresponding one-position socle normal
generator bound.  Later finite catalogues therefore need only construct the
chain datum; they do not need separate bottom, middle, and top row modules.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace FiniteThreeNormalChainData

variable {G : Type} [Group G]

private noncomputable def bottomQuotientOfEq
    (D : FiniteThreeNormalChainData G)
    (N : Subgroup G) [N.Normal] (h : N = ⊥) :
    SocleNormalGeneratorBound (G ⧸ N) 1 := by
  subst N
  exact D.bottomQuotientSocleGenerator

private noncomputable def middleQuotientOfEq
    (D : FiniteThreeNormalChainData G)
    (N : Subgroup G) [N.Normal] (h : N = D.middle) :
    SocleNormalGeneratorBound (G ⧸ N) 1 := by
  subst N
  exact D.middleQuotientSocleGenerator

private noncomputable def topQuotientOfEq
    (N : Subgroup G) [N.Normal] (h : N = ⊤) :
    SocleNormalGeneratorBound (G ⧸ N) 1 := by
  subst N
  exact
    FiniteThreeNormalChainData.topQuotientSocleGenerator
      (G := G)

/-- Every normal quotient in a three-point normal lattice has a one-position
socle normal-generator witness.  The branch is selected by the chain's
kernel-checked exhaustive normal classification. -/
noncomputable def quotientSocleGenerator
    (D : FiniteThreeNormalChainData G)
    (N : Subgroup G) [N.Normal] :
    SocleNormalGeneratorBound (G ⧸ N) 1 := by
  rcases D.normal_eq_bot_or_middle_or_top N (by infer_instance) with
      hbot | hmiddle | htop
  · exact bottomQuotientOfEq D N hbot
  · exact middleQuotientOfEq D N hmiddle
  · exact topQuotientOfEq N htop

end FiniteThreeNormalChainData
end SymmetricSubgroupAsymptotics

end
