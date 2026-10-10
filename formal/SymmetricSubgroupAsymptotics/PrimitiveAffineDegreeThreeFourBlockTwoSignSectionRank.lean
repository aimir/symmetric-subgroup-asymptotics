import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignRankSplit
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockTwoSignSections
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockFullTranslationTail
import SymmetricSubgroupAsymptotics.OriginalKernelNormalSubrepresentation

/-!
# Rank of every proper ternary section in the two-sign branch

The remaining representation-theoretic input is parity of the invariant
intersection `N ∩ E`.  This file proves the group-theoretic half needed to
turn that parity into the exact section rank two.  In the rank-four branch,
self-centrality excludes a zero intersection; in both rank branches,
nontriviality of the retained quotient excludes the full intersection.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

private abbrev G := preE7NonPairAction w U

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- The invariant intersection `N ∩ E` in the original translation-module
coordinates. -/
abbrev degreeThreeFourBlockTwoSignSectionNormalSpace
    (N : TwoSignProperAxis (E block P)) :
    Submodule (ZMod P.p) (TranslationSubmodule block P) :=
  (elementaryChart block P).originalKernelChart.normalSpace
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation
    (degreeThreeFourBlockTwoSignSectionAxis block P N)

/-- In the rank-four branch, a nontrivial proper normal axis cannot meet
the translation layer trivially.  Otherwise the two disjoint normal
subgroups commute; self-centrality of the translation layer then forces
the axis itself to be trivial. -/
theorem degreeThreeFourBlockTwoSignSectionNormalSpace_ne_bot_of_finrank_four
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hfull : Module.finrank (ZMod P.p)
      (TranslationSubmodule block P) = 4)
    (N : TwoSignProperAxis (E block P)) :
    degreeThreeFourBlockTwoSignSectionNormalSpace block P N ≠ ⊥ := by
  intro hspace
  let M := degreeThreeFourBlockTwoSignSectionAxis block P N
  let pi := QuotientGroup.mk' (E block P)
  let chart := (elementaryChart block P).originalKernelChart
  have hker : (chart.kernelCoordinates pi
      (elementaryChart block P).quotientRepresentation).ker ≤
        M.subgroupOf pi.ker := by
    intro k hk
    have hk1 : k = 1 := by
      apply chart.equiv.symm.injective
      exact (MonoidHom.mem_ker.mp hk).trans (map_one chart.equiv.symm).symm
    subst k
    exact Subgroup.one_mem _
  have hinter : M.subgroupOf pi.ker = ⊥ := by
    apply le_antisymm
    · intro k hk
      change k = 1
      apply chart.equiv.symm.injective
      apply Multiplicative.toAdd.injective
      have hmem :
          (chart.kernelCoordinates pi
            (elementaryChart block P).quotientRepresentation k).toAdd ∈
            degreeThreeFourBlockTwoSignSectionNormalSpace block P N := by
        apply (sectionSubgroupImage_mem_iff
          (chart.kernelCoordinates pi
            (elementaryChart block P).quotientRepresentation)
          (M.subgroupOf pi.ker) hker k).2
        exact hk
      rw [hspace] at hmem
      have hz := Submodule.mem_bot.mp hmem
      simpa only [map_one, toAdd_one] using hz
    · exact bot_le
  have hdisjoint : Disjoint M (E block P) := by
    rw [Subgroup.disjoint_def]
    intro x hxM hxE
    let k : pi.ker := ⟨x, by
      rw [QuotientGroup.ker_mk']
      exact hxE⟩
    have hkM : k ∈ M.subgroupOf pi.ker := hxM
    have hk1 : k = 1 := by
      have : k ∈ (⊥ : Subgroup pi.ker) := hinter ▸ hkM
      exact Subgroup.mem_bot.mp this
    exact congrArg Subtype.val hk1
  have hcommute : ∀ x ∈ M, ∀ e ∈ E block P, Commute x e := by
    intro x hx e he
    exact Subgroup.commute_of_normal_of_disjoint M (E block P)
      inferInstance inferInstance hdisjoint x e hx he
  have hMbot : M = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxE : x ∈ E block P :=
        degreeThreeFourBlock_translationIntersection_selfCentralizing_of_finrank_four
          block P hr hs hcomponent hfull x (by
            intro e he
            exact (hcommute x hx e he).eq)
      have hx1 : x = 1 := by
        exact Subgroup.disjoint_def.mp hdisjoint x hx hxE
      simpa only [Subgroup.mem_bot] using hx1
    · exact bot_le
  exact N.2 hMbot

/-- Parity of the invariant intersection forces every retained proper
section to have rank two.  This is the exact numerical conclusion needed
to identify its monomial affine quotient with the degree-six wreath
comparator. -/
theorem degreeThreeFourBlockTwoSignSectionModule_finrank_eq_two_of_even_normalSpace
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4)
    (hcomponent : Nat.card block.Component = 6)
    (hbinary : IsPGroup 2
      (degreeThreeFourBlockPairChart block P hr hs hcomponent).action)
    (htwo : (degreeThreeFourBlockSignedIsotypeProfile
      block P hr hs hcomponent).isotypeCount = 2)
    (N : TwoSignProperAxis (E block P))
    (heven : Even (Module.finrank (ZMod P.p)
      (degreeThreeFourBlockTwoSignSectionNormalSpace block P N))) :
    Module.finrank (ZMod P.p)
      (DegreeThreeFourBlockTwoSignSectionModule block P N) = 2 := by
  let I := degreeThreeFourBlockTwoSignSectionNormalSpace block P N
  have hsplit :=
    degreeThreeFourBlockTwoSign_translation_finrank_eq_two_or_four
      block P hr hs hcomponent hbinary htwo
  letI : Nontrivial (DegreeThreeFourBlockTwoSignSectionModule block P N) :=
    degreeThreeFourBlockTwoSignSectionModule_nontrivial block P N
  have hsectionPos : 0 < Module.finrank (ZMod P.p)
      (DegreeThreeFourBlockTwoSignSectionModule block P N) :=
    Module.finrank_pos
  have hsum := I.finrank_quotient_add_finrank
  change Module.finrank (ZMod P.p)
      (DegreeThreeFourBlockTwoSignSectionModule block P N) +
    Module.finrank (ZMod P.p) I =
      Module.finrank (ZMod P.p) (TranslationSubmodule block P) at hsum
  obtain ⟨d, hd⟩ := heven
  rcases hsplit with htwoRank | hfourRank
  · omega
  · have hIne : I ≠ ⊥ :=
      degreeThreeFourBlockTwoSignSectionNormalSpace_ne_bot_of_finrank_four
        block P hr hs hcomponent hfourRank N
    have hIpos : 0 < Module.finrank (ZMod P.p) I := by
      apply Nat.pos_of_ne_zero
      intro hzero
      exact hIne (Submodule.finrank_eq_zero.mp hzero)
    omega

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
