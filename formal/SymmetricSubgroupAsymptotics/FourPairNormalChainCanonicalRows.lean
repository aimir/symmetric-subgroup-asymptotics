import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow11NormalStates
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairedEightRow14NormalStates
import SymmetricSubgroupAsymptotics.PrimitiveAffineEightTransitiveMatch
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoFourPairsClassification

/-! Three actual canonical rows from existing complete normal chains.
No new abstract group recognition or normal census is required. The axis
is the whole original group; every original normal quotient has socle1. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairNormalChainCanonicalRows
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

/-- A proved complete normal chain supplies an actual character model.
The comparator is the trivial quotient by the whole original group. -/
def characterModel {U : PreE7NonPairActionClass 8}
    (chain : ∀ N M : Subgroup (preE7NonPairAction 8 U),
      N.Normal → M.Normal → N ≤ M ∨ M ≤ N) : CertifiedFourPairCharacterModel U where
  interval := {
    E := ⊤
    quotientDegree := 1
    quotientAction := 1
    quotientAction_injective := by
      intro x y _
      have hz : ∀ z : (preE7NonPairAction 8 U) ⧸ (⊤ : Subgroup (preE7NonPairAction 8 U)), z=1 := by
        intro z
        obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (⊤ : Subgroup (preE7NonPairAction 8 U)) z
        exact (QuotientGroup.eq_one_iff g).mpr (Subgroup.mem_top g)
      exact (hz x).trans (hz y).symm
    slots := 1
    quotientSocleGenerators := by
      intro N _
      letI := N.2
      exact quotientSocleNormalGeneratorBound_one_of_normal_total chain N.1 }
  quotientDegree_le_six := by norm_num
  slots_eq_one := rfl

private def matchEquiv (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p)) :
    preE7PairAction 4 p ≃* (DegreeTwoPairedEightSharedTops.interface M.index).top :=
  PermutationStabilizerTransport.groupEquiv _ _ M.points M.conjugator M.matched

namespace Row11
abbrev Source := PrimitiveAffineEightFrameRow20TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow20TopCertificate.group
abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow20TopCertificate.generators)

private theorem state_monotone : Monotone PrimitiveAffineDegreeTwoPairedEightRow11NormalStates.state := by
  intro i j hij
  apply (PrimitiveAffineDegreeTwoPairedEightRow11NormalStates.state_le_iff_maskLE i j).mpr
  revert hij
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem source_normal_total (N M : Subgroup Source) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N := by
  letI := hN
  letI := hM
  obtain ⟨i,rfl⟩ := PrimitiveAffineEightFrameRow20NormalCertificate.complete N
  obtain ⟨j,rfl⟩ := PrimitiveAffineEightFrameRow20NormalCertificate.complete M
  exact (le_total i j).elim (fun h => Or.inl (state_monotone h))
    (fun h => Or.inr (state_monotone h))

theorem top_normal_total (N M : Subgroup Top) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N :=
  normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameRow20TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow20TopCertificate.originalEquiv.surjective
    source_normal_total N M hN hM
end Row11

namespace Row14
abbrev Source := PrimitiveAffineEightFrameRow23TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineEightFrameRow23TopCertificate.group
abbrev Top := Subgroup.closure
  (Set.range PrimitiveAffineEightFrameRow23TopCertificate.generators)

private theorem state_monotone : Monotone PrimitiveAffineDegreeTwoPairedEightRow14NormalStates.state := by
  intro i j hij
  apply (PrimitiveAffineDegreeTwoPairedEightRow14NormalStates.state_le_iff_maskLE i j).mpr
  revert hij
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem source_normal_total (N M : Subgroup Source) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N := by
  letI := hN
  letI := hM
  obtain ⟨i,rfl⟩ := PrimitiveAffineEightFrameRow23NormalCertificate.complete N
  obtain ⟨j,rfl⟩ := PrimitiveAffineEightFrameRow23NormalCertificate.complete M
  exact (le_total i j).elim (fun h => Or.inl (state_monotone h))
    (fun h => Or.inr (state_monotone h))

theorem top_normal_total (N M : Subgroup Top) (hN : N.Normal) (hM : M.Normal) :
    N ≤ M ∨ M ≤ N :=
  normalSubgroups_total_of_surjective
    PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.toMonoidHom
    PrimitiveAffineEightFrameRow23TopCertificate.originalEquiv.surjective
    source_normal_total N M hN hM
end Row14

/-- Actual retained canonical index1; all structural facts are proved. -/
def s4RowOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (1 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) := by
  have heq : (DegreeTwoPairedEightSharedTops.interface M.index).top = PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles.Top := by
    rw [hindex]
    rfl
  let e : preE7PairAction 4 p ≃* PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles.Top :=
    (matchEquiv p M).trans (MulEquiv.subgroupCongr heq)
  exact .character (characterModel (normalSubgroups_total_of_surjective
    e.symm.toMonoidHom e.symm.surjective PrimitiveAffineDegreeTwoPairedEightRow2QuotientSocles.top_normal_total))

/-- Actual retained canonical index10; all structural facts are proved. -/
def slRowOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (10 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) := by
  have heq : (DegreeTwoPairedEightSharedTops.interface M.index).top = Row11.Top := by
    rw [hindex]
    rfl
  let e : preE7PairAction 4 p ≃* Row11.Top :=
    (matchEquiv p M).trans (MulEquiv.subgroupCongr heq)
  exact .character (characterModel (normalSubgroups_total_of_surjective
    e.symm.toMonoidHom e.symm.surjective Row11.top_normal_total))

/-- Actual retained canonical index13; all structural facts are proved. -/
def glRowOfMatch (p : PreE7PairActionClass 4)
    (M : DegreeEightCanonicalCatalogue.TransitiveLiteralMatch (preE7PairAction 4 p))
    (hindex : M.index = (13 : Fin 24)) :
    PublishedDegreeTwoFourPairRow (preE7FourPairNonPairAction p) := by
  have heq : (DegreeTwoPairedEightSharedTops.interface M.index).top = Row14.Top := by
    rw [hindex]
    rfl
  let e : preE7PairAction 4 p ≃* Row14.Top :=
    (matchEquiv p M).trans (MulEquiv.subgroupCongr heq)
  exact .character (characterModel (normalSubgroups_total_of_surjective
    e.symm.toMonoidHom e.symm.surjective Row14.top_normal_total))

end SymmetricSubgroupAsymptotics.FourPairNormalChainCanonicalRows
end
