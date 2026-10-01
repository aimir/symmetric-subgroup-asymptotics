import SymmetricSubgroupAsymptotics.Non2PreE7ComparatorAbelianTowerMenu
import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleMenu
import SymmetricSubgroupAsymptotics.Non2PreE7RefinedCapacityMenu
import SymmetricSubgroupAsymptotics.Non2PreE7CharacterCertificateMenu

/-!
# Unified numerical instances for the four ordinary templates

This dispatcher is the exact integration boundary for the 37 families
covered by refined capacity, comparator/abelian towers, character
certificates, and ordinary semisimple estimates.  `SNS2` and the fifteen
small fixed-degree families remain on their special-moment lane.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- One of the four ordinary template sources on a literal family/action
pair.  Each constructor retains the proof that the family belongs to the
corresponding audited template. -/
inductive PreE7OrdinaryNumericalSourceData
    (family : PreE7NoPairNoC3EarlierOwnerFamily)
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type 1 where
  | refined (hfamily : IsPreE7RefinedCapacityFamily family)
      (source : RefinedCapacityCertificateSourceData family w i)
  | comparator (hfamily : IsPreE7ComparatorAbelianTowerFamily family)
      (source : ComparatorAbelianTowerCertificateSourceData family w i)
  | character (hfamily : IsPreE7CharacterFamily family)
      (source : PreE7CharacterMenuSourceData family hfamily w i)
  | semisimple (hfamily : IsPreE7OrdinarySemisimpleFamily family)
      (source : SemisimpleCertificateSourceData family w i)

/-- Dispatch an ordinary source to its numerically complete catalogue
package. -/
noncomputable def PreE7OrdinaryNumericalSourceData.toPackage
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7OrdinaryNumericalSourceData family w i) :
    PreE7EarlierNumericalPackage family w i := by
  cases S with
  | refined hfamily source =>
      exact preE7RefinedCapacityNumericalPackage family hfamily source
  | comparator hfamily source =>
      exact preE7ComparatorAbelianTowerNumericalPackage
        family hfamily w i source
  | character hfamily source =>
      exact preE7CharacterNumericalPackage lit family hfamily source
  | semisimple hfamily source =>
      exact preE7OrdinarySemisimpleNumericalPackage
        hgen family hfamily source

/-- Every source in the four ordinary templates is accepted by the exact
numerically certified family predicate used by the T1 catalogue. -/
theorem preE7OrdinaryNumericalFamilyAction
    (lit : PreE7CharacterLiterature)
    (hgen : PermutationSubgroupGeneratorBound)
    {family : PreE7NoPairNoC3EarlierOwnerFamily}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7OrdinaryNumericalSourceData family w i) :
    preE7NoPairNoC3EarlierNumericalFamilyAction family w i :=
  ⟨S.toPackage lit hgen⟩

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
