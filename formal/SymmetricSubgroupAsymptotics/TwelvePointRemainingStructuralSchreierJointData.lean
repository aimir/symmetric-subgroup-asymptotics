import SymmetricSubgroupAsymptotics.TwelvePointRemainingStructuralSchreierSocles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! A reusable complete joint package from an actual signed-S4 descriptor,
its physical two-orbit cover, and a separately proved natural capacity.
The interface's exact original subgroup is identified by equality; its
existing registries and the published admissible parameter menu are kept. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelveJointFiniteRows

structure SymmetricPairTwoOrbitCover {n : ℕ}
    {generators : Fin n → Equiv.Perm (Fin 12)}
    (D : SymmetricPairGeneratorData generators) where
  cubic : Subgroup.closure (Set.range generators)
  representative : Fin 2 → Fin 6
  cover : ∀ x : Fin 6, ∃ (j : Fin 2) (k : ℕ),
    ((D.frame.top cubic)^k) (representative j)=x

namespace SymmetricPairSchreierWordData
variable {n : ℕ} {generators : Fin n → Equiv.Perm (Fin 12)}
  {D : SymmetricPairGeneratorData generators}
  (C : SymmetricPairSchreierWordData generators D)
  (O : SymmetricPairTwoOrbitCover D)

def quotientSocleFamily
    (R : FiniteNormalStateRegistry (Subgroup.closure (Set.range generators))) :
    R.QuotientSocleGeneratorFamily 2 :=
  .ofQuotientBounds _ (fun N => by
    letI := N.2
    exact C.original_quotientSocle_of_orbitCover O.cubic O.representative O.cover N.1)

/-- Complete finite data on the exact original interface. The natural
field is an independently proved module certificate, not a socle premise. -/
def finiteAtTwo (I : DegreeTwoPairTopFiniteInterface 12)
    (hTop : I.top=Subgroup.closure (Set.range generators))
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) I.top (Fin 12)) 2) :
    DegreeTwoTwelveJointFiniteRowData I 2 2 := by
  have hs : ∀ (U : Subgroup (Equiv.Perm (Fin 12))),
      U=Subgroup.closure (Set.range generators) →
      ∀ R : FiniteNormalStateRegistry U, R.QuotientSocleGeneratorFamily 2 := by
    intro U hU
    subst U
    intro R
    exact C.quotientSocleFamily O R
  exact { topSocle := hs I.top hTop I.normalRegistry, natural := natural }

/-- Catalogue-facing data at the existing admissible pair (2,2).
No historical-profile equality or final counting hypothesis is added. -/
def jointDataAtTwo (I : DegreeTwoPairTopFiniteInterface 12)
    (hTop : I.top=Subgroup.closure (Set.range generators))
    (natural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) I.top (Fin 12)) 2) :
    DegreeTwoTwelveFlexibleProfiles.Data I :=
  .ofExact (C.finiteAtTwo O I hTop natural) (by decide +kernel)

end SymmetricPairSchreierWordData
end SymmetricSubgroupAsymptotics.TwelvePointRemainingStructural
