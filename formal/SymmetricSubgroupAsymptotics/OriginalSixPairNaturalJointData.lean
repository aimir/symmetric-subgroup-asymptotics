import SymmetricSubgroupAsymptotics.SixPairTransitiveTopOriginalSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds

/-! Assemble original joint data from an actual physical six-pair frame,
a checked reference-point word cover, and the original natural bound. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData
open Non2UnipotentPrefixFiniteMenu
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

 theorem top_pretransitive
    {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 6))
    (words : Fin 6 → U)
    (hwords : ∀ i, (F.frame.symm ((words i : Equiv.Perm X) (F.frame (0,0)))).1 = i) :
    MulAction.IsPretransitive F.top.range (Fin 6) where
  exists_smul_eq i j := by
    have hz (k : Fin 6) : F.top (words k) 0 = k :=
      (F.intertwine (words k) (0,0)).symm.trans (hwords k)
    refine ⟨F.top.rangeRestrict (words j * (words i)⁻¹),?_⟩
    change F.top (words j * (words i)⁻¹) i = j
    rw [map_mul,map_inv]
    change F.top (words j) ((F.top (words i))⁻¹ i) = j
    have hi : (F.top (words i))⁻¹ i = 0 := by
      calc
        (F.top (words i))⁻¹ i = (F.top (words i))⁻¹ (F.top (words i) 0) :=
          congrArg (fun x => (F.top (words i))⁻¹ x) (hz i).symm
        _ = 0 := (F.top (words i)).symm_apply_apply 0
    rw [hi,hz]

def jointData
    (socle : PublishedPrimitiveSocleDichotomyInput)
    (catalogue : PublishedBoundedPrimitiveCatalogueCorrespondence)
    (C : DegreeTwoPairTopFiniteInterface 12)
    (F : BinaryPairFrame C.top (Fin 6))
    [MulAction.IsPretransitive F.top.range (Fin 6)]
    (hnatural : UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) C.top (Fin 12)) 1) :
    DegreeTwoTwelveJointFiniteRows.DegreeTwoTwelveJointFiniteRowData C 3 1 where
  topSocle := FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    C.normalRegistry (fun N => by
      letI := N.2
      exact SixPairTransitiveTopOriginalSocles.quotientSocle socle catalogue F hnatural N.1)
  natural := hnatural

end SymmetricSubgroupAsymptotics.OriginalSixPairNaturalJointData
