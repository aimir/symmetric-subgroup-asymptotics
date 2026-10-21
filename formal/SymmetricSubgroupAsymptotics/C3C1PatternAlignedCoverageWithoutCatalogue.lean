import SymmetricSubgroupAsymptotics.C3C1PatternAlignedCoverage
import SymmetricSubgroupAsymptotics.C1DegreeNinePatternDeletionWithoutCatalogue

/-! The exact aligned nine-point source restriction uses the proved
unchanged rank budget on the same deleted model and complement. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
namespace C3HighNestedCarrier

/-- The exact degree-nine chart inherits the source rank budget from the
complete one-C3 pattern. -/
theorem Data.degreeNine_deletedModel_rankBudget_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {b : ℕ}
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = 9)
    (i : Non2TransitiveActionClass (Fin 9))
    (eO : Fin 9 ≃ C.orbit.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (hpattern : C1DegreeNineSourcePattern (physicalSubgroup H)) :
    C1DegreeNineRankBudget
      ((fusionDeletedModel i.representative
          (relabelSubgroup (chart H C.orbit hw eO).symm
            (physicalSubgroup H))).map
        (MonoidHom.snd i.representative
          (Equiv.Perm (Fin (b + 3 - 9))))) := by
  have hselected : ¬ IsRegularC3Orbit
      (physicalSubgroup H) (liftedOrbit H C.orbit) := by
    intro hregular
    have hcard := hregular.1
    rw [liftedOrbit_card H C.orbit, hw] at hcard
    omega
  exact hpattern.deletedModel_rankBudget_without_catalogue hChief hgen hindex published8 h18
    (physicalSubgroup H) (liftedOrbit H C.orbit) i.representative
    (pointEquiv H C.orbit eO) (complementEquiv H C.orbit hw)
    (pointEquiv_image H C.orbit i.representative eO himage) hselected

/-- A degree-nine high-C3 chart from the exact c=1 family enters the aligned
first-owner cell with the source budget installed in its local predicate. -/
theorem Data.mem_non2FirstOwnerCanonicalFamily_forAction_rankBudget_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {r b : ℕ}
    (Eligible : ∀ n, Fin r → Subgroup (Equiv.Perm (Fin n)) → Prop)
    (hEligible : DegreeNaturalOwnerMenu Eligible)
    (H : Subgroup (ternaryRegularAction × Equiv.Perm (Fin b)))
    (C : Data H)
    (hw : Nat.card C.orbit.orbit = 9)
    (q : TernaryCyclic ⊕ Fin b ≃ Fin (b + 3))
    (hordinary : ¬ IsCriticalSubgroup (b + 3)
      (relabelSubgroup q (physicalSubgroup H)))
    (owner : Fin r)
    (howner : FirstOwned (Eligible (b + 3)) owner
      (relabelSubgroup q (physicalSubgroup H)))
    (i : Non2TransitiveActionClass (Fin 9))
    (eO : Fin 9 ≃ C.orbit.orbit)
    (himage : relabelSubgroup eO i.representative =
      OrbitProfileFromOrbits.orbitImage (C3ComplementSource b H) C.orbit)
    (hpattern : C1DegreeNineSourcePattern (physicalSubgroup H)) :
    relabelSubgroup q (physicalSubgroup H) ∈
      FusionWidthCanonicalFamily i.representative (by
        have hwb := width_le H C.orbit hw
        omega)
        (FusionSourceRestrictedPredicate i.representative
          (non2FirstOwnerPredicate Eligible 9 (owner, i) (b + 3 - 9))
          C1DegreeNineRankBudget) := by
  have hownerLocal :=
    C.deletedModel_non2FirstOwnerPredicate_forAction
      Eligible hEligible H hw q hordinary owner howner i eO himage
  have hbudget := C.degreeNine_deletedModel_rankBudget_without_catalogue
    hChief hgen hindex published8 h18 H hw i eO himage hpattern
  exact mem_widthCanonicalFamily_of_relabel H C hw i.representative
    eO himage q
    (FusionSourceRestrictedPredicate i.representative
      (non2FirstOwnerPredicate Eligible 9 (owner, i) (b + 3 - 9))
      C1DegreeNineRankBudget)
    ⟨hownerLocal, hbudget⟩

end C3HighNestedCarrier
end SymmetricSubgroupAsymptotics
