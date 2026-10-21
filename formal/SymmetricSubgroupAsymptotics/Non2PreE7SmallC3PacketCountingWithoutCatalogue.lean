import SymmetricSubgroupAsymptotics.Non2PreE7SmallC3PacketCounting
import SymmetricSubgroupAsymptotics.Non2PreE7SmallC3PacketStructureWithoutCatalogue

/-! Actual-consumer adapter without the composition catalogue. The original
physical families, rank caps, normal axes and numerical kernels are retained. -/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
open RepeatedC3TailPhysical RepeatedC3TailExtraction

private theorem packet_has_regularOrbit {n : ℕ}
    (G : PreE7SmallC3PacketSubgroupSet n) :
    ∃ o : OrbitProfileFromOrbits.Orbit G.1.1,
      IsRegularC3Orbit G.1.1 o := by
  obtain ⟨o, hbad⟩ := exists_preE7ViolationOrbit G.1.1 G.1.2.1.1.2
  let outside : RepeatedMarkerOwnerBound.OutsideOrbit G.1.1 :=
    ⟨o, hbad.1, hbad.2.1⟩
  have hcard : Nat.card o.orbit = 3 := G.2 o hbad
  obtain ⟨e, he⟩ :=
    RepeatedMarkerOwnerBound.outsideOrbit_degree_three_ternary_chart
      G.1.1 outside hcard
  have hp0 : IsPGroup 3 ternaryRegularAction :=
    IsPGroup.iff_card.mpr ⟨1, by
      rw [ternaryRegularAction_card]
      norm_num⟩
  let g : ternaryRegularAction ≃*
      OrbitProfileFromOrbits.orbitImage G.1.1 o :=
    (e.permCongrHom.subgroupMap ternaryRegularAction).trans
      (MulEquiv.subgroupCongr he)
  exact ⟨o, hcard, hp0.of_equiv g⟩

private theorem packet_regularCount_pos {n : ℕ}
    (G : PreE7SmallC3PacketSubgroupSet n) :
    0 < regularCount G.1.1 := by
  obtain ⟨o, ho⟩ := packet_has_regularOrbit G
  exact regularCount_pos G.1.1 o ho

private theorem packet_degree_eq {n : ℕ}
    (G : PreE7SmallC3PacketSubgroupSet n) :
    3 * regularCount G.1.1 + tailDegree G.1.1 = n := by
  simpa only [Fintype.card_fin] using degree_eq G.1.1

private def positiveProfileIndex {n : ℕ}
    (G : PreE7SmallC3PacketPositive n) :
    RepeatedC3PositiveProfileIndex n where
  c := ⟨regularCount G.1.1.1, by
    have h := packet_degree_eq G.1
    omega⟩
  m := ⟨tailDegree G.1.1.1, by
    have h := packet_degree_eq G.1
    omega⟩
  c_pos := packet_regularCount_pos G.1
  m_pos := G.2
  degree_eq := packet_degree_eq G.1


def positivePresentation_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} (G : PreE7SmallC3PacketPositive n) :
    Σ p : RepeatedC3PositiveProfileIndex n,
      AssembledOrbitProfileOn
        (RepeatedC3TailProfile.modelPredicate p.c
          (3 * p.m / 20) p.m) (Fin n) :=
  ⟨positiveProfileIndex G,
    repeatedC3Tail_packetAssembly_without_catalogue hChief hWeight hgen hindex published8 h18
      G.1.1.1 G.1.2⟩

theorem positivePresentation_injective_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    {n : ℕ} :
    Function.Injective
      (positivePresentation_without_catalogue hChief hWeight hgen hindex published8 h18
        (n := n)) := by
  intro G K h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hv := congrArg (fun z => z.2.1) h
  change G.1.1.1 = K.1.1.1 at hv
  exact hv

/-- Every zero-tail packet member enters the honest one-colour pure profile. -/

theorem preE7SmallC3PacketPositive_card_le_without_catalogue
    (hChief : PrimitiveTernaryChiefWeightBound (fun r => r / 3))
    (hWeight : PrimitiveTernaryThreeTenthsWeightBound)
    (hgen : PrimitiveNormalGeneratorInput)
    (hindex : PrimitiveSocleRawStructure.PublishedSimpleIndexBounds)
    (published8 : Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer.DegreeEightCanonicalCatalogue.PublishedClassification)
    (h18 : DegreeEighteenTernaryHeadBound)
    (n : ℕ) :
    Nat.card (PreE7SmallC3PacketPositive n) ≤
      ∑ p : RepeatedC3PositiveProfileIndex n,
        Nat.card (AssembledOrbitProfileOn
          (RepeatedC3TailProfile.modelPredicate p.c
            (3 * p.m / 20) p.m) (Fin n)) := by
  letI : ∀ p : RepeatedC3PositiveProfileIndex n,
      Finite (AssembledOrbitProfileOn
        (RepeatedC3TailProfile.modelPredicate p.c
          (3 * p.m / 20) p.m) (Fin n)) := fun _ => by
    unfold AssembledOrbitProfileOn
    infer_instance
  calc
    _ ≤ Nat.card (Σ p : RepeatedC3PositiveProfileIndex n,
        AssembledOrbitProfileOn
          (RepeatedC3TailProfile.modelPredicate p.c
            (3 * p.m / 20) p.m) (Fin n)) :=
      Nat.card_le_card_of_injective
        (positivePresentation_without_catalogue hChief hWeight hgen hindex published8 h18)
        (positivePresentation_injective_without_catalogue hChief hWeight hgen hindex published8 h18)
    _ = _ := Nat.card_sigma

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
end
