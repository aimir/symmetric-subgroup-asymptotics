import SymmetricSubgroupAsymptotics.PrimitiveEightCanonicalMatch
import SymmetricSubgroupAsymptotics.S8TransitiveCanonicalCoverage
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! Actual primitive degree-eight actions need at most three generators.
The existing exact subgroup coverage is used, not assumed. This does not
close smaller-degree globally minimal failed actions. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

private theorem closure_range_genRank_le {G : Type} [Group G] [Finite G]
    {k : ℕ} (g : Fin k → G) : MarkedC4.genRank (Subgroup.closure (Set.range g)) ≤ k := by
  let H := Subgroup.closure (Set.range g)
  let u : Fin k → H := fun i => ⟨g i,Subgroup.subset_closure (Set.mem_range_self i)⟩
  let K : Subgroup H := Subgroup.closure (Set.range u)
  have hHK : H ≤ K.map H.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro z ⟨i,rfl⟩
    exact ⟨u i,Subgroup.subset_closure (Set.mem_range_self i),rfl⟩
  have hu : Subgroup.closure (Set.range u)=⊤ := by
    apply top_unique
    intro z _
    obtain ⟨w,hw,he⟩ := hHK z.property
    have he' : w=z := Subtype.ext he
    exact he' ▸ hw
  let S : Finset H := Finset.univ.image u
  have hs : (S : Set H)=Set.range u := by
    simp only [S,Finset.coe_image,Finset.coe_univ,Set.image_univ]
  have hgen : Subgroup.closure (S : Set H)=⊤ := by rw [hs]; exact hu
  exact (MarkedC4.genRank_le hgen).trans (Finset.card_image_le.trans (by simp))

private theorem primitive_interface_rank (i : Fin 24) (hi : 17 ≤ i.val) :
    MarkedC4.genRank (DegreeTwoPairedEightSharedTops.interface i).top ≤ 3 := by
  fin_cases i <;> norm_num at hi
  · change MarkedC4.genRank (Subgroup.closure (Set.range DegreeTwoPairedEightSharedTops.top18Generators)) ≤ 3
    exact (closure_range_genRank_le _).trans (by decide : 2 ≤ 3)
  · change MarkedC4.genRank (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow27TopCertificate.generators)) ≤ 3
    exact closure_range_genRank_le _
  · change MarkedC4.genRank (Subgroup.closure (Set.range DegreeTwoPairedEightSharedTops.top20Generators)) ≤ 3
    exact closure_range_genRank_le _
  · change MarkedC4.genRank (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow28TopCertificate.generators)) ≤ 3
    exact closure_range_genRank_le _
  · change MarkedC4.genRank (Subgroup.closure (Set.range PrimitiveAffineEightFrameRow29TopCertificate.generators)) ≤ 3
    exact closure_range_genRank_le _
  · change MarkedC4.genRank (Subgroup.closure (Set.range DegreeTwoPairedEightSharedTops.top23Generators)) ≤ 3
    exact (closure_range_genRank_le _).trans (by decide : 2 ≤ 3)
  · change MarkedC4.genRank (Subgroup.closure (Set.range DegreeTwoPairedEightSharedTops.top24Generators)) ≤ 3
    exact (closure_range_genRank_le _).trans (by decide : 2 ≤ 3)

theorem genRank_le_three (J : Subgroup (Equiv.Perm (Fin 8)))
    (hp : MulAction.IsPreprimitive J (Fin 8)) : MarkedC4.genRank J ≤ 3 := by
  letI : MulAction.IsPreprimitive J (Fin 8) := hp
  let M := DegreeEightCanonicalCatalogue.primitiveLiteralMatch
    S8TransitiveCanonicalCoverage.publishedClassification J (by simp only [Nat.card_fin])
  exact (CoprimeNilpotentProductGenerators.genRank_mulEquiv M.groupEquiv).le.trans
    (primitive_interface_rank M.index M.primitive_index)

end SymmetricSubgroupAsymptotics.PrimitiveEightOrdinaryGeneratorsFromCanonicalCoverage
