import SymmetricSubgroupAsymptotics.NormalIsotypicCoordinateOrigins
import SymmetricSubgroupAsymptotics.TwoMinimalNormalIsotypicOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawChart
import SymmetricSubgroupAsymptotics.PrimitiveSocleMinimalNormalAlternatives

/-! Actual primitive full-socle compression with the original common
simple group retained. The one/two-minimal-normal cover is proved from
the actual centralizer alternatives before ordinary costs are charged.
No simple two-generation, CFSG generator hypothesis, or fitted numerical
aggregate is supplied. The original quotientG/socle(G) remains literal. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleIsotypicOrdinaryCompression
open PrimitiveSocleRawStructure PrimitiveSocleONanScottHelpers

private theorem noncommutative_of_coordinates {A T I : Type} [Group A] [Group T]
    (e : A ≃* (I → T)) (i : I) (hT : ¬ IsMulCommutative T) :
    ¬ IsMulCommutative A := by
  intro hA
  apply hT
  apply isMulCommutative_iff.mpr
  intro x y
  have hh := congrArg (fun z : A => e z i)
    (isMulCommutative_iff.mp hA
      (e.symm (Pi.mulSingle i x)) (e.symm (Pi.mulSingle i y)))
  simpa only [map_mul,Pi.mul_apply,MulEquiv.apply_symm_apply,Pi.mulSingle_eq_same] using hh

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X] [MulAction.IsPreprimitive G X]
    (D : NonaffineData G X)

include D in
/-- The full socle has an ACTUAL one- or two-minimal-normal cover.
Nonabelianness of the selected minimal normal follows from its retained
coordinates in the original homogeneous full socle. -/
theorem exists_minimal_normal_cover :
    ∃ E : Subgroup G, IsMinimalNormalSubgroup E ∧ ¬ IsMulCommutative E ∧
      (finiteGroupSocle G = E ∨ ∃ F : Subgroup G,
        IsMinimalNormalSubgroup F ∧ Disjoint E F ∧ finiteGroupSocle G = E⊔F) := by
  let N := finiteGroupSocle G
  letI : Nonempty (Fin D.factorCount) := ⟨⟨0,D.factorCount_pos⟩⟩
  letI : Nontrivial N := D.socleEquiv.symm.injective.nontrivial
  letI : Nontrivial G := N.subtype_injective.nontrivial
  obtain ⟨E,hE⟩ := exists_minimalNormal (G := G)
  letI : E.Normal := hE.1
  have hEN : E ≤ N := by
    intro x hx
    exact Subgroup.subset_normalClosure ⟨E,hE,hx⟩
  have hT := centerless_of_nonabelian_simple D.Simple D.noncommutative
  let e := NormalIsotypicCoordinateOrigins.coordinates N E hEN D.socleEquiv hT
  let i := Classical.choice
    (NormalIsotypicCoordinateOrigins.coordinates_nonempty N E hEN D.socleEquiv hT hE.2.1)
  have hnc : ¬ IsMulCommutative E := noncommutative_of_coordinates e i D.noncommutative
  by_cases hc : Subgroup.centralizer (E : Set G) = ⊥
  · exact ⟨E,hE,hnc,Or.inl (full_socle_eq_of_centralizer_bot E hE hc)⟩
  · obtain ⟨hC,hdis,hs,_,_⟩ := centralizer_regular_alternative (X := X) E hE hnc hc
    exact ⟨E,hE,hnc,Or.inr ⟨Subgroup.centralizer (E : Set G),hC,hdis,hs⟩⟩

/-- The ordinary debt of the full original primitive socle is at most
twice the genuine rank of its retained common simple group. -/
theorem genRank_le_twice_simple_add_quotient :
    MarkedC4.genRank G ≤ 2*MarkedC4.genRank D.Simple+
      MarkedC4.genRank (G ⧸ finiteGroupSocle G) := by
  let N := finiteGroupSocle G
  have hT := centerless_of_nonabelian_simple D.Simple D.noncommutative
  obtain ⟨E,hE,_,hcover⟩ := exists_minimal_normal_cover D
  letI : E.Normal := hE.1
  have hEN : E ≤ N := by
    intro x hx
    exact Subgroup.subset_normalClosure ⟨E,hE,hx⟩
  let eE := NormalIsotypicCoordinateOrigins.coordinates N E hEN D.socleEquiv hT
  let i := Classical.choice
    (NormalIsotypicCoordinateOrigins.coordinates_nonempty N E hEN D.socleEquiv hT hE.2.1)
  rcases hcover with hsingle | ⟨F,hF,hdis,hs⟩
  · have hh := MinimalNormalIsotypicRelativeOrdinaryGenerators.genRank_le E eE i hE
    have hquot : MarkedC4.genRank (G ⧸ E) = MarkedC4.genRank (G ⧸ finiteGroupSocle G) :=
      CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hsingle.symm)
    rw [hquot] at hh
    omega
  · letI : F.Normal := hF.1
    have hFN : F ≤ N := by
      intro x hx
      exact Subgroup.subset_normalClosure ⟨F,hF,hx⟩
    let eF := NormalIsotypicCoordinateOrigins.coordinates N F hFN D.socleEquiv hT
    let j := Classical.choice
      (NormalIsotypicCoordinateOrigins.coordinates_nonempty N F hFN D.socleEquiv hT hF.2.1)
    have hh := TwoMinimalNormalIsotypicOrdinaryGenerators.genRank_le E F eE eF i j hE hF hdis
    have hquot : MarkedC4.genRank (G ⧸ (E⊔F)) =
        MarkedC4.genRank (G ⧸ finiteGroupSocle G) :=
      CoprimeNilpotentProductGenerators.genRank_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hs.symm)
    rw [hquot] at hh
    exact hh

theorem exists_generating_finset :
    ∃ s : Finset G, Subgroup.closure (s : Set G) = ⊤ ∧
      s.card ≤ 2*MarkedC4.genRank D.Simple+MarkedC4.genRank (G ⧸ finiteGroupSocle G) := by
  obtain ⟨s,hs,hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨s,hgen,hs.le.trans (genRank_le_twice_simple_add_quotient D)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleIsotypicOrdinaryCompression
