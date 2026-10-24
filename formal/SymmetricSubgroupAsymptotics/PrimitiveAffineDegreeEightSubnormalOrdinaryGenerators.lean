import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightConjugatedCoordinates
import SymmetricSubgroupAsymptotics.BinaryTripleModelSubnormalAction
import SymmetricSubgroupAsymptotics.SubnormalSemidirectTranslation
import SymmetricSubgroupAsymptotics.PrimitiveAffineOrdinaryGeneratorRank
import SymmetricSubgroupAsymptotics.BlockSubnormalOrdinaryGeneratorInduction

/-! Every actual subnormal subgroup of a primitive affine group of
degree eight has at most three ordinary generators. The actual coordinate
range is one of the three already checked complement models. Zero right
image lies in the original translations; nonzero image is irreducible,
forces all translations, and costs one translation plus two image
generators. The original minimal-block installer has no local certificate
or current-degree MN premise. -/
set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative Matrix

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
open SemidirectProduct

theorem subnormal_genRank_le_three_of_degreeEight
    {G X : Type} [Group G] [Finite G] [Finite X] [Nontrivial X]
    [MulAction G X] [FaithfulSMul G X]
    (P : PrimitiveAffineProfile G X) (hprimitive : MulAction.IsPreprimitive G X)
    (x : X) (hdegree : Nat.card X = 8)
    (N : Subgroup G) (hN : N.IsSubnormal) : MarkedC4.genRank N ≤ 3 := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  letI : Nontrivial P.V := (P.pointEquiv x).symm.injective.nontrivial
  let H := P.complement x
  let φ := P.complementAction x
  let u : P.V ⋊[φ] H ≃* G := P.semidirectEquiv x
  letI : Finite (P.V ⋊[φ] H) := Finite.of_equiv G u.symm.toEquiv
  let L := N.map u.symm.toMonoidHom
  let E := L.map (rightHom : P.V ⋊[φ] H →* H)
  have hL : L.IsSubnormal := hN.map u.symm.surjective
  have hE : E.IsSubnormal := hL.map rightHom_surjective
  let eN := N.equivMapOfInjective u.symm.toMonoidHom u.symm.injective
  apply (CoprimeNilpotentProductGenerators.genRank_mulEquiv eN).le.trans
  by_cases hzero : E = ⊥
  · have hright : ∀ g : L, g.val.right = 1 := by
      intro g
      have hg : g.val.right ∈ E := ⟨g.val,g.property,rfl⟩
      rw [hzero] at hg
      exact Subgroup.mem_bot.mp hg
    have hinj : Function.Injective (fun g : L => g.val.left) := by
      intro a b he
      apply Subtype.ext
      apply SemidirectProduct.ext
      · exact he
      · exact (hright a).trans (hright b).symm
    have hV : Nat.card P.V = 8 := (Nat.card_congr (P.pointEquiv x)).trans hdegree
    have hcard : Nat.card L ≤ 2^3 := by
      exact (Nat.card_le_card_of_injective _ hinj).trans_eq hV
    exact FiniteGroupBinaryOrderGenerators.genRank_le_of_card_le_two_pow L 3 hcard
  · obtain ⟨i,a,ha⟩ := P.exists_coordinates_range_model hprimitive x hdegree
    let e : H ≃* PrimitiveAffineDegreeEightThreeImages.models i :=
      (MonoidHom.ofInjective (P.complementCoordinateMap_injective x a)).trans
        (MulEquiv.subgroupCongr ha)
    have hact : ∀ h v, (e h).val.val *ᵥ (a v).toAdd = (a (φ h v)).toAdd :=
      P.complementCoordinateMap_action x a
    have hirr := BinaryTripleModelSubnormalAction.subnormal_image_irreducible
      φ a i e hact (P.complementAction_ordinary_irreducible hprimitive x) E hE hzero
    have hrank := BinaryTripleModelSubnormalAction.subnormal_image_genRank_le_two i e E hE
    exact (SubnormalSemidirectTranslation.genRank_le_image_add_one φ
      (P.complementAction_injective x) L hL hzero hirr).trans
        (Nat.add_le_add_right hrank 1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators

theorem subgroup_half_degree_generators (n : ℕ) (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] (ω₀ : Fin n)
    (D : OriginalMinimalBlock (A := J) ω₀)
    (P : PrimitiveAffineProfile D.Component D.Fibre) (hdegree : Nat.card D.Fibre = 8)
    (hbelow : ∀ k : ℕ, k < n → ∀ K : Subgroup (Equiv.Perm (Fin k)),
      (k = 3 → K ≠ ⊤) →
        ∃ S : Finset K, Subgroup.closure (S : Set K) = ⊤ ∧ 2 * S.card ≤ k) :
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧ 2 * S.card ≤ n := by
  letI : Nontrivial D.Fibre := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let origin : D.Fibre := ⟨ω₀,D.map_base⟩
  exact BlockSubnormalOrdinaryGeneratorInduction.subgroup_half_degree_generators n J ω₀ D 3
    (fun N hN => P.subnormal_genRank_le_three_of_degreeEight
      D.component_preprimitive origin hdegree N hN)
    (by omega) hbelow

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators
