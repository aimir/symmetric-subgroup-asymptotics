import SymmetricSubgroupAsymptotics.PrimitiveSixTwelveSocleQuotientFromComposition
import SymmetricSubgroupAsymptotics.PrimitiveTwelveExactProfileNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileParity

/-! Exact degree6/12 profile consumers from the actual full socle. The
profile subgroup need not be identified by a finite locator: unique-minimal
containment puts the actual full socle inside it, which suffices for its
quotient-order and normal-lattice bounds. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

/-- Any nontrivial normal subgroup contained in every nontrivial normal
subgroup contains the literal full socle. -/
theorem finiteGroupSocle_le_of_unique_minimal
    {G : Type} [Group G] (E : Subgroup G) [E.Normal] (hE : E≠⊥)
    (hcontains : ∀ N : Subgroup G,N.Normal → N≠⊥ → E≤N) : finiteGroupSocle G≤E := by
  apply Subgroup.normalClosure_le_normal
  rintro g ⟨M,hM,hg⟩
  have hEM : E≤M := hcontains M hM.1 hM.2.1
  have heq : E=M := hM.2.2 E inferInstance hE hEM
  rw [heq]
  exact hg

namespace PrimitiveSixTwelveExactProfileFromComposition
open PrimitiveSocleRawStructure

variable {G : Type} [Group G] [Finite G] {r : ℕ}
    [MulAction G (Fin r)] [FaithfulSMul G (Fin r)]
    [MulAction.IsPreprimitive G (Fin r)]
    (D : ExactPrimitiveSemisimpleOuterLogProfile G r)

omit [Finite G] [MulAction G (Fin r)] [FaithfulSMul G (Fin r)]
    [MulAction.IsPreprimitive G (Fin r)] in
theorem factorCount_eq_one (hr : r=6 ∨ r=12) : D.profile.factorCount=1 := by
  have hp := D.profile.factorCount_pos
  have hf := D.profile.leastIndex_five_le
  have hd := D.profile.primitive_index_lower
  by_contra hn
  have hm : 2≤D.profile.factorCount := by omega
  have h25 : 25≤D.profile.leastIndex^D.profile.factorCount := calc
    25=5^2 := by decide
    _ ≤ D.profile.leastIndex^2 := Nat.pow_le_pow_left hf 2
    _ ≤ D.profile.leastIndex^D.profile.factorCount :=
      pow_le_pow_right₀ (by omega : 1≤D.profile.leastIndex) hm
  omega

theorem socle_quotient_card_le_two
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds) (hr : r=6 ∨ r=12) :
    Nat.card (G⧸D.profile.E)≤2 := by
  letI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hone := factorCount_eq_one D hr
  have hE := D.oneFactor_socle_nontrivial hone
  have hcontains := D.oneFactor_socle_le hone
  have hle := finiteGroupSocle_le_of_unique_minimal D.profile.E hE hcontains
  have hb : Nat.card (G⧸finiteGroupSocle G)≤2 := by
    cases Classical.choice (publishedONanScottStructure G (Fin r)) with
    | inl S =>
        exact S.sixTwelve_socle_quotient_card_le_two catalogue hindex
          (by simpa only [Nat.card_fin] using hr)
    | inr P =>
        let x : Fin r := ⟨0,by omega⟩
        have hp2 := P.prime_eq_two_of_even_degree x (by rcases hr with h|h <;> rw [h] <;> decide)
        obtain ⟨d,hd⟩ := P.degree_eq_prime_power x
        rw [hp2] at hd
        rcases hr with h|h
        · exact (PrimitiveSixExactProfileNormalGenerators.six_not_two_power d (h.symm.trans hd)).elim
        · exact (PrimitiveTwelveExactProfileNormalGenerators.twelve_not_two_power d (h.symm.trans hd)).elim
  calc
    Nat.card (G⧸D.profile.E)=D.profile.E.index := D.profile.E.index_eq_card.symm
    _ ≤ (finiteGroupSocle G).index := Subgroup.index_antitone hle
    _ = Nat.card (G⧸finiteGroupSocle G) := (finiteGroupSocle G).index_eq_card
    _ ≤ 2 := hb

include D in
theorem normal_total
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds) (hr : r=6 ∨ r=12)
    (A B : Subgroup G) (hA : A.Normal) (hB : B.Normal) : A≤B ∨ B≤A :=
  PrimitiveSixExactProfileNormalGenerators.normal_total_of_unique_minimal_small_quotient
    D.profile.E (D.oneFactor_socle_le (factorCount_eq_one D hr))
    (socle_quotient_card_le_two D catalogue hindex hr) A B hA hB

include D in
theorem normal_generating_singletons
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds) (hr : r=6 ∨ r=12)
    (N : Subgroup G) (hN : N.Normal) :
    ∃ x : Fin 1→G,Subgroup.normalClosure (Set.range x)=N :=
  normal_generating_singletons_of_finite_normal_total
    (normal_total D catalogue hindex hr) N hN

include D in
theorem quotientSocle_one
    (catalogue : PublishedPrimitiveCompositionCatalogueCorrespondence)
    (hindex : PublishedSimpleIndexBounds) (hr : r=6 ∨ r=12)
    (N : Subgroup G) [N.Normal] : SocleNormalGeneratorBound (G⧸N) 1 :=
  quotientSocleNormalGeneratorBound_one_of_normal_total
    (normal_total D catalogue hindex hr) N

end PrimitiveSixTwelveExactProfileFromComposition
end SymmetricSubgroupAsymptotics
