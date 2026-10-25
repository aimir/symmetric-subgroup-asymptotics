import SymmetricSubgroupAsymptotics.CFSGUnitaryRadicalFrattiniOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGUnitaryBinaryRankThreeFrattiniHead

/-! Ordinary generators of the SAME actual upper product are a union
of actual radical and middle generators. Combining the checked Frattini
radical bound with the binary rank-three head supplies the rank-five
small-degree edge without classifying actions or assuming a pair. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitaryUpperProductOrdinaryHeads
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent
open CFSGTwistedAUnitaryCoordinates

theorem upper_product_genRank_le (q : CFSG.PrimePower) (s : ℕ) :
    MarkedC4.genRank (naturalUnipotent (s+2) q) ≤
      MarkedC4.genRank (fixedRadical q s)+MarkedC4.genRank (naturalUnipotent s q) := by
  classical
  obtain ⟨R,hRcard,hR⟩ := MarkedC4.genRank_spec (G := fixedRadical q s)
  obtain ⟨M,hMcard,hM⟩ := MarkedC4.genRank_spec (G := naturalUnipotent s q)
  let T := R.image (radicalUpperHom q s) ∪ M.image (middleUnipotentHom q s)
  let H := Subgroup.closure (T : Set (naturalUnipotent (s+2) q))
  have hRle : (radicalUpperHom q s).range ≤ H := by
    have hh : (Subgroup.closure (R : Set (fixedRadical q s))).map (radicalUpperHom q s) ≤ H := by
      rw [MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x,hx,rfl⟩
      exact Subgroup.subset_closure (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    rw [hR,←MonoidHom.range_eq_map] at hh
    exact hh
  have hMle : (middleUnipotentHom q s).range ≤ H := by
    have hh : (Subgroup.closure (M : Set (naturalUnipotent s q))).map (middleUnipotentHom q s) ≤ H := by
      rw [MonoidHom.map_closure]
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨x,hx,rfl⟩
      exact Subgroup.subset_closure (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    rw [hM,←MonoidHom.range_eq_map] at hh
    exact hh
  have hT : H = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨⟨r,m⟩,rfl⟩ := upperProduct_surjective q s g
    change radicalUpperHom q s r*middleUnipotentHom q s m ∈ H
    have hr : radicalUpperHom q s r ∈ H := hRle ⟨r,rfl⟩
    have hm : middleUnipotentHom q s m ∈ H := hMle ⟨m,rfl⟩
    exact H.mul_mem hr hm
  have hcard : T.card ≤ R.card+M.card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
  exact (MarkedC4.genRank_le hT).trans (hcard.trans (by omega))

theorem binary_rank_five_upper_le_eleven (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (naturalUnipotent 5 q) ≤ 11 := by
  have he := ClassicalClassEquationCapacity.exponent_eq_one_of_prime_order q (by rw [hq]; decide)
  have hrad := CFSGUnitaryRadicalFrattiniOrdinaryGenerators.radical_genRank_le q 3
  have hrad8 : MarkedC4.genRank (fixedRadical q 3) ≤ 8 := by simpa only [he] using hrad
  have hmid := CFSGUnitaryBinaryRankThreeFrattiniHead.upper_genRank_le_three q hq
  exact (upper_product_genRank_le q 3).trans (by omega)

theorem binary_rank_five_model_le_twelve (q : CFSG.PrimePower) (hq : q.order = 2) :
    MarkedC4.genRank (CFSG.Models.TwistedA 5 q) ≤ 12 := by
  letI : Finite (Fixed 5 q) := originalFixed_finite q 5 (by omega)
  let A := commutator (Fixed 5 q)
  let U := originalUnipotent 5 q
  have hUA : U ≤ A := originalUnipotent_le_derived q 2
  let P : Sylow q.prime A :=
    (originalSylow q 5 (by omega)).subtype (originalSylow_le_derived q 2)
  let eP : P ≃* naturalUnipotent 5 q :=
    (U.subgroupOfEquivOfLe hUA).trans
      (MonoidHom.ofInjective (unipotentToOriginalFixed_injective 5 (by omega) q)).symm
  have hP : MarkedC4.genRank P ≤ 11 := by
    rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv eP]
    exact binary_rank_five_upper_le_eleven q hq
  have hh := GoodSylowSelectedRankOrdinaryGenerators.genRank_le_of_surjective q.prime
    (originalDerived_goodSylowPrime q 2) P (QuotientGroup.mk' (Subgroup.center A))
    (QuotientGroup.mk'_surjective _)
  exact hh.trans (Nat.add_le_add_right hP 1)

theorem exists_generating_finset (q : CFSG.PrimePower) (hq : q.order = 2) :
    ∃ S : Finset (CFSG.Models.TwistedA 5 q), Subgroup.closure (S : Set (CFSG.Models.TwistedA 5 q)) = ⊤ ∧ S.card ≤ 12 := by
  letI : Finite (Fixed 5 q) := originalFixed_finite q 5 (by omega)
  letI : Finite (CFSG.Models.TwistedA 5 q) := by
    change Finite (commutator (Fixed 5 q) ⧸ Subgroup.center (commutator (Fixed 5 q)))
    infer_instance
  obtain ⟨S,hcard,hgen⟩ := MarkedC4.genRank_spec (G := CFSG.Models.TwistedA 5 q)
  exact ⟨S,hgen,hcard.le.trans (binary_rank_five_model_le_twelve q hq)⟩

end SymmetricSubgroupAsymptotics.CFSGUnitaryUpperProductOrdinaryHeads
