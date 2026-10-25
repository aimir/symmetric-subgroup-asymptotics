import SymmetricSubgroupAsymptotics.PrimitiveSocleOneFactorRootCountIndexOrdinaryTail
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeOrdinaryGenerators
import SymmetricSubgroupAsymptotics.CFSGTwistedDProperIndexOrderBudget
import SymmetricSubgroupAsymptotics.CFSGTwistedDOuterBudget
import SymmetricSubgroupAsymptotics.CFSGSimpleIndexTransport

/-! Every original nonsplit D model of rank at least four in the
ordinary one-factor tail. Its actual relative parameter homomorphisms
give 2*r*f generators, and the original q^(r-2) proper-index bound
pays that count. The original field, model, quotient and isomorphism
remain literal; no global generation or permutation input is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDOneFactorOrdinaryTail
open PrimitiveSocleRawStructure

variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (D : NonaffineData G X)

theorem genRank_le_ceiling (hk : D.factorCount = 1)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (hn : 128 ≤ Nat.card X) :
    MarkedC4.genRank G ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  classical
  obtain ⟨s, rfl⟩ : ∃ s : ℕ, r = s+4 := ⟨r-4, by omega⟩
  letI : IsSimpleGroup (CFSG.Models.TwistedD (s+4) q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedD (s+4) q) := Finite.of_equiv D.Simple e.toEquiv
  have hnoncomm : ¬ IsMulCommutative (CFSG.Models.TwistedD (s+4) q) := by
    intro h
    apply D.noncommutative
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.injective
    simpa only [map_mul] using (isMulCommutative_iff.mp h) (e x) (e y)
  obtain ⟨S, hS, hcard⟩ :=
    CFSGTwistedDRelativeOrdinaryGenerators.original_exists_generating_finset s q
  let U := S.image e.symm
  have hU : Subgroup.closure (U : Set D.Simple) = ⊤ := by
    rw [Finset.coe_image]
    change Subgroup.closure (e.symm.toMonoidHom '' (S : Set _)) = ⊤
    rw [← MonoidHom.map_closure, hS]
    exact Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective
  have hcount : (2*(s+4))*q.exponent ≤ 4*(q.exponent*(s+2)) := by
    nlinarith only [Nat.zero_le (s*q.exponent)]
  have hUcard : U.card ≤ 4*(q.exponent*(s+2)) :=
    Finset.card_image_le.trans (hcard.trans hcount)
  have hindex : ∀ H : Subgroup D.Simple, H ≠ ⊤ → q.order^(s+2) ≤ H.index := by
    intro H hH
    have hmap : H.map e.toMonoidHom ≠ ⊤ := by
      intro ht
      apply hH
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
    have hi := CFSGTwistedDProperIndexOrderBudget.typeTwistedD_field_power_le_proper_index
      (s+4) (by omega) q (H.map e.toMonoidHom) hmap
    have hidx : (H.map e.toMonoidHom).index = H.index := H.index_map_equiv e
    rw [hidx] at hi
    simpa only [show s+4-2 = s+2 by omega] using hi
  obtain ⟨ell, hell⟩ := exists_leastProperIndex D.Simple
  have houter : SufficientOuterOrderBudget ell (Nat.card (Outer D.Simple)) := by
    rw [CFSGReduction.outer_card_congr e]
    exact CFSGReduction.typeTwistedD_sufficientOuterBudget (s+4) (by omega) q hnoncomm ell
      (CFSGReduction.leastProperIndex_of_mulEquiv e ell hell)
  exact PrimitiveSocleOneFactorRootCountIndexOrdinaryTail.genRank_le_ceiling
    D hk q (s+2) (by omega) U hU hUcard hindex ell hell houter hn

theorem exists_generating_finset (hk : D.factorCount = 1)
    (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    (e : D.Simple ≃* CFSG.Models.TwistedD r q) (hn : 128 ≤ Nat.card X) :
    ∃ U : Finset G, Subgroup.closure (U : Set G) = ⊤ ∧
      U.card ≤ traceyPermutationGeneratorCeiling (Nat.card X) := by
  obtain ⟨U, hU, hgen⟩ := MarkedC4.genRank_spec (G := G)
  exact ⟨U, hgen, hU.le.trans (genRank_le_ceiling D hk r hr q e hn)⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleTwistedDOneFactorOrdinaryTail
