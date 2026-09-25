import SymmetricSubgroupAsymptotics.PrimeAbelianization
import SymmetricSubgroupAsymptotics.BinaryCoverage
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! The prime-character quotient is the actual Frattini quotient of a finite p-group. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]

/-- Every prime-field character kills the original Frattini subgroup. -/
theorem frattini_le_primeCharacter_ker (χ : G →* Multiplicative (ZMod p)) :
    frattini G ≤ χ.ker := by
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by simp
  letI : Fact (Nat.card (Multiplicative (ZMod p))).Prime :=
    ⟨by simpa only [hcard] using (Fact.out : p.Prime)⟩
  rcases χ.range.eq_bot_or_eq_top_of_prime_card with hχ | hχ
  · intro x _
    have hx : χ x ∈ χ.range := ⟨x,rfl⟩
    rwa [hχ] at hx
  · have hbot : IsCoatom (⊥ : Subgroup (Multiplicative (ZMod p))) := by
      refine ⟨bot_ne_top,?_⟩
      intro H hH
      exact H.eq_bot_or_eq_top_of_prime_card.resolve_left (ne_of_gt hH)
    simpa using frattini_le_coatom
      (Subgroup.isCoatom_comap_of_surjective (MonoidHom.range_eq_top.mp hχ) hbot)

/-- The evaluation quotient keeps precisely the intersection of the
maximal subgroups of the actual finite p-group. -/
theorem primeAbelianizationGroupMap_ker [Finite G] (hG : IsPGroup p G) :
    (primeAbelianizationGroupMap p G).ker = frattini G := by
  apply le_antisymm
  · simp only [frattini,Order.radical,le_iInf_iff]
    intro H hH
    haveI : Group.IsNilpotent G := hG.isNilpotent
    haveI : H.Normal := Subgroup.NormalizerCondition.normal_of_coatom H
      Group.normalizerCondition_of_isNilpotent hH
    have hcard : Nat.card (G ⧸ H) = p :=
      H.index_eq_card.symm.trans (pGroup_coatom_index hG H hH)
    let e : G ⧸ H ≃* Multiplicative (ZMod p) :=
      mulEquivOfPrimeCardEq hcard (by simp)
    let χ : G →* Multiplicative (ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' H)
    intro x hx
    have heval : primeAbelianizationMap p G (Additive.ofMul x) = 0 := hx
    have hχ : χ x = 1 := by
      have he := congrArg (fun z : PrimeAbelianization p G =>
        z (AddMonoidHom.toMultiplicativeRight.symm χ)) heval
      exact he
    have hxH : QuotientGroup.mk' H x = 1 := by
      apply e.injective
      exact hχ.trans (map_one e).symm
    simpa only [QuotientGroup.ker_mk'] using
      (show x ∈ (QuotientGroup.mk' H).ker from hxH)
  · intro x hx
    change primeAbelianizationMap p G (Additive.ofMul x) = 0
    apply LinearMap.ext
    intro χ
    exact frattini_le_primeCharacter_ker p G
      (AddMonoidHom.toMultiplicativeRight χ) hx

/-- An explicit isomorphism from the actual Frattini quotient to the
prime-field vector model used by the Hom and Schur bounds. -/
def primeFrattiniQuotientEquiv [Finite G] (hG : IsPGroup p G) :
    G ⧸ frattini G ≃* Multiplicative (PrimeAbelianization p G) :=
  (QuotientGroup.quotientMulEquivOfEq (primeAbelianizationGroupMap_ker p G hG).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (primeAbelianizationGroupMap p G)
      (primeAbelianizationGroupMap_surjective p G))

@[simp] theorem primeFrattiniQuotientEquiv_apply [Finite G] (hG : IsPGroup p G) (x : G) :
    primeFrattiniQuotientEquiv p G hG (QuotientGroup.mk' (frattini G) x) =
      primeAbelianizationGroupMap p G x := rfl

/-- The vector-space rank is the exact logarithm of the original
Frattini-quotient order. -/
theorem primeFrattini_quotient_card [Finite G] (hG : IsPGroup p G) :
    Nat.card (G ⧸ frattini G) =
      p ^ Module.finrank (ZMod p) (PrimeAbelianization p G) := by
  rw [Nat.card_congr (primeFrattiniQuotientEquiv p G hG).toEquiv]
  simpa using Module.natCard_eq_pow_finrank (K := ZMod p) (V := PrimeAbelianization p G)

/-- A separately proved bound for the actual abelian quotient gives the
same numerical bound for the actual source rank; no rank premise is hidden. -/
theorem primeFrattini_rank_le_of_card_le [Finite G] (hG : IsPGroup p G) (n : ℕ)
    (hcard : Nat.card (G ⧸ frattini G) ≤ p^n) :
    Module.finrank (ZMod p) (PrimeAbelianization p G) ≤ n := by
  rw [primeFrattini_quotient_card p G hG] at hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard

end SymmetricSubgroupAsymptotics
