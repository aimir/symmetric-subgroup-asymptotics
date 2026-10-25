import SymmetricSubgroupAsymptotics.CFSGGoodSylowPrime
import SymmetricSubgroupAsymptotics.TwoConjugateSubgroupsOrdinaryGenerators
import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import SymmetricSubgroupAsymptotics.CoprimeNilpotentProductGenerators

/-! An actual conjugate-Sylow generation witness pays ordinary generators
using the order of a selected Sylow of the SAME original source. Sylow
conjugacy preserves its actual rank, and an explicit surjection retains
the derived/central-quotient passage used by original Lie models. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.GoodSylowPrimeOrderOrdinaryGenerators

variable {G : Type} [Group G] [Finite G]

private theorem rank_surjective {M : Type} [Group M]
    (f : G →* M) (hf : Function.Surjective f) : MarkedC4.genRank M ≤ MarkedC4.genRank G := by
  obtain ⟨S,hS,hgen⟩ := MarkedC4.genRank_spec (G := G)
  have hT : Subgroup.closure ((S.image f : Finset M) : Set M) = ⊤ := by
    have he := congrArg (Subgroup.map f) hgen
    simpa only [Finset.coe_image,MonoidHom.map_closure,
      Subgroup.map_top_of_surjective f hf] using he
  exact (MarkedC4.genRank_le hT).trans (Finset.card_image_le.trans hS.le)

theorem genRank_le_selected_cardFactors (p : ℕ)
    (hgood : CFSGReduction.GoodSylowPrime G p) (Q : Sylow p G) :
    MarkedC4.genRank G ≤ ArithmeticFunction.cardFactors (Nat.card Q) + 1 := by
  obtain ⟨hp,P,g,_,hgen⟩ := hgood
  letI : Fact p.Prime := ⟨hp⟩
  have he := CoprimeNilpotentProductGenerators.genRank_mulEquiv (P.equiv Q)
  have hpair := TwoConjugateSubgroupsOrdinaryGenerators.genRank_le_add_one
    (P : Subgroup G) g hgen
  rw [he] at hpair
  exact hpair.trans (Nat.add_le_add_right
    (FiniteGroupPrimeMultiplicityGenerators.genRank_le_cardFactors Q) 1)

theorem genRank_le_selected_prime_power (p a : ℕ)
    (hgood : CFSGReduction.GoodSylowPrime G p) (Q : Sylow p G)
    (hcard : Nat.card Q ∣ p ^ a) : MarkedC4.genRank G ≤ a + 1 := by
  have hc := FiniteGroupPrimeMultiplicityGenerators.cardFactors_mono_of_dvd
    (Nat.card_pos (α := Q)).ne' (pow_ne_zero a hgood.1.ne_zero) hcard
  rw [ArithmeticFunction.cardFactors_apply_prime_pow hgood.1] at hc
  exact (genRank_le_selected_cardFactors p hgood Q).trans (Nat.add_le_add_right hc 1)

theorem genRank_le_of_surjective_prime_power {M : Type} [Group M]
    (p a : ℕ) (hgood : CFSGReduction.GoodSylowPrime G p) (Q : Sylow p G)
    (hcard : Nat.card Q ∣ p ^ a) (f : G →* M) (hf : Function.Surjective f) :
    MarkedC4.genRank M ≤ a + 1 :=
  (rank_surjective f hf).trans (genRank_le_selected_prime_power p a hgood Q hcard)

end SymmetricSubgroupAsymptotics.GoodSylowPrimeOrderOrdinaryGenerators
