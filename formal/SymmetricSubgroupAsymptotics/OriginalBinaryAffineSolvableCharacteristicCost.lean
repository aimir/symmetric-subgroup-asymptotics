import SymmetricSubgroupAsymptotics.ActualWreathSolvableChiefProfile
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointCharacteristicCost
import SymmetricSubgroupAsymptotics.BinaryGeneralLinearPrimeMultiplicity

/-! The actual solvable-complement branch of binary affine block costs.
The translation head is followed by the SAME genuine quotient chief
trace, with zero nonabelian charge proved from actual solvability.
Joint odd-prime multiplicities replace the old logarithmic allowance.
No conclusion about nonsolvable complements is made. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineSolvableCharacteristicCost
open OriginalAffineBlockCharacteristicHead ActualWreathChiefOrderDivisibility
open CharacteristicChiefPrimePowerCosts CharacteristicChiefPrimeMultiplicityBudget

def solvablePrimaryCost (d e : ℕ) : ℕ :=
  (d + d*(d-1)/2) * e.choose (e/2) +
    primeMultiplicityAway 2 (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)))

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem translation_quotient_solvable_of_complement (x : block.Fibre)
    [IsSolvable (P.complement x)] : IsSolvable (block.Component ⧸ P.V) := by
  let e : (block.Component ⧸ P.V) ≃* P.complement x :=
    (QuotientGroup.quotientMulEquivOfEq (P.complementProjection_ker x).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (P.complementProjection x) (P.complementProjection_surjective x))
  exact solvable_of_solvable_injective (f := e.toMonoidHom) e.injective

theorem exists_solvable_tail_profile
    (hsolv : IsSolvable (block.Component ⧸ P.V)) (i : block.Points) :
    ∃ c : ℕ,
      ActualWreathOrdinaryChiefRecurrence.ChiefCost i (quotientState J block P) c ∧
      ∃ prof : DivisibleProfile (Fintype.card block.Points) c
          (Nat.card (block.Component ⧸ P.V)),
        prof.simpleRank = 0 ∧ MarkedC4.genRank J ≤
          (headCharge J block P i).capacity + c + MarkedC4.genRank block.Top := by
  let S := quotientState J block P
  letI : IsSolvable S.D := by
    change IsSolvable (block.Component ⧸ P.V)
    exact hsolv
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  obtain ⟨c,hc,prof,hzero⟩ := ActualWreathSolvableChiefProfile.exists_divisible_profile S i hI
  have hhead : ActualWreathOrdinaryChiefRecurrence.ChiefCost i
      (OriginalBlockOrdinaryCompressionState.initialState J block)
      ((headCharge J block P i).capacity + c) :=
    .elementary (OriginalBlockOrdinaryCompressionState.initialState J block)
      (block.Component ⧸ P.V) (QuotientGroup.mk' P.V) (QuotientGroup.mk'_surjective P.V)
      (translation_kernel_minimal J block P) (translationChart J block P) c hc
  exact ⟨c,hc,prof,hzero,ActualWreathOrdinaryChiefRecurrence.genRank_le_cost_add_top hhead⟩

theorem genRank_le_solvable_cost (hp : P.p = 2) (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points)
    (hsolv : IsSolvable (block.Component ⧸ P.V)) :
    MarkedC4.genRank J ≤ solvablePrimaryCost (translationDimension J block P) e +
      MarkedC4.genRank block.Top := by
  let d := translationDimension J block P
  obtain ⟨c,hc,prof,hzero,hrank⟩ := exists_solvable_tail_profile J block P hsolv i
  have htR : (Fintype.card block.Points : ℝ) = (2 : ℝ)^e := by exact_mod_cast ht
  have cancel (a b : ℝ) : a*(2 : ℝ)^e*b/(2 : ℝ)^e = a*b := by
    rw [mul_right_comm,mul_div_cancel_right₀ _ (by positivity : (2 : ℝ)^e ≠ 0)]
  have hhead := (headCharge J block P i).primePower 2 e Nat.prime_two ht
  simp only [show 2-1 = (1 : ℕ) by omega,mul_one,headCharge_dimension] at hhead
  rw [htR,cancel] at hhead
  have htail := profile_cost_le_primePower_valuation prof 2 e Nat.prime_two ht
    (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
  simp only [show 2-1 = (1 : ℕ) by omega,mul_one,hzero,add_zero] at htail
  rw [htR,cancel] at htail
  have hv := OriginalBinaryAffineCharacteristicCost.translation_quotient_defining_valuation_le
    J block P
  rw [hp] at hv
  have hvR : ((Nat.card (block.Component ⧸ P.V)).factorization 2 : ℝ) ≤
      ((d*(d-1)/2 : ℕ) : ℝ) := by exact_mod_cast hv
  have hvMul := mul_le_mul_of_nonneg_right hvR
    (show 0 ≤ (e.choose (e/2) : ℝ) by positivity)
  have hdvd := OriginalBinaryAffineJointCharacteristicCost.translation_quotient_card_dvd_GL
    J block P hp
  have hother := otherDimension_le_primeMultiplicityAway prof 2
    (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)))
    (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).ne' hdvd
  have hotherR : (otherDimensionAt 2 prof.charges : ℝ) ≤
      primeMultiplicityAway 2 (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) := by
    exact_mod_cast hother
  have hrankR : (MarkedC4.genRank J : ℝ) ≤
      ((headCharge J block P i).capacity : ℝ) + (c : ℝ) + MarkedC4.genRank block.Top := by
    exact_mod_cast hrank
  have hfinal : (MarkedC4.genRank J : ℝ) ≤
      ((solvablePrimaryCost d e + MarkedC4.genRank block.Top : ℕ) : ℝ) := by
    simp only [solvablePrimaryCost,Nat.cast_add,Nat.cast_mul]
    change (MarkedC4.genRank J : ℝ) ≤
      ((d : ℝ) + ((d*(d-1)/2 : ℕ) : ℝ)) * (e.choose (e/2) : ℝ) +
        primeMultiplicityAway 2 (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) +
          MarkedC4.genRank block.Top
    change ((headCharge J block P i).capacity : ℝ) ≤ (d : ℝ) * (e.choose (e/2) : ℝ) at hhead
    nlinarith
  exact_mod_cast hfinal

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineSolvableCharacteristicCost
