import SymmetricSubgroupAsymptotics.OriginalBinaryAffineCharacteristicCost
import SymmetricSubgroupAsymptotics.CharacteristicChiefBinaryJointBudget

/-! The joint complement-order optimization on the original block
action. The tail is the actual translation quotient, its order divides
the literal GL order, and both primary and remaining costs consume that
same order. No separate full logarithmic charge is added to the primary
valuation. The actual top rank is left explicit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointCharacteristicCost
open OriginalAffineBlockCharacteristicHead
open ActualWreathCharacteristicChiefProfile ActualWreathChiefOrderDivisibility
open CharacteristicChiefFilteredDimensions CharacteristicChiefPrimePowerCosts
open CharacteristicChiefBinaryJointBudget

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem translation_quotient_card_dvd_GL (hp : P.p = 2) :
    Nat.card (block.Component ⧸ P.V) ∣ Nat.card
      (Matrix.GeneralLinearGroup (Fin (translationDimension J block P)) (ZMod 2)) := by
  let x : block.Fibre := ⟨x₀, block.map_base⟩
  let C := P.elementaryChart block.component_preprimitive
  let eqv : (block.Component ⧸ P.V) ≃* P.complement x :=
    (QuotientGroup.quotientMulEquivOfEq (P.complementProjection_ker x).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (P.complementProjection x) (P.complementProjection_surjective x))
  rw [Nat.card_congr eqv.toEquiv]
  have hh := P.complement_card_dvd_matrix_GL block.component_preprimitive C x
  have hcard : Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod P.p)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod 2)) :=
    congrArg (fun q : ℕ => Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod q))) hp
  change Nat.card (P.complement x) ∣
    Nat.card (Matrix.GeneralLinearGroup (Fin C.d) (ZMod 2))
  rw [← hcard]
  exact hh

theorem GL_primary_cap_le_log (d : ℕ) : d*(d-1)/2 ≤
    Nat.log 2 (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) := by
  have hh := binary_factorization_le_log
    (Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)))
    (Nat.card_pos (α := Matrix.GeneralLinearGroup (Fin d) (ZMod 2))).ne'
  rw [PrimeGeneralLinearDefiningValuation.matrix_GL_defining_factorization 2 d Nat.prime_two]
    at hh
  exact hh

/-- A genuine ordinary-rank bound with one common complement-order
budget. Set A=d(d-1)/2 and L=floorlog2|GL_d(2)|: the charge is
(d+A)*choose(e,floor(e/2))+(L-A)+rank(actual Top). -/
theorem genRank_le_joint_primary_cost (hp : P.p = 2) (e : ℕ)
    (ht : Fintype.card block.Points = 2^e) (i : block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      ((translationDimension J block P +
        translationDimension J block P * (translationDimension J block P - 1) / 2 : ℕ) : ℝ) *
          (e.choose (e/2) : ℝ) +
      (Nat.log 2 (Nat.card (Matrix.GeneralLinearGroup
        (Fin (translationDimension J block P)) (ZMod 2))) -
          translationDimension J block P * (translationDimension J block P - 1) / 2 : ℕ) +
      MarkedC4.genRank block.Top := by
  obtain ⟨c, hc, ⟨prof⟩, hhead, hrank⟩ := exists_translation_head_and_tail J block P i
  have hdvd := translation_quotient_card_dvd_GL J block P hp
  have ha := dimensionAt_le_factorization prof 2 Nat.prime_two
    (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
  have hv := OriginalBinaryAffineCharacteristicCost.translation_quotient_defining_valuation_le
    J block P
  rw [hp] at hv
  have htail := cost_le_binary_joint prof.toProfile e
    (translationDimension J block P * (translationDimension J block P - 1) / 2)
    ht hdvd (Nat.card_pos (α := Matrix.GeneralLinearGroup
      (Fin (translationDimension J block P)) (ZMod 2))).ne'
    (ha.trans hv) (GL_primary_cap_le_log (translationDimension J block P))
  have hheadCost := (headCharge J block P i).primePower 2 e Nat.prime_two ht
  simp only [show 2-1 = (1 : ℕ) by omega, mul_one, headCharge_dimension] at hheadCost
  have htR : (Fintype.card block.Points : ℝ) = (2 : ℝ)^e := by exact_mod_cast ht
  have cancel (a b : ℝ) : a*(2 : ℝ)^e*b/(2 : ℝ)^e = a*b := by
    rw [mul_right_comm, mul_div_cancel_right₀ _ (by positivity : (2 : ℝ)^e ≠ 0)]
  rw [htR, cancel] at hheadCost
  have hrankR : (MarkedC4.genRank J : ℝ) ≤
      ((headCharge J block P i).capacity : ℝ) + (c : ℝ) + MarkedC4.genRank block.Top := by
    exact_mod_cast hrank
  simp only [Nat.cast_add]
  nlinarith

end SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointCharacteristicCost
