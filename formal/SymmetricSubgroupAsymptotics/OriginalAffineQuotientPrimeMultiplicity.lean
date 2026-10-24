import SymmetricSubgroupAsymptotics.OriginalAffineBlockCharacteristicHead
import SymmetricSubgroupAsymptotics.PrimitiveAffineComplementGLDivisibility
import SymmetricSubgroupAsymptotics.FiniteGroupPrimeMultiplicityGenerators
import Mathlib.Algebra.BigOperators.Fin

/-! Actual affine quotient orders divide their defining GL orders, in
every characteristic. The prime-multiplicity bound retains the SAME
complement quotient used by the ordinary chief trace. The selected
ternary cubic order is a scalar product certificate, not a group census. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.OriginalAffineQuotientPrimeMultiplicity
open OriginalAffineBlockCharacteristicHead

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem quotient_card_dvd_matrix_GL :
    Nat.card (block.Component ⧸ P.V) ∣ Nat.card
      (Matrix.GeneralLinearGroup (Fin (translationDimension J block P)) (ZMod P.p)) := by
  let x : block.Fibre := ⟨x₀,block.map_base⟩
  let C := P.elementaryChart block.component_preprimitive
  let e : (block.Component ⧸ P.V) ≃* P.complement x :=
    (QuotientGroup.quotientMulEquivOfEq (P.complementProjection_ker x).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (P.complementProjection x) (P.complementProjection_surjective x))
  rw [Nat.card_congr e.toEquiv]
  exact P.complement_card_dvd_matrix_GL block.component_preprimitive C x

theorem quotient_cardFactors_le_matrix_GL :
    ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V)) ≤
      ArithmeticFunction.cardFactors (Nat.card
        (Matrix.GeneralLinearGroup (Fin (translationDimension J block P)) (ZMod P.p))) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  exact FiniteGroupPrimeMultiplicityGenerators.cardFactors_mono_of_dvd
    (Nat.card_pos (α := block.Component ⧸ P.V)).ne'
    (Nat.card_pos (α := Matrix.GeneralLinearGroup
      (Fin (translationDimension J block P)) (ZMod P.p))).ne'
    (quotient_card_dvd_matrix_GL J block P)

theorem ternary_GL_three_cardFactors :
    ArithmeticFunction.cardFactors
      (Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3))) = 9 := by
  have hh : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) =
      ∏ i : Fin 3, (3^3-3^(i : ℕ)) := by
    simpa only [Fintype.card_eq_nat_card,Nat.card_zmod] using
      (Matrix.card_GL_field (𝔽 := ZMod 3) 3)
  rw [hh]
  change ArithmeticFunction.cardFactors 11232 = 9
  decide +kernel

theorem quotient_cardFactors_le_nine_of_ternary_cubic (hp : P.p = 3)
    (hd : translationDimension J block P = 3) :
    ArithmeticFunction.cardFactors (Nat.card (block.Component ⧸ P.V)) ≤ 9 := by
  have hh := quotient_cardFactors_le_matrix_GL J block P
  have heq : Nat.card (Matrix.GeneralLinearGroup
      (Fin (translationDimension J block P)) (ZMod P.p)) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 3)) := by rw [hp,hd]
  rw [heq,ternary_GL_three_cardFactors] at hh
  exact hh

end SymmetricSubgroupAsymptotics.OriginalAffineQuotientPrimeMultiplicity
