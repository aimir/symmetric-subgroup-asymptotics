import SymmetricSubgroupAsymptotics.OriginalFourPointSharedTranslationKernel
import SymmetricSubgroupAsymptotics.OriginalFourPointZeroOddCharacteristicCost
import SymmetricSubgroupAsymptotics.ActualWreathSixOrderChooseCost
import SymmetricSubgroupAsymptotics.OriginalBinaryAffineJointCharacteristicCost
import SymmetricSubgroupAsymptotics.BinaryAffineJointSelectedWindowNumerics

/-! The genuine shared binary head cost for an actual primitive
four-point component. Zero odd image has no linear-base charge; nonzero
odd image shares the translations in half as many positions and pays the
SAME order-six tail. The final max bound has no odd-image premise and
leaves the actual top rank explicit. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalFourPointSharedChooseCost
open OriginalAffineBlockCharacteristicHead ActualWreathChooseDivisorCapacity

variable {n : ℕ} (J : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive J (Fin n)] {x₀ : Fin n}
    (block : OriginalMinimalBlock (A := J) x₀) [Fintype block.Points]

local instance fibreNontrivial : Nontrivial block.Fibre :=
  Finite.one_lt_card_iff_nontrivial.mp (by
    have h := block.degrees_ge_two.1
    omega)

variable (P : PrimitiveAffineProfile block.Component block.Fibre)

theorem quotientState_card_dvd_six (hp : P.p = 2)
    (hdim : translationDimension J block P = 2) : Nat.card (quotientState J block P).D ∣ 6 := by
  have hh := OriginalBinaryAffineJointCharacteristicCost.translation_quotient_card_dvd_GL
    J block P hp
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [BinaryAffineJointSelectedWindowNumerics.matrix_GL_card_eq_order]
    decide +kernel
  have hcard : Nat.card (Matrix.GeneralLinearGroup
      (Fin (translationDimension J block P)) (ZMod 2)) = 6 :=
    (congrArg (fun d : ℕ => Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2))) hdim).trans hGL
  change Nat.card (block.Component ⧸ P.V) ∣ 6
  exact hcard ▸ hh

theorem genRank_le_half_add_primary_choose (hfour : Nat.card block.Fibre = 4)
    (hp : P.p = 2) (hdim : translationDimension J block P = 2)
    (hO : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) ≠ ⊥)
    (i : block.Points) (a : ℕ) (hdiv : 2 ^ a ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤ (Fintype.card block.Points : ℝ) / 2 +
      (Fintype.card block.Points : ℝ) * primaryRate 2 a +
      (Fintype.card block.Points : ℝ) / (2 : ℝ) ^ a + MarkedC4.genRank block.Top := by
  have hI : 2 ≤ Fintype.card block.Points := by
    simpa only [Fintype.card_eq_nat_card] using block.degrees_ge_two.2
  have htail := ActualWreathSixOrderChooseCost.genRank_le_primary_choose_add_primeTo
    (quotientState J block P) i hI (quotientState_card_dvd_six J block P hp hdim) a hdiv
  have hhead := OriginalFourPointSharedTranslationKernel.genRank_le_half_add_quotient
    J block P hfour hp hO
  have hheadR : (MarkedC4.genRank J : ℝ) ≤ (MarkedC4.genRank (quotientState J block P).A : ℝ) +
      (Nat.card block.Points / 2 : ℕ) := by exact_mod_cast hhead
  have hhalf : ((Nat.card block.Points / 2 : ℕ) : ℝ) ≤ (Fintype.card block.Points : ℝ) / 2 := by
    simpa only [Fintype.card_eq_nat_card] using
      (Nat.cast_div_le (m := Nat.card block.Points) (n := 2) (α := ℝ))
  linarith

theorem genRank_le_shared_primary_choose (hfour : Nat.card block.Fibre = 4)
    (hp : P.p = 2) (hdim : translationDimension J block P = 2)
    (i : block.Points) (a : ℕ) (hdiv : 2 ^ a ∣ Fintype.card block.Points) :
    (MarkedC4.genRank J : ℝ) ≤
      max (2 * (Fintype.card block.Points : ℝ) * primaryRate 2 a)
        ((Fintype.card block.Points : ℝ) / 2 + (Fintype.card block.Points : ℝ) * primaryRate 2 a +
          (Fintype.card block.Points : ℝ) / (2 : ℝ) ^ a) + MarkedC4.genRank block.Top := by
  classical
  by_cases hzero : BinaryPlaneWreathActualOddKernel.oddKernel
      (FourPointBlockAffineCoordinates.linearImage block.map block.map_equivariant block.base hfour) = ⊥
  · have hh := OriginalFourPointZeroOddCharacteristicCost.genRank_le_primary_choose
      J block P hfour hp hzero i a hdiv
    simp only [hdim,Nat.cast_ofNat] at hh
    exact hh.trans (add_le_add (le_max_left _ _) (le_rfl :
      (MarkedC4.genRank block.Top : ℝ) ≤ MarkedC4.genRank block.Top))
  · exact (genRank_le_half_add_primary_choose J block P hfour hp hdim hzero i a hdiv).trans
      (add_le_add (le_max_right _ _) (le_rfl :
        (MarkedC4.genRank block.Top : ℝ) ≤ MarkedC4.genRank block.Top))

end SymmetricSubgroupAsymptotics.OriginalFourPointSharedChooseCost
