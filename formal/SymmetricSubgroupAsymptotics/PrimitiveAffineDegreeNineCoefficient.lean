import SymmetricSubgroupAsymptotics.CompleteCharacterIntervalTailBound
import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveSmallOrder

/-!
# The finite coefficient for the degree-nine whole-core interval

The literal block embedding bounds the ambient action by
`432^s * s!`.  At the five surviving block counts this fits respectively
under `2^19`, `2^29`, `2^40`, `2^64`, and `2^137`.  Those exact order
exponents fit the log-squared menu already at complement degree zero, so
the shared finite-axis theorem pays the complete character coefficient.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

private def degreeNinePermutationalWreathEquivProd :
    PermutationalWreathProduct block.Component block.Top block.Points ≃
      (block.Points → block.Component) × block.Top where
  toFun x := (x.left, x.right)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

include P in
/-- The exact literal wreath embedding gives the uniform order ceiling
`|U| <= 432^s s!`. -/
theorem degreeNine_ambient_card_le_wreath_ceiling
    (hr : Nat.card block.Fibre = 9) :
    Nat.card (preE7NonPairAction w U) ≤
      432 ^ Nat.card block.Points * (Nat.card block.Points).factorial := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  letI : Finite
      (PermutationalWreathProduct block.Component block.Top block.Points) :=
    Finite.of_injective (degreeNinePermutationalWreathEquivProd block)
      (degreeNinePermutationalWreathEquivProd block).injective
  have hcomponent : Nat.card block.Component ≤ 432 :=
    Nat.le_of_dvd (by norm_num) (component_card_dvd_432 block P hr)
  have htop : Nat.card block.Top ≤
      (Nat.card block.Points).factorial := by
    have h := Nat.card_le_card_of_injective block.Top.subtype
      (show Function.Injective block.Top.subtype from Subtype.val_injective)
    exact h.trans_eq Nat.card_perm
  have hwreath : Nat.card
      (PermutationalWreathProduct block.Component block.Top block.Points) =
        Nat.card block.Component ^ Nat.card block.Points *
          Nat.card block.Top := by
    rw [Nat.card_congr (degreeNinePermutationalWreathEquivProd block),
      Nat.card_prod, Nat.card_fun]
  have hambient : Nat.card (preE7NonPairAction w U) ≤
      Nat.card block.Component ^ Nat.card block.Points *
        Nat.card block.Top := by
    calc
      Nat.card (preE7NonPairAction w U) ≤ Nat.card
          (PermutationalWreathProduct block.Component block.Top
            block.Points) :=
        Nat.card_le_card_of_injective (ambientEmbedding block)
          (ambientEmbedding_injective block)
      _ = _ := hwreath
  exact hambient.trans (Nat.mul_le_mul
    (Nat.pow_le_pow_left hcomponent (Nat.card block.Points)) htop)

private theorem eight_thirds_le_log_of_sixteen_le
    (n : ℕ) (h : 16 ≤ n) :
    (8 : ℝ) / 3 ≤ Real.log (n : ℝ) := by
  have hmono : Real.log (16 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h)
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow] at hmono
  have hlogtwo : (2 : ℝ) / 3 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  norm_num at hmono
  linarith

private theorem four_le_log_of_sixtyFour_le
    (n : ℕ) (h : 64 ≤ n) :
    (4 : ℝ) ≤ Real.log (n : ℝ) := by
  have hmono : Real.log (64 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h)
  rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow] at hmono
  have hlogtwo : (2 : ℝ) / 3 < Real.log 2 :=
    lt_trans (by norm_num) Real.log_two_gt_d9
  norm_num at hmono
  linarith

include P in
/-- At every surviving block count, the exact order exponent fits the
log-squared menu at complement degree zero. -/
theorem degreeNine_exists_orderExponent_and_menuBound
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12) :
    ∃ m : ℕ,
      Nat.card (preE7NonPairAction w U) ≤ 2 ^ m ∧
      ((m * w + m * ((w + 2) / 2) : ℕ) : ℝ) ≤
        16 * (w : ℝ) * Real.log ((w + 2 : ℕ) : ℝ) ^ 2 := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  have horder := degreeNine_ambient_card_le_wreath_ceiling block P hr
  have hw := width_eq block
  rcases hs with hs | hs | hs | hs | hs
  · refine ⟨19, horder.trans ?_, ?_⟩
    · rw [hs]
      norm_num
    · have hw18 : w = 18 := by simpa only [hr, hs] using hw
      rw [hw18]
      have hlog := eight_thirds_le_log_of_sixteen_le 20 (by norm_num)
      norm_num at hlog ⊢
      nlinarith [sq_nonneg (Real.log 20 - 8 / 3)]
  · refine ⟨29, horder.trans ?_, ?_⟩
    · rw [hs]
      norm_num
    · have hw27 : w = 27 := by simpa only [hr, hs] using hw
      rw [hw27]
      have hlog := eight_thirds_le_log_of_sixteen_le 29 (by norm_num)
      norm_num at hlog ⊢
      nlinarith [sq_nonneg (Real.log 29 - 8 / 3)]
  · refine ⟨40, horder.trans ?_, ?_⟩
    · rw [hs]
      norm_num
    · have hw36 : w = 36 := by simpa only [hr, hs] using hw
      rw [hw36]
      have hlog := eight_thirds_le_log_of_sixteen_le 38 (by norm_num)
      norm_num at hlog ⊢
      nlinarith [sq_nonneg (Real.log 38 - 8 / 3)]
  · refine ⟨64, horder.trans ?_, ?_⟩
    · rw [hs]
      norm_num
    · have hw54 : w = 54 := by simpa only [hr, hs] using hw
      rw [hw54]
      have hlog := eight_thirds_le_log_of_sixteen_le 56 (by norm_num)
      norm_num at hlog ⊢
      nlinarith [sq_nonneg (Real.log 56 - 8 / 3)]
  · refine ⟨137, horder.trans ?_, ?_⟩
    · rw [hs]
      norm_num
    · have hw108 : w = 108 := by simpa only [hr, hs] using hw
      rw [hw108]
      have hlog := four_le_log_of_sixtyFour_le 110 (by norm_num)
      norm_num at hlog ⊢
      nlinarith [sq_nonneg (Real.log 110 - 4)]

include P in
/-- The complete finite-axis coefficient is paid by the ordinary menu mass
in all five degree-nine residual cells. -/
theorem degreeNine_tailConstant_le_menuMass
    (D : CompleteCharacterIntervalData (preE7NonPairAction w U))
    (hgen : PermutationSubgroupGeneratorBound)
    (hr : Nat.card block.Fibre = 9)
    (hs : Nat.card block.Points = 2 ∨ Nat.card block.Points = 3 ∨
      Nat.card block.Points = 4 ∨ Nat.card block.Points = 6 ∨
      Nat.card block.Points = 12) :
    ∀ b,
      D.tailConstant ≤
        (2 : ℝ) ^
          (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  obtain ⟨m, horder, hexp⟩ :=
    degreeNine_exists_orderExponent_and_menuBound block P hr hs
  intro b
  exact D.tailConstant_le_menuMass_of_order_and_generators_exact
    hgen m horder (by
      have hw : w = 9 * Nat.card block.Points := by
        simpa only [hr] using width_eq block
      have hs2 := block.degrees_ge_two.2
      omega) hexp b

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
