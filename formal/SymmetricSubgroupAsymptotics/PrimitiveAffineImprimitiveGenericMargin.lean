import SymmetricSubgroupAsymptotics.PrimitiveAffineImprimitiveComponentTransfer
import SymmetricSubgroupAsymptotics.PrimitiveCompositionTail

/-!
# The unbounded imprimitive affine margin

The actual wreath tower already bounds its source exponent by Tracey's
half-induced-module theorem and an actual composition series of the literal
primitive component.  This file closes the numerical margin for local degree
at least forty-five from the published Glasby--Praeger--Rosa--Verret
composition-length theorem.  No finite affine catalogue is used here.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- The exact rational upper bound used in the affine-capacity arithmetic.
It follows from the integer inequality `3^32 < 2^51`. -/
theorem fixedTargetCompositionGamma_lt_seventeen_thirtyTwo :
    fixedTargetCompositionGamma < (17 : ℝ) / 32 := by
  have hp : (3 : ℝ) ^ (32 : ℕ) < (2 : ℝ) ^ (51 : ℕ) := by
    norm_num
  have hlog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < 3 ^ (32 : ℕ)) hp
  simp only [Real.logb_pow,
    Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one] at hlog
  unfold fixedTargetCompositionGamma
  norm_num [div_eq_mul_inv] at hlog ⊢
  linarith

namespace Non2UnipotentPrefixFiniteMenu

/-- The published composition bound leaves much more than the required
`1/8192` margin once the primitive local degree is at least forty-five.
The proof retains the parity loss through `evenWidth`; it does not replace it
by an asymptotic equality. -/
theorem primitiveAffine_genericMargin_of_degree_ge_fortyFive
    (r s w : ℕ) (hr : 45 ≤ r) (hs : 2 ≤ s) (hw : w = r * s)
    (eta : ℝ)
    (heta : eta ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) *
      ((8 / 3 : ℝ) * Real.logb 2 r - 4 / 3)) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - s) / 8 - eta := by
  have hc := primitive_composition_log_tail r hr
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo
  have hgamma0 : 0 ≤ fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
  have hgammaPos : 0 < fixedTargetCompositionGamma := by
    unfold fixedTargetCompositionGamma
    exact div_pos (Real.logb_pos (by norm_num) (by norm_num)) (by norm_num)
  have hsPos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have heta' : eta < (51 : ℝ) / 640 * (r * s) := by
    calc
      eta ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) *
          ((8 / 3 : ℝ) * Real.logb 2 r - 4 / 3) := heta
      _ < fixedTargetCompositionGamma * ((s : ℝ) / 2) *
          ((3 : ℝ) / 10 * r) :=
        mul_lt_mul_of_pos_left hc (mul_pos hgammaPos (by positivity))
      _ < ((17 : ℝ) / 32) * ((s : ℝ) / 2) *
          ((3 : ℝ) / 10 * r) := by
        have hsr : 0 < ((s : ℝ) / 2) * ((3 : ℝ) / 10 * r) := by
          positivity
        nlinarith
      _ = (51 : ℝ) / 640 * (r * s) := by ring
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hrR : (45 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hwR : (w : ℝ) = r * s := by exact_mod_cast hw
  unfold preE7CharacterRho
  rw [hwR]
  nlinarith

namespace PrimitiveAffineImprimitiveBlockTransfer
namespace ComponentSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
  (hTraceyLog : TraceyAffineInducedModuleInput)
  (hTraceyPerm : TraceyPermutationGeneratorInput)
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)

include P

/-- The group-native tower has the required pre-E7 margin throughout the
unbounded local-degree range. -/
theorem margin_of_localDegree_ge_fortyFive
    (hcomp : PrimitiveCompositionLengthInput)
    (hr : 45 ≤ Nat.card block.Fibre) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) -
          (envelope hTraceyHalf hTraceyLog hTraceyPerm block).v) / 8 -
        (envelope hTraceyHalf hTraceyLog hTraceyPerm block).eta := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  have hv : (envelope hTraceyHalf hTraceyLog hTraceyPerm block).v =
      Nat.card block.Points := by
    simpa only [envelope, Fintype.card_eq_nat_card] using
      ActualWreathCompressionTower.envelope_v
        (tower hTraceyHalf hTraceyLog hTraceyPerm block)
  rw [hv]
  apply primitiveAffine_genericMargin_of_degree_ge_fortyFive
    (Nat.card block.Fibre) (Nat.card block.Points) w hr
    block.degrees_ge_two.2 (width_eq block)
  simpa only [Fintype.card_eq_nat_card] using
    envelope_eta_le_primitiveCompositionBound
      hTraceyHalf hTraceyLog hTraceyPerm block hcomp

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
