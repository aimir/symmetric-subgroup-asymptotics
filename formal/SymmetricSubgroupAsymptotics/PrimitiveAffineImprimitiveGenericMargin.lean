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

/-- An integer composition length at most eleven already gives the required
pre-E7 margin from local degree twenty-five.  This is the finite-range
counterpart of the logarithmic tail theorem and keeps the parity loss in
`evenWidth` explicit. -/
theorem primitiveAffine_margin_of_length_le_eleven
    (r s w : ℕ) (hr : 25 ≤ r) (hs : 2 ≤ s) (hw : w = r * s)
    (eta : ℝ)
    (heta : eta ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) * 11) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - s) / 8 - eta := by
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo
  have heta' : eta < (187 : ℝ) / 64 * s := by
    calc
      eta ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) * 11 := heta
      _ < ((17 : ℝ) / 32) * ((s : ℝ) / 2) * 11 := by
        have hsPos : 0 < (s : ℝ) := by positivity
        nlinarith
      _ = (187 : ℝ) / 64 * s := by ring
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hrR : (25 : ℝ) ≤ r := by exact_mod_cast hr
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  have hwR : (w : ℝ) = r * s := by exact_mod_cast hw
  unfold preE7CharacterRho
  rw [hwR]
  nlinarith

/-- An integer composition length at most fourteen gives the required
pre-E7 margin from local degree thirty-two. -/
theorem primitiveAffine_margin_of_length_le_fourteen
    (r s w : ℕ) (hr : 32 ≤ r) (hs : 2 ≤ s) (hw : w = r * s)
    (eta : ℝ)
    (heta : eta ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) * 14) :
    preE7CharacterRho * w ≤ ((evenWidth w : ℝ) - s) / 8 - eta := by
  have hgamma := fixedTargetCompositionGamma_lt_seventeen_thirtyTwo
  have heta' : eta < (119 : ℝ) / 32 * s := by
    calc
      eta ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) * 14 := heta
      _ < ((17 : ℝ) / 32) * ((s : ℝ) / 2) * 14 := by
        have hsPos : 0 < (s : ℝ) := by positivity
        nlinarith
      _ = (119 : ℝ) / 32 * s := by ring
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hrR : (32 : ℝ) ≤ r := by exact_mod_cast hr
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
  (hTraceyRefined : TraceyRefinedInducedModuleInput)
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
          (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).v) / 8 -
        (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).eta := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  have hv : (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).v =
      Nat.card block.Points := by
    simpa only [envelope, Fintype.card_eq_nat_card] using
      ActualWreathCompressionTower.envelope_v
        (tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block)
  rw [hv]
  apply primitiveAffine_genericMargin_of_degree_ge_fortyFive
    (Nat.card block.Fibre) (Nat.card block.Points) w hr
    block.degrees_ge_two.2 (width_eq block)
  simpa only [Fintype.card_eq_nat_card] using
    envelope_eta_le_primitiveCompositionBound
      hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block hcomp

/-- The bounded logarithmic range `25 ≤ r < 45` is already uniform: the
published composition-length theorem forces length at most eleven below
degree 32 and at most fourteen below degree 45.  Consequently no finite
primitive-action catalogue is needed in this range. -/
theorem margin_of_localDegree_twentyFive_to_fortyFour
    (hcomp : PrimitiveCompositionLengthInput)
    (hr25 : 25 ≤ Nat.card block.Fibre)
    (hr45 : Nat.card block.Fibre < 45) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) -
          (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).v) / 8 -
        (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).eta := by
  letI : Nontrivial block.Fibre :=
    Finite.one_lt_card_iff_nontrivial.mp block.degrees_ge_two.1
  let r := Nat.card block.Fibre
  let s := Nat.card block.Points
  have hv : (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).v = s := by
    simpa only [envelope, s, Fintype.card_eq_nat_card] using
      ActualWreathCompressionTower.envelope_v
        (tower hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block)
  rw [hv]
  obtain ⟨t, htower⟩ :=
    (trace hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).envelope_eta_le_some_compositionLength
  have ht := PrimitiveCompositionLengthInput.bound_of_equiv hcomp
    r block.degrees_ge_two.1 (Finite.equivFin block.Fibre)
    block.Component block.component_preprimitive t
  have hfactor : 0 ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) := by
    apply mul_nonneg
    · exact div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num))
        (by norm_num)
    · positivity
  have hs : 2 ≤ s := block.degrees_ge_two.2
  have hw : w = r * s := width_eq block
  by_cases hr32 : r < 32
  · have hrpos : (0 : ℝ) < r := by
      exact_mod_cast (show 0 < r by omega)
    have hr32R : (r : ℝ) < 32 := by exact_mod_cast hr32
    have hlog : Real.logb 2 r < 5 := by
      have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hrpos hr32R
      have h32 : Real.logb 2 (32 : ℝ) = 5 := by
        rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        norm_num
      simpa [h32] using h
    have hlenR : (t.chain.length : ℝ) < 12 := by
      calc
        (t.chain.length : ℝ) ≤ (8 / 3 : ℝ) * Real.logb 2 r - 4 / 3 := ht
        _ < 12 := by nlinarith
    have hlenNat : t.chain.length ≤ 11 := by
      have : t.chain.length < 12 := by exact_mod_cast hlenR
      omega
    apply primitiveAffine_margin_of_length_le_eleven r s w hr25 hs hw
    calc
      (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).eta ≤
          fixedTargetCompositionGamma * ((s : ℝ) / 2) * t.chain.length := by
        simpa only [Fintype.card_eq_nat_card, s] using htower
      _ ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) * 11 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlenNat) hfactor
  · have hr32' : 32 ≤ r := by omega
    have hrpos : (0 : ℝ) < r := by
      exact_mod_cast (show 0 < r by omega)
    have hr64R : (r : ℝ) < 64 := by
      exact_mod_cast (show r < 64 by omega)
    have hlog : Real.logb 2 r < 6 := by
      have h := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) hrpos hr64R
      have h64 : Real.logb 2 (64 : ℝ) = 6 := by
        rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
        norm_num
      simpa [h64] using h
    have hlenR : (t.chain.length : ℝ) < 15 := by
      calc
        (t.chain.length : ℝ) ≤ (8 / 3 : ℝ) * Real.logb 2 r - 4 / 3 := ht
        _ < 15 := by nlinarith
    have hlenNat : t.chain.length ≤ 14 := by
      have : t.chain.length < 15 := by exact_mod_cast hlenR
      omega
    apply primitiveAffine_margin_of_length_le_fourteen r s w hr32' hs hw
    calc
      (envelope hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block).eta ≤
          fixedTargetCompositionGamma * ((s : ℝ) / 2) * t.chain.length := by
        simpa only [Fintype.card_eq_nat_card, s] using htower
      _ ≤ fixedTargetCompositionGamma * ((s : ℝ) / 2) * 14 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hlenNat) hfactor

/-- Every literal primitive-affine component of degree at least twenty-five
supplies the construction-facing source.  The split at degree forty-five is
only the point where the published logarithmic tail replaces the finite
integer composition-length rounding; it does not create two owners. -/
noncomputable def of_localDegree_ge_twentyFive
    (hcomp : PrimitiveCompositionLengthInput)
    (hr : 25 ≤ Nat.card block.Fibre) :
    ComponentSource hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P where
  margin := by
    by_cases h45 : 45 ≤ Nat.card block.Fibre
    · exact margin_of_localDegree_ge_fortyFive
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hcomp h45
    · exact margin_of_localDegree_twentyFive_to_fortyFour
        hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm block P hcomp hr
          (by omega)

end ComponentSource
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
