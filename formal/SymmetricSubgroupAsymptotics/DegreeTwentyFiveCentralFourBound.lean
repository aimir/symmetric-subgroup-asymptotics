import SymmetricSubgroupAsymptotics.Non2PreE7SaprimExceptionalOdd
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveTemplate
import SymmetricSubgroupAsymptotics.FiniteGroupPaddedGenerators

/-!
# Central cyclic lifts in degree twenty-five

Let `X` be a literal quotient of a soluble subgroup of `GL₂(5)`.  Its scalar
kernel is cyclic of order dividing four, and its projective image has order at
most twenty-four.  This file proves the counting consequence rather than
assuming it: central-lift fibres inject into `C₄` characters of the source,
Kovács--Praeger bounds those characters through the source abelianization,
and ordinary generator counting handles the projective image.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

private abbrev C4 := Multiplicative (ZMod 4)

/-- Structural information on one literal quotient.  These fields are the
finite-group content of the scalar/projective reduction; there is no counting
inequality in the datum. -/
structure CentralFourQuotientDatum
    (X : Type*) [Group X] [Finite X] where
  P : Type
  [groupP : Group P]
  [finiteP : Finite P]
  projection : X →* P
  projection_surjective : Function.Surjective projection
  central_kernel : ∀ z ∈ projection.ker, ∀ x : X, z * x = x * z
  kernelCharacter : projection.ker →* C4
  kernelCharacter_injective : Function.Injective kernelCharacter
  projective_order_le : Nat.card P ≤ 24

attribute [instance] CentralFourQuotientDatum.groupP
  CentralFourQuotientDatum.finiteP

namespace CentralFourQuotientDatum

variable {X : Type*} [Group X] [Finite X]
  (D : CentralFourQuotientDatum X)

theorem kernel_hom_card_le_cyclicFour {J : Type*} [Group J] [Finite J] :
    Nat.card (J →* D.projection.ker) ≤ Nat.card (J →* C4) := by
  letI : Finite (J →* D.projection.ker) :=
    Finite.of_injective (fun f : J →* D.projection.ker => (f : J → D.projection.ker))
      DFunLike.coe_injective
  letI : Finite (J →* C4) :=
    Finite.of_injective (fun f : J →* C4 => (f : J → C4)) DFunLike.coe_injective
  exact Nat.card_le_card_of_injective
    (fun f : J →* D.projection.ker => D.kernelCharacter.comp f)
    (fun f g h => MonoidHom.ext fun x => D.kernelCharacter_injective
      (DFunLike.congr_fun h x))

private theorem three_rpow_eq_two {b : ℕ} :
    (3 : ℝ) ^ ((b : ℝ) / 3) =
      (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  rw [show (Real.logb 2 3 / 3) * (b : ℝ) =
      Real.logb 2 3 * ((b : ℝ) / 3) by ring,
    Real.rpow_mul (by norm_num),
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]

/-- The central fibre is bounded by the published abelianization theorem.
The only group-specific step is its faithful embedding in `C₄`. -/
theorem kernel_hom_bound
    (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (J →* D.projection.ker) : ℝ) ≤
      (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  calc
    (Nat.card (J →* D.projection.ker) : ℝ) ≤
        Nat.card (J →* C4) := by
      exact_mod_cast D.kernel_hom_card_le_cyclicFour (J := J)
    _ ≤ Nat.card (Abelianization J) := by
      exact_mod_cast cyclicCharacter_card_le_abelianization J 4
    _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := hKP b J
    _ = _ := three_rpow_eq_two

include D in
/-- One literal central quotient has the claimed pure exponential row. -/
theorem epi_card_le
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
      24 * (2 : ℝ) ^
        (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
  have hlift := epi_card_le_centralLift (J := J) D.projection
    D.projection_surjective D.central_kernel
  have hproj := Non2UnipotentPrefixFiniteMenu.PreE7SaprimOddLargeAffineSource.epi_le_orderCeiling
    hgen J (q := 24) (by norm_num) D.projective_order_le
  have hker := D.kernel_hom_bound hKP J
  calc
    (Nat.card (GroupEpimorphism J X) : ℝ) ≤
        (Nat.card (GroupEpimorphism J D.P) : ℝ) *
          Nat.card (J →* D.projection.ker) := by exact_mod_cast hlift
    _ ≤ (24 * (2 : ℝ) ^ ((Real.logb 2 24 / 2) * b)) *
          (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) :=
      mul_le_mul hproj hker (Nat.cast_nonneg _) (by positivity)
    _ = 24 * (2 : ℝ) ^
          (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num)]
      unfold Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope
      congr 3
      ring

end CentralFourQuotientDatum

/-- Structural scalar/projective data on all normal quotients of one fixed
degree-twenty-five complement. -/
structure DegreeTwentyFiveCentralFourModel
    (R : Type*) [Group R] [Finite R] where
  quotient : ∀ M : {M : Subgroup R // M.Normal},
    CentralFourQuotientDatum (R ⧸ M.1)

namespace DegreeTwentyFiveCentralFourModel

variable {R : Type*} [Group R] [Finite R]
  (D : DegreeTwentyFiveCentralFourModel R)

def coefficient (_D : DegreeTwentyFiveCentralFourModel R) : ℝ :=
  24 * Nat.card {M : Subgroup R // M.Normal}

theorem coefficient_nonneg : 0 ≤ D.coefficient := by
  unfold coefficient
  positivity

/-- The coefficient is bounded solely from the published order ceiling on
the linear complement.  As in degree nine, the finite subgroup catalogue
supplies structural scalar/projective data; this numerical consequence is
proved here. -/
theorem coefficient_le (hR : Nat.card R ≤ 96) : D.coefficient ≤ 2 ^ 54 := by
  have hR128 : Nat.card R ≤ 2 ^ 7 := hR.trans (by norm_num)
  have hnormal :
      Nat.card {M : Subgroup R // M.Normal} ≤ 2 ^ 49 := by
    simpa using normalSubgroup_card_le_two_pow_sq 7 hR128
  have hnat :
      24 * Nat.card {M : Subgroup R // M.Normal} ≤ 2 ^ 54 := by
    calc
      24 * Nat.card {M : Subgroup R // M.Normal} ≤ 24 * 2 ^ 49 :=
        Nat.mul_le_mul_left 24 hnormal
      _ ≤ 2 ^ 54 := by norm_num
  unfold coefficient
  exact_mod_cast hnat

/-- Summing the proved per-quotient row gives the complete central-`C₄`
bound, with no normal stratum discarded. -/
theorem complete_bound
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound)
    {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := R) J ≤
      D.coefficient * (2 : ℝ) ^
        (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
  unfold completeQuotientWeight completeQuotientCount coefficient
  push_cast
  calc
    (∑ M : {M : Subgroup R // M.Normal},
        (Nat.card (GroupEpimorphism J (R ⧸ M.1)) : ℝ)) ≤
      ∑ _M : {M : Subgroup R // M.Normal},
        24 * (2 : ℝ) ^
          (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
      apply Finset.sum_le_sum
      intro M _
      exact (D.quotient M).epi_card_le hgen hKP J
    _ = (24 * Nat.card {M : Subgroup R // M.Normal} : ℝ) *
          (2 : ℝ) ^
            (Non2UnipotentPrefixFiniteMenu.degreeTwentyFiveCentralSlope * b) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Constructor for the numerical source's former counting input. -/
noncomputable def toBound
    (hgen : PermutationSubgroupGeneratorBound)
    (hKP : KovacsPraegerAbelianizationBound) :
    Non2UnipotentPrefixFiniteMenu.PreE7DegreeTwentyFiveCentralFourBound R where
  coefficient := D.coefficient
  coefficient_nonneg := D.coefficient_nonneg
  complete_bound := D.complete_bound hgen hKP

end DegreeTwentyFiveCentralFourModel

end SymmetricSubgroupAsymptotics

end
