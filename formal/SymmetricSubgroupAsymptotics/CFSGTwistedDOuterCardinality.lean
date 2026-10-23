import SymmetricSubgroupAsymptotics.CFSGTwistedDAutomorphismCardinality
import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedIsometryIndex
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeProjectiveModel
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldAutomorphisms
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Algebra

/-! The full actual fixed-Q isometry index, the original relative
centre, and faithful semilinear encoding give the outer bound 8f on
the SAME original twisted-D group. No automorphism recognition or
classical group-order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDOuterCardinality
open CFSGTwistedDRelativeElementaryGroup CFSGTwistedDRelativeProjectiveModel
open CFSGTwistedDAutomorphismCardinality CFSGTwistedDFixedIsometryIndex CFSGTwistedDFixedQuadraticSpace
open CFSGTwistedA2FixedField PrimitiveSocleRawStructure

local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : CharP (fixedField q) q.prime :=
  (fixedField q).subtype.charP (fixedField q).subtype.injective q.prime
local instance (q : CFSG.PrimePower) : Algebra (ZMod q.prime) (fixedField q) :=
  ZMod.algebra (fixedField q) q.prime

theorem fixedField_aut_card (q : CFSG.PrimePower) :
    Nat.card (fixedField q ≃+* fixedField q) = q.exponent := by
  apply Nat.pow_right_injective q.prime_isPrime.two_le
  have he := CFSGFiniteFieldAutomorphisms.field_card_eq_pow_card_ringAut (fixedField q) q.prime
  rw [fixedField_card] at he
  exact he

private theorem original_outer_card_le_center_fieldAut (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedD (s + 4) q)) (c : ℕ)
    (hcenter : Nat.card (Subgroup.center (relativeRootGroup (s + 2) q)) ≤ c) :
    Nat.card (Outer (CFSG.Models.TwistedD (s + 4) q)) ≤
      (4 * c) * Nat.card (fixedField q ≃+* fixedField q) := by
  let E := relativeRootGroup (s + 2) q
  let G := CFSG.Models.TwistedD (s + 4) q
  let e := originalRelativeProjectiveEquiv s q
  letI : Finite G := Finite.of_injective e e.injective
  have hcard := (Subgroup.center E).card_mul_index
  change Nat.card (Subgroup.center E) * Nat.card (E ⧸ Subgroup.center E) = Nat.card E at hcard
  rw [← Nat.card_congr e.toEquiv] at hcard
  have hE : Nat.card E ≤ c * Nat.card G :=
    hcard.symm.trans_le (Nat.mul_le_mul_right _ hcenter)
  have hI : Nat.card (CFSGQuadraticSimilitudeGroup.isometries (fixedQuadraticForm (s + 2) q)) ≤
      (4 * c) * Nat.card G := by
    calc
      _ ≤ 4 * Nat.card E := isometries_card_le_four_mul_relative (s + 2) q
      _ ≤ 4 * (c * Nat.card G) := Nat.mul_le_mul_left _ hE
      _ = (4 * c) * Nat.card G := (Nat.mul_assoc _ _ _).symm
  have hAut : Nat.card (MulAut G) ≤ Nat.card G * ((4 * c) * Nat.card (fixedField q ≃+* fixedField q)) := by
    calc
      _ ≤ Nat.card (fixedField q ≃+* fixedField q) *
          Nat.card (CFSGQuadraticSimilitudeGroup.isometries (fixedQuadraticForm (s + 2) q)) :=
        original_card_aut_le_field_mul_isometries s q
      _ ≤ Nat.card (fixedField q ≃+* fixedField q) * ((4 * c) * Nat.card G) := Nat.mul_le_mul_left _ hI
      _ = Nat.card G * ((4 * c) * Nat.card (fixedField q ≃+* fixedField q)) := by ac_rfl
  exact CFSGOuterCardinalityCancellation.outer_card_le_of_automorphism_bound hn _ hAut

theorem original_outer_card_le_eight_fieldAut (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedD (s + 4) q)) :
    Nat.card (Outer (CFSG.Models.TwistedD (s + 4) q)) ≤
      8 * Nat.card (fixedField q ≃+* fixedField q) :=
  original_outer_card_le_center_fieldAut s q hn 2 (relative_center_card_le_two s q)

theorem original_outer_card_le_eight_exponent (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedD (s + 4) q)) :
    Nat.card (Outer (CFSG.Models.TwistedD (s + 4) q)) ≤ 8 * q.exponent := by
  simpa only [fixedField_aut_card] using original_outer_card_le_eight_fieldAut s q hn

theorem original_binary_outer_card_le_four_exponent (s : ℕ) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TwistedD (s + 4) q)]
    (hn : ¬ IsMulCommutative (CFSG.Models.TwistedD (s + 4) q)) (hp : q.prime = 2) :
    Nat.card (Outer (CFSG.Models.TwistedD (s + 4) q)) ≤ 4 * q.exponent := by
  have hle := relative_center_card_le_two s q
  have hcp := relative_center_prime_coprime s q
  have hc : Nat.card (Subgroup.center (relativeRootGroup (s + 2) q)) ≤ 1 := by
    by_contra h
    have he : Nat.card (Subgroup.center (relativeRootGroup (s + 2) q)) = 2 := by omega
    rw [he] at hcp
    rw [hp] at hcp
    norm_num at hcp
  simpa only [Nat.mul_one, fixedField_aut_card] using
    original_outer_card_le_center_fieldAut s q hn 1 hc

end SymmetricSubgroupAsymptotics.CFSGTwistedDOuterCardinality
