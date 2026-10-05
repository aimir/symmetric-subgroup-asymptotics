import SymmetricSubgroupAsymptotics.SocleGeneratorCharacterInterval
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource

/-!
# Raw complete-quotient envelope of a character interval

The correlated character-interval theorem already partitions every literal
normal axis at one retained subgroup `E`.  The same partition applies to
the complete quotient weight itself: axes above `E` inject into the normal
menu of `U/E`, while axes below `E` are paid by the fixed character tail.
This file records that pre-padding form for affine-layer composition.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [-instance] originalNormalFintype

private abbrev RawNormalAxis (G : Type*) [Group G] :=
  {N : Subgroup G // N.Normal}

private abbrev RawNormalAxisAbove {G : Type*} [Group G]
    (E : Subgroup G) :=
  {N : RawNormalAxis G // E ≤ N.1}

private abbrev RawNormalAxisBelow {G : Type*} [Group G]
    (E : Subgroup G) :=
  {N : RawNormalAxis G // ¬ E ≤ N.1}

namespace CompleteCharacterIntervalData

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  (D : CompleteCharacterIntervalData U)

/-- The literal axes below `E`, without an orbit predicate, obey the same
uniform character tail. -/
theorem below_epimorphism_sum_le (lit : PreE7CharacterLiterature) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ N : RawNormalAxisBelow D.E,
        (Nat.card (GroupEpimorphism J (U ⧸ N.1.1)) : ℝ)) ≤
      D.tailConstant * (2 : ℝ) ^ (D.theta * b) := by
  have haxis : ∀ N : RawNormalAxisBelow D.E,
      (Nat.card (GroupEpimorphism J (U ⧸ N.1.1)) : ℝ) ≤
        (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
          (2 : ℝ) ^ (D.theta * b) := by
    intro N
    have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    calc
      (Nat.card (GroupEpimorphism J (U ⧸ N.1.1)) : ℝ) ≤
          (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
            (2 : ℝ) ^ ((D.quotientCertificate N.1 N.2).slope * b) :=
        (D.quotientCertificate N.1 N.2).envelope lit b J
      _ ≤ (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
          (2 : ℝ) ^ (D.theta * b) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
          (mul_le_mul_of_nonneg_right
            (D.quotientCertificate_slope N.1 N.2) hb)
  calc
    (∑ N : RawNormalAxisBelow D.E,
        (Nat.card (GroupEpimorphism J (U ⧸ N.1.1)) : ℝ)) ≤
        ∑ N : RawNormalAxisBelow D.E,
          (Nat.card ((U ⧸ N.1.1) ≃* (U ⧸ N.1.1)) : ℝ) *
            (2 : ℝ) ^ (D.theta * b) :=
      Finset.sum_le_sum (fun N _ => haxis N)
    _ = D.tailConstant * (2 : ℝ) ^ (D.theta * b) := by
      rw [← Finset.sum_mul]
      rfl

/-- Pointwise complete quotient weight of the literal target, compressed to
one complete quotient weight of `U/E` and one additive character tail. -/
theorem completeQuotientWeight_le_rawEnvelope
    (lit : PreE7CharacterLiterature) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := U) J ≤
      completeQuotientWeight (R := U ⧸ D.E) J +
        D.tailConstant * (2 : ℝ) ^ (D.theta * b) := by
  let Q : RawNormalAxis U → Prop := fun N => D.E ≤ N.1
  let f : RawNormalAxis U → ℝ := fun N =>
    Nat.card (GroupEpimorphism J (U ⧸ N.1))
  have hsplit := Fintype.sum_subtype_add_sum_subtype Q f
  calc
    completeQuotientWeight (R := U) J =
        ∑ N : RawNormalAxis U, f N := by
      unfold completeQuotientWeight completeQuotientCount
      rw [Nat.cast_sum]
    _ = (∑ N : {N : RawNormalAxis U // Q N}, f N.1) +
        ∑ N : {N : RawNormalAxis U // ¬ Q N}, f N.1 := hsplit.symm
    _ ≤ completeQuotientWeight (R := U ⧸ D.E) J +
        D.tailConstant * (2 : ℝ) ^ (D.theta * b) :=
      add_le_add
        (normalAxisAbove_epimorphism_sum_le_completeQuotientWeight D.E J)
        (D.below_epimorphism_sum_le lit J)

/-- Source-summed raw character interval, before any physical pointing. -/
noncomputable def quotientSummedEnvelope
    (lit : PreE7CharacterLiterature) :
    Non2UnipotentPrefixFiniteMenu.PreE7DegreeTwoPairQuotientSummedEnvelope U where
  R := U ⧸ D.E
  mainCoefficient := 1
  coldCoefficient := fun _ => D.tailConstant
  eta := 0
  theta := D.theta
  mainCoefficient_nonneg := zero_le_one
  coldCoefficient_nonneg := fun _ => D.tailConstant_nonneg
  exceptionalRaw := fun _ => 0
  exceptionalRaw_nonneg := fun _ => le_rfl
  summed := fun b => by
    have h := Finset.sum_le_sum (s := Finset.univ)
      (fun (J : Subgroup (Equiv.Perm (Fin b))) _ =>
        D.completeQuotientWeight_le_rawEnvelope lit J)
    simpa only [zero_mul, Real.rpow_zero, mul_one, one_mul, add_zero] using h

end CompleteCharacterIntervalData
end SymmetricSubgroupAsymptotics

end
