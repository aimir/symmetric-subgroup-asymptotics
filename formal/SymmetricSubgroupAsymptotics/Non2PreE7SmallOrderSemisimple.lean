import SymmetricSubgroupAsymptotics.Non2PreE7SemisimpleTemplate
import SymmetricSubgroupAsymptotics.TrivialQuotientComparator

/-!
# The SO family from the ordinary generator bound

This is the direct all-source proof for actual non-2 actions of small
exponential order.  The sole external input is the ordinary-generator
specialization of Holt--Roney-Dougal: every subgroup of `S_b` has a
generating set of size at most `b/2 + 1`, including the degree-three
exception.  Target normal quotients are kept literal.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Published ordinary-generator input in the exact rounded form used by
the SO source. -/
def PermutationSubgroupGeneratorBound : Prop :=
  ∀ (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    ∃ S : Finset J, Subgroup.closure (S : Set J) = ⊤ ∧
      2 * S.card ≤ b + 2

namespace Non2UnipotentPrefixFiniteMenu

/-- One literal action in the small-order family.  `m` is a certified binary
logarithmic order ceiling; retaining it as an integer avoids any rounding
ambiguity in the quotient bounds. -/
structure PreE7SoOrderSourceData
    (w : ℕ) (i : PreE7NonPairActionClass w) where
  width_lower : 64 ≤ w
  order_not_two_power : ¬ IsPGroup 2 (preE7NonPairAction w i)
  m : ℕ
  order_le : Nat.card (preE7NonPairAction w i) ≤ 2 ^ m
  exponent_small : 8 * m ≤ w
  coefficient_total_bound : ∀ b,
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
        (fun _ => (2 : ℝ) ^ m) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

namespace PreE7SoOrderSourceData

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (D : PreE7SoOrderSourceData w i)

def eta : ℝ := (D.m : ℝ) / 2

def degree (_D : PreE7SoOrderSourceData w i) : ℕ :=
  paddedComparatorDegree preE7CharacterRho 2 w

def delta : ℝ :=
  paddedComparatorDelta preE7CharacterRho D.eta 2 w

def cutoff : ℝ := (D.degree : ℝ) / 8 + D.delta / 2

def alpha : ℝ := D.eta + D.cutoff

theorem eta_nonneg : 0 ≤ D.eta := by
  dsimp [eta]
  positivity

/-- The SO order condition leaves a uniform `rho = 1/8192` margin even in
the adverse odd-width parity. -/
theorem degree_margin :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - 2) / 8 - D.eta := by
  have hm : (8 * D.m : ℕ) ≤ w := D.exponent_small
  have hmR : (8 : ℝ) * D.m ≤ w := by exact_mod_cast hm
  have heven : (w : ℝ) ≤ evenWidth w + 1 := by
    exact_mod_cast width_le_evenWidth_add_one w
  have hw : (64 : ℝ) ≤ w := by exact_mod_cast D.width_lower
  unfold preE7CharacterRho eta
  norm_num
  linarith

/-- An onto map to any literal quotient of the SO action is determined by
the images of an ordinary source generating set. -/
theorem axis_epimorphism_bound
    (hgen : PermutationSubgroupGeneratorBound)
    (b : ℕ)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal})
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J
        (preE7NonPairAction w i ⧸ N.1)) : ℝ) ≤
      (2 : ℝ) ^ D.m * (2 : ℝ) ^ (D.eta * b) := by
  obtain ⟨S, hS, hScard⟩ := hgen b J
  let Q := preE7NonPairAction w i ⧸ N.1
  have hQ : Nat.card Q ≤ 2 ^ D.m :=
    (Nat.card_le_card_of_surjective _
      (QuotientGroup.mk_surjective (s := N.1))).trans D.order_le
  have hepi : Nat.card (GroupEpimorphism J Q) ≤ Nat.card (J →* Q) := by
    letI : Finite (J →* Q) := Finite.of_injective
      (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hnat : Nat.card (GroupEpimorphism J Q) ≤ 2 ^ (D.m * S.card) := by
    calc
      Nat.card (GroupEpimorphism J Q) ≤ Nat.card (J →* Q) := hepi
      _ ≤ Nat.card Q ^ S.card := monoidHom_card_le_pow_of_closure S hS
      _ ≤ (2 ^ D.m) ^ S.card := Nat.pow_le_pow_left hQ _
      _ = 2 ^ (D.m * S.card) := by rw [pow_mul]
  have hexponent : ((D.m * S.card : ℕ) : ℝ) ≤
      D.m + D.eta * b := by
    have hScardR : (2 : ℝ) * S.card ≤ b + 2 := by
      exact_mod_cast hScard
    dsimp [eta]
    have hm0 : (0 : ℝ) ≤ D.m := by positivity
    push_cast
    nlinarith
  have hreal :
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (2 : ℝ) ^ ((D.m * S.card : ℕ) : ℝ) := by
    calc
      (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
          ((2 ^ (D.m * S.card) : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = (2 : ℝ) ^ ((D.m * S.card : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
  calc
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (2 : ℝ) ^ ((D.m * S.card : ℕ) : ℝ) := hreal
    _ ≤ (2 : ℝ) ^ (D.m + D.eta * b) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexponent
    _ = (2 : ℝ) ^ D.m * (2 : ℝ) ^ (D.eta * b) := by
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [Real.rpow_natCast]

/-- The complete SO earlier-owner certificate.  The comparator is trivial;
its padded faithful action has positive degree only to enter the common
hot/cold numerical interface, while its complete quotient weight is exactly
one. -/
noncomputable def certificate
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7EarlierActionComparatorCertificate .so w i where
  R := PUnit
  groupR := inferInstance
  finiteR := inferInstance
  v := D.degree
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  C := fun _ _ => (2 : ℝ) ^ D.m
  tailCoefficient := fun _ _ => 0
  eta := D.eta
  delta := D.delta
  cutoff := D.cutoff
  alpha := D.alpha
  theta := 0
  alpha_eq := rfl
  coefficient_nonneg := fun _ _ => by positivity
  tail_nonneg := fun _ _ => le_rfl
  broad_axis_envelope := by
    intro b N J
    rw [completeQuotientWeight_eq_one_of_subsingleton (R := PUnit) J]
    have hsurvive := fusionSurvivingEpiCount_le_groupEpimorphism_card
      (preE7NonPairAction w i)
      (preE7NoPairNoC3BroadActionPredicate w i b) N J
    have hepi := D.axis_epimorphism_bound hgen b N J
    calc
      fusionSurvivingEpiCount (preE7NonPairAction w i)
          (preE7NoPairNoC3BroadActionPredicate w i b) N J ≤
          (Nat.card (GroupEpimorphism J
            (preE7NonPairAction w i ⧸ N.1)) : ℝ) := hsurvive
      _ ≤ (2 : ℝ) ^ D.m * (2 : ℝ) ^ (D.eta * b) := hepi
      _ = ((2 : ℝ) ^ D.m * (2 : ℝ) ^ (D.eta * b)) * 1 +
          0 * (2 : ℝ) ^ ((0 : ℝ) * b) := by ring

end PreE7SoOrderSourceData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
