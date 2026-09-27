import SymmetricSubgroupAsymptotics.BinaryCharacterEnvelope
import SymmetricSubgroupAsymptotics.FusionWidthPhysical

/-!
# A separate binary character envelope at rate 5^(2/7)

The premise concerns actual binary permutation subgroups only. Restriction
to the original Sylow 2-subgroup handles an arbitrary exterior group, and
the original target automorphism factor is retained. The integer acceptance
test is new; no existing 38/25 character certificate is converted.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- Exact integer interface to the actual binary permutation class theorem.
`BinaryPermutationClassBound.literal_class_card_pow_seven_le` supplies it
once that separate finite-base installation is checked. -/
def BinarySevenPermutationClassInput : Prop :=
  ∀ (b : ℕ) (P : Subgroup (Equiv.Perm (Fin b))), IsPGroup 2 P →
    Nat.card (ConjClasses P)^7 ≤ 5^(2*b)

def binarySevenGamma : ℝ := (5:ℝ)^((2:ℝ)/7)
def binarySevenCharacterSlope (z : ℕ) : ℝ :=
  (2*(z:ℝ)/7)*Real.logb 2 5

theorem binarySevenCharacterSlope_eq (z : ℕ) :
    binarySevenCharacterSlope z = (z:ℝ)*Real.logb 2 binarySevenGamma := by
  rw [binarySevenGamma, Real.logb_rpow_eq_mul_logb_of_pos (by norm_num : (0:ℝ)<5)]
  unfold binarySevenCharacterSlope
  ring

/-- The seventh-power bound gives the exact character-tuple exponent. -/
theorem binarySeven_class_power_le (b z : ℕ) (c : ℝ) (hc : 0<c)
    (hclass : c^7 ≤ (5:ℝ)^(2*b)) :
    c^z ≤ (2:ℝ)^(binarySevenCharacterSlope z*(b:ℝ)) := by
  have hl := Real.logb_le_logb_of_le (b := 2) (by norm_num)
    (show 0<c^7 by positivity) hclass
  simp only [Real.logb_pow, Nat.cast_mul, Nat.cast_ofNat] at hl
  have hm := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg z : (0:ℝ)≤z)
  calc
    _ = (2:ℝ)^(Real.logb 2 c*(z:ℝ)) := by
      rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2),
        Real.rpow_logb (by norm_num : (0:ℝ)<2) (by norm_num) hc, Real.rpow_natCast]
    _ ≤ _ := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      unfold binarySevenCharacterSlope
      nlinarith [hm]

/-- Restrict to the original Sylow inside the same original symmetric
group; no binary assumption on the entire exterior group is needed. -/
theorem originalSylow_conjugacyClass_pow_seven_le
    (hclass : BinarySevenPermutationClassInput) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) (P : Sylow 2 J) :
    Nat.card (ConjClasses (P:Subgroup J))^7 ≤ 5^(2*b) := by
  let T := (P:Subgroup J).map J.subtype
  let e : (P:Subgroup J) ≃* T :=
    Subgroup.equivMapOfInjective (P:Subgroup J) J.subtype Subtype.val_injective
  have hT : IsPGroup 2 T := P.isPGroup'.of_equiv e
  have hc : Nat.card (ConjClasses (P:Subgroup J)) ≤ Nat.card (ConjClasses T) :=
    Nat.card_le_card_of_surjective (ConjClasses.map e.symm.toMonoidHom)
      (ConjClasses.map_surjective e.symm.surjective)
  exact (Nat.pow_le_pow_left hc 7).trans (hclass b T hT)

/-- Complete epimorphisms retain the original Aut(Q) multiplier. -/
theorem binarySeven_groupEpimorphism_original_envelope
    (hclass : BinarySevenPermutationClassInput)
    {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q):ℝ) ≤ (Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binarySevenCharacterSlope
        (Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q)))*(b:ℝ)) := by
  let P : Sylow 2 J := Classical.choice inferInstance
  let z := Module.finrank (ZMod 2) (Additive (binaryCentralOmega Q))
  have hnat := (groupEpimorphism_card_le_sylow P hQ).trans
    (binary_groupEpimorphism_card_le_characters (J := (P:Subgroup J)) hQ)
  have hp := binarySeven_class_power_le b z
    (Nat.card (ConjClasses (P:Subgroup J)) : ℝ)
    (by exact_mod_cast (Nat.card_pos (α := ConjClasses (P:Subgroup J))))
    (by exact_mod_cast originalSylow_conjugacyClass_pow_seven_le hclass b J P)
  exact (by exact_mod_cast hnat : (Nat.card (GroupEpimorphism J Q):ℝ) ≤
    (Nat.card (Q≃*Q):ℝ)*(Nat.card (ConjClasses (P:Subgroup J)):ℝ)^z).trans
      (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _))

/-- Actual central involutions and the new exact integer gap. -/
structure BinarySevenCharacterCriterion (G : Type*) [Group G] (w : ℕ) where
  dimension : ℕ
  cardinal : Nat.card (binaryCentralOmega G) = 2^dimension
  gap : 5^(16*dimension) < 2^(7*w)

namespace BinarySevenCharacterCriterion

variable {G : Type*} [Group G] {w : ℕ} (C : BinarySevenCharacterCriterion G w)

def transport {H : Type*} [Group H] (e : G ≃* H) :
    BinarySevenCharacterCriterion H w where
  dimension := C.dimension
  cardinal := (binaryCentralOmega_card_congr G e).symm.trans C.cardinal
  gap := C.gap

theorem exact_dimension [Finite G] :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) = C.dimension :=
  binaryCentralOmega_finrank G C.dimension C.cardinal

theorem slope_gap : binarySevenCharacterSlope C.dimension < (w:ℝ)/8 := by
  have hg : (5:ℝ)^(16*C.dimension) < (2:ℝ)^(7*w) := by exact_mod_cast C.gap
  have hl := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hg
  simp only [Real.logb_pow, Nat.cast_mul, Nat.cast_ofNat] at hl
  rw [Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at hl
  unfold binarySevenCharacterSlope
  nlinarith

end BinarySevenCharacterCriterion

namespace BinarySevenCharacterCriterion

variable {Q : Type} [Group Q] [Finite Q] {w : ℕ} (C : BinarySevenCharacterCriterion Q w)

theorem original_envelope (hclass : BinarySevenPermutationClassInput)
    (hQ : IsPGroup 2 Q) (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J Q):ℝ) ≤ (Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binarySevenCharacterSlope C.dimension*(b:ℝ)) := by
  simpa only [C.exact_dimension] using
    binarySeven_groupEpimorphism_original_envelope hclass hQ b J

theorem survival_envelope (hclass : BinarySevenPermutationClassInput)
    (hQ : IsPGroup 2 Q) (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f}:ℝ) ≤ (Nat.card (Q≃*Q):ℝ)*
      (2:ℝ)^(binarySevenCharacterSlope C.dimension*(b:ℝ)) := by
  letI : Finite (GroupEpimorphism J Q) := Finite.of_injective
    (fun f : GroupEpimorphism J Q => (f.1:J→Q))
    (fun _ _ h => Subtype.ext (DFunLike.coe_injective h))
  have hn := Nat.card_le_card_of_injective
    (Subtype.val : {f : GroupEpimorphism J Q // S f} → GroupEpimorphism J Q)
    Subtype.val_injective
  exact (by exact_mod_cast hn : (Nat.card {f : GroupEpimorphism J Q // S f}:ℝ) ≤
    (Nat.card (GroupEpimorphism J Q):ℝ)).trans (C.original_envelope hclass hQ b J)

end BinarySevenCharacterCriterion

theorem binarySevenCharacter_physicalAxis_envelope
    (hclass : BinarySevenPermutationClassInput) {w b : ℕ}
    (U : Subgroup (Equiv.Perm (Fin w))) (hU : IsPGroup 2 U)
    (P : Subgroup (U×Equiv.Perm (Fin b)) → Prop)
    (N : {N : Subgroup U // N.Normal})
    (C : BinarySevenCharacterCriterion (U⧸N.1) w)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionSurvivingEpiCount U P N J ≤ (Nat.card ((U⧸N.1)≃*(U⧸N.1)):ℝ)*
      (2:ℝ)^(binarySevenCharacterSlope C.dimension*(b:ℝ)) :=
  C.survival_envelope hclass (hU.to_quotient N.1) b J
    (fun f => P (fusionFullGoursatEncode N J f).1)

end SymmetricSubgroupAsymptotics

end
