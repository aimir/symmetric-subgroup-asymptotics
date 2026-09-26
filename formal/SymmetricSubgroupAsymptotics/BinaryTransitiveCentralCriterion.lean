import SymmetricSubgroupAsymptotics.FaithfulTransitiveCentralCard
import SymmetricSubgroupAsymptotics.BinaryCharacterFusion

/-!
# Uniform original bottom-axis character criteria in degree sixteen

The central involution group acts freely on the original transitive points.
If its cardinality reaches the degree, the entire original group is regular.
Thus a nonregular degree-sixteen action has central involution dimension at
most three, and satisfies the exact existing character criterion uniformly.
No target generator-rank bound is substituted for a homomorphism count.

The finite criterion is algebraic. Its original-source counting corollary
retains the named nilpotent conjugacy-class input explicitly, together with
the original target automorphism factor and arbitrary survival condition.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G X : Type*} [Group G] [Finite G]

/-- Cardinality of the actual central involution group, with its existing
binary vector-space structure. -/
theorem binaryCentralOmega_card_eq_pow_finrank :
    Nat.card (binaryCentralOmega G) =
      2 ^ Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) := by
  calc
    _ = Nat.card (Additive (binaryCentralOmega G)) :=
      (Nat.card_congr Additive.toMul).symm
    _ = Nat.card (ZMod 2) ^
        Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) :=
      Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Additive (binaryCentralOmega G))
    _ = _ := by rw [Nat.card_zmod]

variable [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    [Finite X] [Nonempty X]

/-- General power-of-two-degree form. The strict original group/degree
comparison excludes exactly the regular case needed by this argument. -/
theorem binaryCentralOmega_finrank_lt_of_nonregular
    (k : ℕ) (hdegree : Nat.card X = 2^k)
    (hlarge : Nat.card X < Nat.card G) :
    Module.finrank (ZMod 2) (Additive (binaryCentralOmega G)) < k := by
  classical
  let x : X := Classical.choice inferInstance
  have hc : Nat.card (binaryCentralOmega G) < Nat.card X :=
    central_card_lt_points_of_points_lt_group
      (binaryCentralOmegaEmbedding (G := G)) binaryCentralOmegaEmbedding_injective
      (fun z => z.1.property) x hlarge
  rw [binaryCentralOmega_card_eq_pow_finrank, hdegree] at hc
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hc

/-- All dimensions zero through three pass the literal degree-sixteen
integer test. This is the exact criterion, not an approximate slope. -/
theorem binary_character_gap_sixteen_of_le_three (z : ℕ) (hz : z ≤ 3) :
    38^(8*z) < 2^16*25^(8*z) := by
  have h : z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> decide +kernel

/-- One original faithful transitive action, with no finite table or
declared central cardinality. The group need not be binary for this finite
criterion itself; binary structure is required by its counting envelope. -/
def binaryTransitiveSixteen_characterCriterion
    (hdegree : Nat.card X = 16) (hlarge : 16 < Nat.card G) :
    BinaryNormalCharacterCriterion G 16 where
  dimension := Module.finrank (ZMod 2) (Additive (binaryCentralOmega G))
  cardinal := binaryCentralOmega_card_eq_pow_finrank
  gap := binary_character_gap_sixteen_of_le_three _ (by
    have h := binaryCentralOmega_finrank_lt_of_nonregular (G := G) (X := X)
      4 (by simpa only [show 2^4 = 16 from rfl] using hdegree)
      (by simpa only [hdegree] using hlarge)
    omega)

/-- The exact literal bottom quotient of the original permutation group.
No action is assigned to an abstract quotient. -/
def binaryTransitiveSixteen_botCharacterCriterion
    (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hlarge : 16 < Nat.card U) :
    BinaryNormalCharacterCriterion (U ⧸ (⊥ : Subgroup U)) 16 :=
  (binaryTransitiveSixteen_characterCriterion (G := U) (X := Fin 16)
    (Nat.card_fin 16) hlarge).transport (QuotientGroup.quotientBot (G := U)).symm

/-- The same original-source onto-map estimate retains the named external
class-count input. It is not an all-Hom estimate inferred from target rank. -/
theorem binaryTransitiveSixteen_bot_survival_envelope
    (hMaroti : NilpotentConjugacyClassInput)
    (U : Subgroup (Equiv.Perm (Fin 16)))
    [MulAction.IsPretransitive U (Fin 16)] (hU : IsPGroup 2 U)
    (hlarge : 16 < Nat.card U) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (S : GroupEpimorphism J (U ⧸ (⊥ : Subgroup U)) → Prop) :
    (Nat.card {f : GroupEpimorphism J (U ⧸ (⊥ : Subgroup U)) // S f} : ℝ) ≤
      (Nat.card ((U ⧸ (⊥ : Subgroup U)) ≃* (U ⧸ (⊥ : Subgroup U))) : ℝ) *
        (2 : ℝ) ^ (binaryCharacterSlope
          (binaryTransitiveSixteen_botCharacterCriterion U hlarge).dimension * (b : ℝ)) :=
  (binaryTransitiveSixteen_botCharacterCriterion U hlarge).survival_envelope
    hMaroti (hU.to_quotient ⊥) b J S

end SymmetricSubgroupAsymptotics

end
