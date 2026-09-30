import SymmetricSubgroupAsymptotics.SemisimpleOuterFibre
import SymmetricSubgroupAsymptotics.Non2PreE7B6RankTailSource
import SymmetricSubgroupAsymptotics.BinaryRankTailFiftyOne

/-!
# SNS2: the weighted fibre of a semisimple normal layer with a binary top

The historical family SNS2 consists of the actual actions `U` of degree
`w ≥ 5` with a nontrivial normal subgroup `E` that is a direct product of
nonabelian simple groups, such that `R = U/E` is a `2`-group of order `2^l`
with `3l ≤ w`.

For every complete source `J ≤ S_b`, the semisimple outer fibre gives
`Z_J(U) ≤ Z_J(R) Ψ_E(b)` with `Ψ_E(b) = ∏ᵢ (1 + |Aut Sᵢ| log₂(b!) / log₂|Sᵢ|)`,
and every map to a quotient of `R` factors through the maximal binary quotient
of `J`, so

`Z_J(U) ≤ ν(R) Ψ_E(b) 2^(l d₂(J))`.

This weighted bound keeps the factor `2^(l d₂(J))`; the cold bound at
`d₂(J) ≤ 51b/200` follows from it.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

/-- A literal action with a nontrivial semisimple normal layer whose quotient
is a small binary group. -/
structure PreE7Sns2ActionCertificate {w : ℕ} (U : Subgroup (Equiv.Perm (Fin w))) :
    Type 1 where
  E : Subgroup U
  [E_normal : E.Normal]
  E_ne_bot : E ≠ ⊥
  chart : SemisimpleNormalChart E
  quotient_twoGroup : IsPGroup 2 (U ⧸ E)
  width_lower : 5 ≤ w
  quotient_small : 3 * Nat.log 2 (Nat.card (U ⧸ E)) ≤ w

attribute [instance] PreE7Sns2ActionCertificate.E_normal

namespace PreE7Sns2ActionCertificate

variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))}
  (C : PreE7Sns2ActionCertificate U)

/-- `l = log₂ |U/E|`. -/
def quotientRank : ℕ := Nat.log 2 (Nat.card (U ⧸ C.E))

/-- `ν(R)`: the number of literal normal subgroups of `R = U/E`. -/
def quotientNormalCount : ℕ := Nat.card {D : Subgroup (U ⧸ C.E) // D.Normal}

/-- `Ψ_E(b) = ∏ᵢ (1 + |Aut Sᵢ| log₂(b!) / log₂|Sᵢ|)`. -/
def outerFactor (b : ℕ) : ℝ :=
  C.chart.outerFactor (Real.logb 2 (Nat.factorial b))

theorem outerFactor_nonneg (b : ℕ) : 0 ≤ C.outerFactor b :=
  C.chart.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.factorial_pos b))

/-- Maps to a quotient of `R` factor through the maximal binary quotient of
the source: `Z_J(R) ≤ ν(R) 2^(l d₂(J))`. -/
theorem quotientSum_le {b : ℕ} (J : Subgroup (Equiv.Perm (Fin b))) :
    (∑ D : {D : Subgroup (U ⧸ C.E) // D.Normal},
        (Nat.card (GroupEpimorphism J ((U ⧸ C.E) ⧸ D.1)) : ℝ)) ≤
      C.quotientNormalCount * (2 : ℝ) ^ ((C.quotientRank : ℝ) * binaryCharacterRank J) := by
  have hD : ∀ D : {D : Subgroup (U ⧸ C.E) // D.Normal},
      (Nat.card (GroupEpimorphism J ((U ⧸ C.E) ⧸ D.1)) : ℝ) ≤
        (2 : ℝ) ^ ((C.quotientRank : ℝ) * binaryCharacterRank J) := by
    intro D
    have htwo : IsPGroup 2 ((U ⧸ C.E) ⧸ D.1) := C.quotient_twoGroup.to_quotient D.1
    have hhom := binaryTargetOrder_hom_card_le (J := J) htwo
    have hepi : Nat.card (GroupEpimorphism J ((U ⧸ C.E) ⧸ D.1)) ≤
        Nat.card (J →* ((U ⧸ C.E) ⧸ D.1)) := by
      letI : Finite (J →* ((U ⧸ C.E) ⧸ D.1)) := Finite.of_injective
        (fun f : J →* ((U ⧸ C.E) ⧸ D.1) => (f : J → (U ⧸ C.E) ⧸ D.1))
        DFunLike.coe_injective
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hlog : Nat.log 2 (Nat.card ((U ⧸ C.E) ⧸ D.1)) ≤ C.quotientRank :=
      Nat.log_mono_right (Nat.card_le_card_of_surjective _
        (QuotientGroup.mk_surjective (s := D.1)))
    have hnat : Nat.card (GroupEpimorphism J ((U ⧸ C.E) ⧸ D.1)) ≤
        2 ^ (C.quotientRank * binaryCharacterRank J) :=
      hepi.trans (hhom.trans (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_right _ hlog)))
    calc (Nat.card (GroupEpimorphism J ((U ⧸ C.E) ⧸ D.1)) : ℝ)
        ≤ ((2 ^ (C.quotientRank * binaryCharacterRank J) : ℕ) : ℝ) := by
          exact_mod_cast hnat
      _ = (2 : ℝ) ^ ((C.quotientRank : ℝ) * binaryCharacterRank J) := by
          rw [show ((C.quotientRank : ℝ) * binaryCharacterRank J) =
              ((C.quotientRank * binaryCharacterRank J : ℕ) : ℝ) by push_cast; ring,
            Real.rpow_natCast]
          push_cast
          rfl
  calc (∑ D : {D : Subgroup (U ⧸ C.E) // D.Normal},
        (Nat.card (GroupEpimorphism J ((U ⧸ C.E) ⧸ D.1)) : ℝ))
      ≤ ∑ _D : {D : Subgroup (U ⧸ C.E) // D.Normal},
          (2 : ℝ) ^ ((C.quotientRank : ℝ) * binaryCharacterRank J) :=
        Finset.sum_le_sum (fun D _ => hD D)
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Fintype.card_eq_nat_card]
        rfl

/-- The weighted complete fibre, on every source:
`Z_J(U) ≤ ν(R) Ψ_E(b) 2^(l d₂(J))`. -/
theorem completeSource_weighted {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    fusionCompleteSourceSum U P J ≤
      C.quotientNormalCount * C.outerFactor b *
        (2 : ℝ) ^ ((C.quotientRank : ℝ) * binaryCharacterRank J) := by
  have hJ : Real.logb 2 (Nat.card J) ≤ Real.logb 2 (Nat.factorial b) := by
    apply Real.logb_le_logb_of_le (by norm_num) (by exact_mod_cast Nat.card_pos)
    have := Nat.card_le_card_of_injective (Subtype.val : J → Equiv.Perm (Fin b))
      Subtype.val_injective
    rw [Nat.card_perm, Nat.card_fin] at this
    exact_mod_cast this
  have hΨ : C.chart.outerFactor (Real.logb 2 (Nat.card J)) ≤ C.outerFactor b := by
    change C.chart.outerFactor _ ≤ C.chart.outerFactor _
    unfold SemisimpleNormalChart.outerFactor
    apply Finset.prod_le_prod
    · intro i _
      have := C.chart.factorWeight_nonneg (Real.logb_nonneg (b := 2) (by norm_num)
        (by exact_mod_cast Nat.card_pos : (1 : ℝ) ≤ Nat.card J)) i
      linarith
    · intro i _
      linarith [C.chart.factorWeight_mono hJ i]
  have hsum : fusionCompleteSourceSum U P J ≤
      ∑ N : {N : Subgroup U // N.Normal},
        (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) :=
    Finset.sum_le_sum (fun N _ => fusionSurvivingEpiCount_le_groupEpimorphism_card U P N J)
  have houter := C.chart.outerSum_le (J := J)
  have hR := C.quotientSum_le J
  have hΨ0 : 0 ≤ C.chart.outerFactor (Real.logb 2 (Nat.card J)) :=
    C.chart.outerFactor_nonneg (Real.logb_nonneg (by norm_num)
      (by exact_mod_cast Nat.card_pos))
  calc fusionCompleteSourceSum U P J
      ≤ ∑ N : {N : Subgroup U // N.Normal},
          (Nat.card (GroupEpimorphism J (U ⧸ N.1)) : ℝ) := hsum
    _ ≤ (∑ D : {D : Subgroup (U ⧸ C.E) // D.Normal},
          (Nat.card (GroupEpimorphism J ((U ⧸ C.E) ⧸ D.1)) : ℝ)) *
          C.chart.outerFactor (Real.logb 2 (Nat.card J)) := houter
    _ ≤ (C.quotientNormalCount *
          (2 : ℝ) ^ ((C.quotientRank : ℝ) * binaryCharacterRank J)) *
          C.outerFactor b :=
        mul_le_mul hR hΨ hΨ0 (by positivity)
    _ = _ := by ring

/-- The cold complete fibre: `d₂(J) ≤ 51b/200` implies
`Z_J(U) ≤ ν(R) Ψ_E(b) 2^(51 l b / 200)`. -/
theorem completeSource_cold {b : ℕ}
    (P : Subgroup (U × Equiv.Perm (Fin b)) → Prop)
    (J : Subgroup (Equiv.Perm (Fin b))) (hJ : ¬ BinaryRankHot (51 / 200) J) :
    fusionCompleteSourceSum U P J ≤
      C.quotientNormalCount * C.outerFactor b *
        (2 : ℝ) ^ ((C.quotientRank : ℝ) * ((51 / 200) * b)) := by
  refine (C.completeSource_weighted P J).trans ?_
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _)
    (C.outerFactor_nonneg b))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  unfold BinaryRankHot at hJ
  linarith

end PreE7Sns2ActionCertificate

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
