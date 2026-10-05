import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource
import SymmetricSubgroupAsymptotics.Non2PreE7Y1RankTailInstance

/-!
# The source-summed row for the two central three-pair actions

The actions `A4 × C2` and `S4 × C2` have two equal-width lower axes.
They cannot be assigned independently to a smaller comparator.  The checked
normal-axis dichotomy is instead used by the concrete constructors to prove
one cold complete-source bound.  This file performs the reusable hot/cold
sum, retaining both the ordinary binary rank and the index-three-kernel
binary rank on the same complete source.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

attribute [-instance] originalNormalFintype

namespace Non2UnipotentPrefixFiniteMenu

/-- The union of the two rank tests needed by the central-product rows. -/
def CentralProductRankHot (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) : Prop :=
  BinaryRankHot (51 / 200) J ∨ IndexThreeRankHot (51 / 200) J

/-- The two rank tails are kept on the same complete source.  The first is
the ordinary binary rank tail; the second selects an actual index-three
kernel and costs one further permutation. -/
theorem centralProductRankHot_card_le (b : ℕ) :
    ((Finset.univ.filter (CentralProductRankHot b)).card : ℝ) ≤
      (1 + Nat.factorial b) *
        ((2 : ℝ) ^
            (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
          (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ)) := by
  let H := {J : Subgroup (Equiv.Perm (Fin b)) // CentralProductRankHot b J}
  let HB := {J : Subgroup (Equiv.Perm (Fin b)) // BinaryRankHot (51 / 200) J}
  let HI := {J : Subgroup (Equiv.Perm (Fin b)) // IndexThreeRankHot (51 / 200) J}
  let f : H → HB ⊕ HI := fun J =>
    if hJ : BinaryRankHot (51 / 200) J.1 then Sum.inl ⟨J.1, hJ⟩
    else Sum.inr ⟨J.1, J.2.resolve_left hJ⟩
  have hf : Function.Injective f := by
    intro J K hJK
    apply Subtype.ext
    by_cases hJ : BinaryRankHot (51 / 200) J.1
    · by_cases hK : BinaryRankHot (51 / 200) K.1
      · have h' : (⟨J.1, hJ⟩ : HB) = ⟨K.1, hK⟩ := by
          exact Sum.inl.inj (by simpa only [f, hJ, hK, dite_true] using hJK)
        exact congrArg (fun z : HB => z.1) h'
      · simp only [f, hJ, hK, dite_true, dite_false, reduceCtorEq] at hJK
    · by_cases hK : BinaryRankHot (51 / 200) K.1
      · simp only [f, hJ, hK, dite_true, dite_false, reduceCtorEq] at hJK
      · have h' : (⟨J.1, J.2.resolve_left hJ⟩ : HI) =
            ⟨K.1, K.2.resolve_left hK⟩ := by
          exact Sum.inr.inj (by simpa only [f, hJ, hK, dite_false] using hJK)
        exact congrArg (fun z : HI => z.1) h'
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_sum] at hcard
  have hH : (Finset.univ.filter (CentralProductRankHot b)).card = Nat.card H := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hB : (Finset.univ.filter
      (fun J : Subgroup (Equiv.Perm (Fin b)) => BinaryRankHot (51 / 200) J)).card =
      Nat.card HB := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hI : (Finset.univ.filter
      (fun J : Subgroup (Equiv.Perm (Fin b)) => IndexThreeRankHot (51 / 200) J)).card =
      Nat.card HI := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hH]
  have hcast : (Nat.card H : ℝ) ≤ Nat.card HB + Nat.card HI := by
    exact_mod_cast hcard
  refine hcast.trans ?_
  have hbinary := binaryRankHot51_card_le b
  have hindex := (indexThreeRankHot_card_le (51 / 200) b).trans
    (mul_le_mul_of_nonneg_left hbinary (Nat.cast_nonneg _))
  rw [hB] at hbinary
  rw [hI] at hindex
  calc
    (Nat.card HB : ℝ) + Nat.card HI ≤
        ((2 : ℝ) ^
            (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
          (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ)) +
        (Nat.factorial b : ℝ) *
          ((2 : ℝ) ^
              (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ)) :=
      add_le_add hbinary hindex
    _ = _ := by ring

/-- Literal structural/counting data before a permutation action is
selected.  In the two concrete applications `E` is the natural Klein layer
in the first direct factor.  The checked normal-axis dichotomy proves the
`lower_axis_cold` field: an axis not containing `E` lies in the central
binary factor, hence its quotient is one of the two retained lower targets.
-/
structure PreE7CentralProductRankTailData
    (Q : Type) [Group Q] [Finite Q] : Type 1 where
  E : Subgroup Q
  [E_normal : E.Normal]
  action : (Q ⧸ E) →* Equiv.Perm (Fin 5)
  action_injective : Function.Injective action
  lowerConstant : ℝ
  lowerConstant_nonneg : 0 ≤ lowerConstant
  lower_axis_cold : ∀ (N : {N : Subgroup Q // N.Normal})
      (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))),
    ¬ E ≤ N.1 → ¬ CentralProductRankHot b J →
      (Nat.card (GroupEpimorphism J (Q ⧸ N.1)) : ℝ) ≤
        lowerConstant * (2 : ℝ) ^ ((3 / 5 : ℝ) * b)
  order_le : Nat.card Q ≤ 2 ^ 16

attribute [instance] PreE7CentralProductRankTailData.E_normal

namespace PreE7CentralProductRankTailData

variable {Q : Type} [Group Q] [Finite Q]
  (D : PreE7CentralProductRankTailData Q)

/-- Number of literal original normal axes. -/
def normalCount (_D : PreE7CentralProductRankTailData Q) : ℝ :=
  Nat.card {N : Subgroup Q // N.Normal}

theorem normalCount_nonneg : 0 ≤ normalCount D := Nat.cast_nonneg _

/-- The whole cold quotient menu.  Axes above `E` are literal quotient
axes of `Q/E`; all other axes use the central-product lower estimate. -/
theorem completeWeight_cold (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬ CentralProductRankHot b J) :
    completeQuotientWeight (R := Q) J ≤
      normalCount D * completeQuotientWeight (R := Q ⧸ D.E) J +
        (normalCount D * D.lowerConstant) *
          (2 : ℝ) ^ ((3 / 5 : ℝ) * b) := by
  unfold completeQuotientWeight completeQuotientCount normalCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup Q // N.Normal},
        (Nat.card (GroupEpimorphism J (Q ⧸ N.1)) : ℝ)) ≤
      ∑ N : {N : Subgroup Q // N.Normal},
        (completeQuotientWeight (R := Q ⧸ D.E) J +
          D.lowerConstant * (2 : ℝ) ^ ((3 / 5 : ℝ) * b)) := by
      apply Finset.sum_le_sum
      intro N _
      by_cases hN : D.E ≤ N.1
      · have haxis := card_groupEpimorphism_le_completeQuotientWeight J
          (⟨N.1.map (QuotientGroup.mk' D.E), inferInstance⟩ :
            {M : Subgroup (Q ⧸ D.E) // M.Normal})
          (QuotientGroup.quotientQuotientEquivQuotient D.E N.1 hN).symm
        exact haxis.trans (le_add_of_nonneg_right
          (mul_nonneg D.lowerConstant_nonneg (by positivity)))
      · exact (D.lower_axis_cold N b J hN hJ).trans
          (le_add_of_nonneg_left (completeQuotientWeight_nonneg J))
    _ = (Nat.card {N : Subgroup Q // N.Normal} : ℝ) *
          completeQuotientWeight (R := Q ⧸ D.E) J +
        ((Nat.card {N : Subgroup Q // N.Normal} : ℝ) * D.lowerConstant) *
          (2 : ℝ) ^ ((3 / 5 : ℝ) * b) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        ← Nat.card_eq_fintype_card]
      ring

/-- The unrestricted finite-order envelope for the complete literal normal
menu. -/
theorem completeWeight_full (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    completeQuotientWeight (R := Q) J ≤
      normalCount D * ((Nat.factorial b : ℕ) : ℝ) ^ 16 := by
  unfold completeQuotientWeight completeQuotientCount normalCount
  rw [Nat.cast_sum]
  calc
    (∑ N : {N : Subgroup Q // N.Normal},
        (Nat.card (GroupEpimorphism J (Q ⧸ N.1)) : ℝ)) ≤
      ∑ _N : {N : Subgroup Q // N.Normal},
        ((Nat.factorial b : ℕ) : ℝ) ^ 16 := by
      apply Finset.sum_le_sum
      intro N _
      have hquot : Nat.card (Q ⧸ N.1) ≤ 2 ^ 16 :=
        (Nat.card_le_card_of_surjective (QuotientGroup.mk' N.1)
          (QuotientGroup.mk'_surjective N.1)).trans D.order_le
      exact_mod_cast groupEpimorphism_card_le_factorial_pow J hquot
    _ = (Nat.card {N : Subgroup Q // N.Normal} : ℝ) *
        ((Nat.factorial b : ℕ) : ℝ) ^ 16 := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        ← Nat.card_eq_fintype_card]

end PreE7CentralProductRankTailData

/-- The exact source-facing datum for an equal-width central-product row.
The two hard group-specific facts are a cold bound on the whole literal
normal menu and an unrestricted finite-order bound.  They are proved by the
`A4 × C2` and `S4 × C2` constructors from the normal-axis dichotomy. -/
structure PreE7DegreeSixCentralProductSource
    (U : PreE7NonPairActionClass 6) : Type 1 where
  R : Type
  [groupR : Group R]
  [finiteR : Finite R]
  action : R →* Equiv.Perm (Fin 5)
  action_injective : Function.Injective action
  mainConstant : ℝ
  coldConstant : ℝ
  fullConstant : ℝ
  mainConstant_nonneg : 0 ≤ mainConstant
  coldConstant_nonneg : 0 ≤ coldConstant
  fullConstant_nonneg : 0 ≤ fullConstant
  completeWeight_cold : ∀ (b : ℕ)
      (J : Subgroup (Equiv.Perm (Fin b))),
    ¬ CentralProductRankHot b J →
      completeQuotientWeight (R := preE7NonPairAction 6 U) J ≤
        mainConstant * completeQuotientWeight (R := R) J +
          coldConstant * (2 : ℝ) ^ ((3 / 5 : ℝ) * b)
  completeWeight_full : ∀ (b : ℕ)
      (J : Subgroup (Equiv.Perm (Fin b))),
    completeQuotientWeight (R := preE7NonPairAction 6 U) J ≤
      fullConstant * ((Nat.factorial b : ℕ) : ℝ) ^ 16

attribute [instance]
  PreE7DegreeSixCentralProductSource.groupR
  PreE7DegreeSixCentralProductSource.finiteR

/-- A literal central-product datum on the selected six-point action gives
the action-facing source. -/
noncomputable def PreE7DegreeSixCentralProductSource.ofLiteral
    {U : PreE7NonPairActionClass 6}
    (D : PreE7CentralProductRankTailData (preE7NonPairAction 6 U)) :
    PreE7DegreeSixCentralProductSource U where
  R := preE7NonPairAction 6 U ⧸ D.E
  action := D.action
  action_injective := D.action_injective
  mainConstant := PreE7CentralProductRankTailData.normalCount D
  coldConstant := PreE7CentralProductRankTailData.normalCount D * D.lowerConstant
  fullConstant := PreE7CentralProductRankTailData.normalCount D
  mainConstant_nonneg := PreE7CentralProductRankTailData.normalCount_nonneg D
  coldConstant_nonneg := mul_nonneg
    (PreE7CentralProductRankTailData.normalCount_nonneg D)
    D.lowerConstant_nonneg
  fullConstant_nonneg := PreE7CentralProductRankTailData.normalCount_nonneg D
  completeWeight_cold := PreE7CentralProductRankTailData.completeWeight_cold D
  completeWeight_full := PreE7CentralProductRankTailData.completeWeight_full D

namespace PreE7DegreeSixCentralProductSource

variable {U : PreE7NonPairActionClass 6}
  (C : PreE7DegreeSixCentralProductSource U)

/-- The complete source sum with the two rank tests retained jointly. -/
theorem summedCompleteWeight_le (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientWeight (R := preE7NonPairAction 6 U) J) ≤
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (C.mainConstant * completeQuotientWeight (R := C.R) J +
          C.coldConstant * (2 : ℝ) ^ ((3 / 5 : ℝ) * b))) +
        C.fullConstant * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((1 + Nat.factorial b) *
            ((2 : ℝ) ^
                (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
  let hot : Subgroup (Equiv.Perm (Fin b)) → Prop := CentralProductRankHot b
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ hot]
  refine (add_comm _ _).le.trans (add_le_add ?_ ?_)
  · calc
      (∑ J ∈ Finset.univ.filter (fun J => ¬ hot J),
          completeQuotientWeight (R := preE7NonPairAction 6 U) J) ≤
          ∑ J ∈ Finset.univ.filter (fun J => ¬ hot J),
            (C.mainConstant * completeQuotientWeight (R := C.R) J +
              C.coldConstant * (2 : ℝ) ^ ((3 / 5 : ℝ) * b)) := by
        apply Finset.sum_le_sum
        intro J hJ
        exact C.completeWeight_cold b J (Finset.mem_filter.mp hJ).2
      _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
            (C.mainConstant * completeQuotientWeight (R := C.R) J +
              C.coldConstant * (2 : ℝ) ^ ((3 / 5 : ℝ) * b)) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro J _ _
        exact add_nonneg
          (mul_nonneg C.mainConstant_nonneg (completeQuotientWeight_nonneg J))
          (mul_nonneg C.coldConstant_nonneg (by positivity))
  · calc
      (∑ J ∈ Finset.univ.filter hot,
          completeQuotientWeight (R := preE7NonPairAction 6 U) J) ≤
          ∑ _J ∈ Finset.univ.filter hot,
            C.fullConstant * ((Nat.factorial b : ℕ) : ℝ) ^ 16 := by
        apply Finset.sum_le_sum
        intro J _
        exact C.completeWeight_full b J
      _ = C.fullConstant * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((Finset.univ.filter hot).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ C.fullConstant * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
          ((1 + Nat.factorial b) *
            ((2 : ℝ) ^
                (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
              (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
        apply mul_le_mul_of_nonneg_left (centralProductRankHot_card_le b)
        exact mul_nonneg C.fullConstant_nonneg (by positivity)

/-- A slightly enlarged exceptional term with one clean factorial power.
This is the form used both by the degree-two decay proof and by the
degree-three prepend. -/
def exceptionalEnvelope (b : ℕ) : ℝ :=
  (2 * C.fullConstant) * ((Nat.factorial b : ℕ) : ℝ) ^ 17 *
    ((2 : ℝ) ^
        (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
      (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))

theorem exceptional_term_le_envelope (b : ℕ) :
    C.fullConstant * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((1 + Nat.factorial b) *
          ((2 : ℝ) ^
              (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) ≤
      C.exceptionalEnvelope b := by
  have hf : (1 : ℝ) ≤ Nat.factorial b := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero b))
  have htail : 0 ≤
      (2 : ℝ) ^ (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
        (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ) := by
    have hs : (0 : ℝ) ≤ subgroupCount (b + 2 * rankTail51Tilt b) := by
      exact_mod_cast (subgroupCount_pos _).le
    positivity
  unfold exceptionalEnvelope
  calc
    _ ≤ C.fullConstant * ((Nat.factorial b : ℕ) : ℝ) ^ 16 *
        ((2 * Nat.factorial b : ℝ) *
          ((2 : ℝ) ^
              (-((rankTail51Tilt b : ℝ) * (51 / 200) * b)) *
            (subgroupCount (b + 2 * rankTail51Tilt b) : ℝ))) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right (by linarith) htail
      · exact mul_nonneg C.fullConstant_nonneg (by positivity)
    _ = _ := by ring

/-- Complete-source form with the clean exceptional envelope. -/
theorem summedCompleteWeight_envelope_le (b : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        completeQuotientWeight (R := preE7NonPairAction 6 U) J) ≤
      (∑ J : Subgroup (Equiv.Perm (Fin b)),
        (C.mainConstant * completeQuotientWeight (R := C.R) J +
          C.coldConstant * (2 : ℝ) ^ ((3 / 5 : ℝ) * b))) +
        C.exceptionalEnvelope b := by
  exact (C.summedCompleteWeight_le b).trans
    (add_le_add_right (C.exceptional_term_le_envelope b) _)

/-- Public literal finite-group package consumed by the degree-three
signed-quotient composition before any physical pointing. -/
noncomputable def quotientSummedEnvelope :
    PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction 6 U) where
  R := C.R
  mainCoefficient := C.mainConstant
  coldCoefficient := fun _ => C.coldConstant
  eta := 0
  theta := 3 / 5
  mainCoefficient_nonneg := C.mainConstant_nonneg
  coldCoefficient_nonneg := fun _ => C.coldConstant_nonneg
  exceptionalRaw := fun b =>
    C.exceptionalEnvelope b
  exceptionalRaw_nonneg := fun b => by
    have hs : (0 : ℝ) ≤ subgroupCount (b + 2 * rankTail51Tilt b) := by
      exact_mod_cast (subgroupCount_pos _).le
    unfold exceptionalEnvelope
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) C.fullConstant_nonneg)
        (by positivity)) (mul_nonneg (by positivity) hs)
  summed := fun b => by
    simpa only [zero_mul, Real.rpow_zero, mul_one] using
      C.summedCompleteWeight_envelope_le b

/-- Public action package.  Forgetting the accepted predicate embeds its
complete source in the literal complete quotient weight, so no second
counting argument is used here. -/
noncomputable def rawSummedSource :
    PreE7DegreeTwoPairSummedSource 6 U where
  R := C.R
  v := 5
  action := C.action
  action_injective := C.action_injective
  mainCoefficient := C.mainConstant
  coldCoefficient := fun _ => C.coldConstant
  eta := 0
  theta := 3 / 5
  mainCoefficient_nonneg := C.mainConstant_nonneg
  coldCoefficient_nonneg := fun _ => C.coldConstant_nonneg
  exceptionalRaw := fun b =>
    C.exceptionalEnvelope b
  exceptionalRaw_nonneg := fun b => by
    have hs : (0 : ℝ) ≤ subgroupCount (b + 2 * rankTail51Tilt b) := by
      exact_mod_cast (subgroupCount_pos _).le
    unfold exceptionalEnvelope
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) C.fullConstant_nonneg)
        (by positivity)) (mul_nonneg (by positivity) hs)
  summed := fun b P => by
    apply (Finset.sum_le_sum (fun J _ => ?_)).trans
      ((C.quotientSummedEnvelope).summed b)
    unfold fusionCompleteSourceSum completeQuotientWeight completeQuotientCount
    rw [Nat.cast_sum]
    exact Finset.sum_le_sum (fun N _ =>
      fusionSurvivingEpiCount_le_groupEpimorphism_card
        (preE7NonPairAction 6 U) P N J)

end PreE7DegreeSixCentralProductSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
