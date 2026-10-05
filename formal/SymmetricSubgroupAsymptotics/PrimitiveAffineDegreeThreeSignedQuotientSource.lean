import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationLayerSource
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeCyclicComponent
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPairSummedSource

/-!
# Prepending the ternary layer to a signed-quotient source

For an actual imprimitive affine block system of local degree three, divide
out the literal intersection with the regular `C3` translations.  The
resulting signed quotient still acts faithfully on the two nonzero points in
each original block.  This file proves the source-composition theorem needed
by the finitely many exceptional block counts: any relative complete-source
envelope for that literal signed quotient can be used as the endpoint of the
actual ternary elementary step.

The construction keeps the original block map, the literal subgroup
`E block P`, the induced quotient representation, and the joint
annihilator/Yoneda capacity returned by the actual-wreath theorem.  It does
not reindex the quotient as a non-pair catalogue action.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

include P in
/-- Once the regular `C3` component has been excluded, the literal
degree-three affine component is the full natural `S3`.  This is an
order-level conclusion from the actual component; no abstract target is
substituted for it. -/
theorem degreeThree_component_card_eq_six_of_not_dvd_three
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : ¬ Nat.card block.Component ∣ 3) :
    Nat.card block.Component = 6 :=
  (component_card_dvd_three_or_eq_six block P hr).resolve_left hcomponent

/-- The literal joint capacity selected by Tracey's refined theorem for the
first (translation) chief edge of the actual affine component. -/
noncomputable def translationLayerJointCapacity
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let raw := (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    S (LocalQuotient block P) (localMap block P)
      (localMap_surjective block P) C
  exact Classical.choose raw

/-- The selected joint capacity retains the full refined induced-module
inequalities; the choice above does not forget them. -/
theorem translationLayerJointCapacity_refined
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    TraceyRefinedInducedCapacityBounds (localTranslationChart block P).p
      (Module.finrank (ZMod (localTranslationChart block P).p)
        (localTranslationChart block P).V)
      (Fintype.card block.Points)
      (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
        hTraceyRefined hTraceyPerm).capacity := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let raw := (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    S (LocalQuotient block P) (localMap block P)
      (localMap_surjective block P) C
  have h := (Classical.choose_spec raw).2.2.1
  simpa only [translationLayerJointCapacity, S, C] using h

/-- The finite incidence coefficient of the selected ternary layer has the
same explicit bound used by the full affine-component tower. -/
theorem translationLayerJointCapacity_coefficient_le
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).coefficient ≤
      ((localTranslationChart block P).p : ℝ) ^
        traceyAffineCoefficientExponent
        (Module.finrank (ZMod (localTranslationChart block P).p)
          (localTranslationChart block P).V)
        (Fintype.card block.Points)
        (traceyInducedGeneratorCeiling
          (Module.finrank (ZMod (localTranslationChart block P).p)
            (localTranslationChart block P).V)
          (Fintype.card block.Points))
        (traceyPermutationGeneratorCeiling w) w P.p := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let raw := (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    S (LocalQuotient block P) (localMap block P)
      (localMap_surjective block P) C
  have h := (Classical.choose_spec raw).2.2.2.2
  simpa only [translationLayerJointCapacity, S, C, initialState] using h

/-- The selected common capacity is an integer, even though the incidence
record stores it in `ℝ`.  This is needed for the sharp three-block round
down. -/
theorem translationLayerJointCapacity_integral
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput) :
    ∃ h : ℕ, (translationLayerJointCapacity block P hTraceyHalf
      hTraceyLog hTraceyRefined hTraceyPerm).capacity = h := by
  let S := initialState hTraceyPerm block
  let C := localTranslationChart block P
  let raw := (affineCapacityInput hTraceyHalf hTraceyLog hTraceyRefined block)
    S (LocalQuotient block P) (localMap block P)
      (localMap_surjective block P) C
  have h := (Classical.choose_spec raw).2.2.2.1
  simpa only [translationLayerJointCapacity, S, C] using h

/-- In local degree three, the selected translation chart is one-dimensional
over `F3`. -/
theorem degreeThree_translation_prime_dim
    (hr : Nat.card block.Fibre = 3) :
    (localTranslationChart block P).p = 3 ∧
      Module.finrank (ZMod (localTranslationChart block P).p)
        (localTranslationChart block P).V = 1 := by
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V => C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  have hdegree₀ : Nat.card block.Fibre = P.p ^ C₀.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C₀.equiv (origin block)
  have hdegree : 3 = P.p ^ C₀.d := hr.symm.trans hdegree₀
  have hpd := prime_pow_positive_injective (d := C₀.d) (e := 1)
    P.p_prime (by norm_num : Nat.Prime 3) C₀.d_pos (by norm_num)
    (hdegree.symm.trans (by norm_num))
  refine ⟨hpd.1, ?_⟩
  change Module.finrank (ZMod P.p) (chart block P).V = 1
  simpa only [chart, C₀, PrimitiveAffineProfile.ElementaryChart.d] using hpd.2

private theorem degreeThree_translation_capacity_le_of_half
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).capacity ≤
        (Nat.card block.Points : ℝ) / 2 := by
  have href := translationLayerJointCapacity_refined block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm
  have hpd := degreeThree_translation_prime_dim block P hr
  have hhalf := href.half
  rw [hpd.2, Fintype.card_eq_nat_card] at hhalf
  norm_num at hhalf ⊢
  exact hhalf

/-- Three blocks: the soluble prime-power Tracey row is `3/2`, and
integrality sharpens it to one. -/
theorem degreeThree_translation_capacity_threeBlocks
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 3) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).capacity ≤ 1 := by
  let H := translationLayerJointCapacity block P hTraceyHalf hTraceyLog
    hTraceyRefined hTraceyPerm
  have href := translationLayerJointCapacity_refined block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm
  have hpd := degreeThree_translation_prime_dim block P hr
  have hpow := href.primePower 3 1 (by norm_num) (by norm_num) (by
    simpa only [Fintype.card_eq_nat_card, hs] using
      (show (3 : ℕ) = 3 ^ 1 by norm_num))
  rw [hpd.2, Fintype.card_eq_nat_card, hs] at hpow
  obtain ⟨h, hh⟩ := translationLayerJointCapacity_integral block P
    hTraceyHalf hTraceyLog hTraceyRefined hTraceyPerm
  change H.capacity ≤ 1
  norm_num at hpow
  rw [hh] at hpow ⊢
  norm_num at hpow ⊢
  have hh2 : (h : ℝ) < 2 := by linarith
  have hh2' : h < 2 := by exact_mod_cast hh2
  exact_mod_cast (Nat.le_of_lt_succ hh2')

/-- Four blocks: the binary square is prime to the ternary characteristic,
so the refined capacity is at most one. -/
theorem degreeThree_translation_capacity_fourBlocks
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 4) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).capacity ≤ 1 := by
  have href := translationLayerJointCapacity_refined block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm
  have hpd := degreeThree_translation_prime_dim block P hr
  have h := href.primeTo 2 2 Nat.prime_two (by omega) (by norm_num) (by
    rw [Fintype.card_eq_nat_card, hs]
    norm_num)
  rw [hpd.2, Fintype.card_eq_nat_card, hs] at h
  norm_num at h ⊢
  exact h

/-- Six blocks: the unconditional half bound gives capacity three.  A
degree-six semiregular ternary top can improve this to two, but the generic
prepend theorem only needs the bound actually requested by its endpoint
package. -/
theorem degreeThree_translation_capacity_sixBlocks
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 6) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).capacity ≤ 3 := by
  have h := degreeThree_translation_capacity_le_of_half block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  rw [hs] at h
  norm_num at h ⊢
  exact h

/-- Twelve blocks: the binary square divisor gives capacity three. -/
theorem degreeThree_translation_capacity_twelveBlocks
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 12) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).capacity ≤ 3 := by
  have href := translationLayerJointCapacity_refined block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm
  have hpd := degreeThree_translation_prime_dim block P hr
  have h := href.primeTo 2 2 Nat.prime_two (by omega) (by norm_num) (by
    rw [Fintype.card_eq_nat_card, hs]
    norm_num)
  rw [hpd.2, Fintype.card_eq_nat_card, hs] at h
  norm_num at h ⊢
  exact h

/-- Eighteen blocks: the unconditional half bound gives capacity nine.
Sharper soluble/semiregular rows may be supplied by the signed-quotient
package, but no classification premise is hidden here. -/
theorem degreeThree_translation_capacity_eighteenBlocks
    (hTraceyHalf : TraceyAffineHalfInducedModuleInput)
    (hTraceyLog : TraceyAffineInducedModuleInput)
    (hTraceyRefined : TraceyRefinedInducedModuleInput)
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hs : Nat.card block.Points = 18) :
    (translationLayerJointCapacity block P hTraceyHalf hTraceyLog
      hTraceyRefined hTraceyPerm).capacity ≤ 9 := by
  have h := degreeThree_translation_capacity_le_of_half block P hTraceyHalf
    hTraceyLog hTraceyRefined hTraceyPerm hr
  rw [hs] at h
  norm_num at h ⊢
  exact h

/-- Prepend the literal affine translation layer to an arbitrary source on
the signed quotient `U / E`.  The previous translation-stop construction is
the special case in which `Q` is the identity envelope of that quotient. -/
noncomputable def translationLayerEnvelopeOver
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (Q : RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P)) :
    RelativeCompleteSourceEnvelope (preE7NonPairAction w U) := by
  let C₀ := P.elementaryChart block.component_preprimitive
  letI : Fact P.p.Prime := C₀.primeFact
  letI : AddCommGroup C₀.V := C₀.addCommGroup
  letI : Module (ZMod P.p) C₀.V := C₀.module
  letI : FiniteDimensional (ZMod P.p) C₀.V := C₀.finiteDimensional
  letI : Finite C₀.V := Finite.of_injective
    (fun v : C₀.V => C₀.equiv.symm (Multiplicative.ofAdd v))
    C₀.equiv.symm.injective
  letI : Finite (TranslationSubmodule block P) :=
    Finite.of_injective (TranslationSubmodule block P).subtype
      (TranslationSubmodule block P).subtype_injective
  letI : Finite (elementaryChart block P).V := by
    change Finite (TranslationSubmodule block P)
    infer_instance
  letI : Finite (elementaryChart block P).quotientRepresentation :=
    inferInstanceAs (Finite (elementaryChart block P).V)
  exact RelativeCompleteSourceEnvelope.elementaryStep
    (p := (elementaryChart block P).p)
    (E block P) (elementaryChart block P) H Q

@[simp] theorem translationLayerEnvelopeOver_v
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (Q : RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P)) :
    (translationLayerEnvelopeOver block P H Q).v = Q.v := rfl

@[simp] theorem translationLayerEnvelopeOver_eta
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (Q : RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P)) :
    (translationLayerEnvelopeOver block P H Q).eta =
      Real.logb 2 (elementaryChart block P).p /
          (elementaryChart block P).p * H.capacity + Q.eta := rfl

@[simp] theorem translationLayerEnvelopeOver_coefficient
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (Q : RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P))
    (b : ℕ) :
    (translationLayerEnvelopeOver block P H Q).coefficient b =
      H.coefficient * Q.coefficient b := rfl

/-- Construction-facing source composition.  All group theory is in the
literal elementary step above.  The argument `M` contains only the combined
numerical margin and the finite coefficient estimate, so degree-specific
pair-source files can discharge it without rebuilding the transfer. -/
noncomputable def translationLayerSourceOver
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (Q : RelativeCompleteSourceEnvelope
      (preE7NonPairAction w U ⧸ E block P))
    (M : RelativeCompleteSourceEnvelope.PreE7Margin
      (translationLayerEnvelopeOver block P H Q)) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  RelativeCompleteSourceEnvelope.toRankTailSourceOrYonedaTopOfMargin
    .acert (translationLayerEnvelopeOver block P H Q) M

/-- Source-summed form of the same literal ternary step.  This is the
interface needed when the signed quotient is controlled by a correlated
binary rank-tail estimate rather than by a pointwise comparator envelope.
The complete source on `U` is first enlarged to the complete quotient
weight, so the statement is independent of the survival predicate. -/
theorem translationLayer_summedSource_le
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (b : ℕ)
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w U) source J) ≤
      H.coefficient *
        (2 : ℝ) ^
          ((Real.logb 2 (elementaryChart block P).p /
              (elementaryChart block P).p * H.capacity) * b) *
        (∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J) := by
  let Q := RelativeCompleteSourceEnvelope.identity
    (preE7NonPairAction w U ⧸ E block P)
    (quotientDegree block) (quotientAction block P)
    (quotientAction_injective block P)
  let T := translationLayerEnvelopeOver block P H Q
  have hpoint : ∀ J : Subgroup (Equiv.Perm (Fin b)),
      fusionCompleteSourceSum (preE7NonPairAction w U) source J ≤
        H.coefficient *
          (2 : ℝ) ^
            ((Real.logb 2 (elementaryChart block P).p /
                (elementaryChart block P).p * H.capacity) * b) *
          completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J := by
    intro J
    calc
      fusionCompleteSourceSum (preE7NonPairAction w U) source J ≤
          completeQuotientWeight (R := preE7NonPairAction w U) J := by
        unfold fusionCompleteSourceSum completeQuotientWeight
          completeQuotientCount
        rw [Nat.cast_sum]
        exact Finset.sum_le_sum (fun N _ =>
          fusionSurvivingEpiCount_le_groupEpimorphism_card
            (preE7NonPairAction w U) source N J)
      _ ≤ T.coefficient b * (2 : ℝ) ^ (T.eta * b) *
          completeQuotientWeight (R := T.R) J := T.bound b J
      _ = H.coefficient *
          (2 : ℝ) ^
            ((Real.logb 2 (elementaryChart block P).p /
                (elementaryChart block P).p * H.capacity) * b) *
          completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J := by
        simp only [T, Q, translationLayerEnvelopeOver,
          RelativeCompleteSourceEnvelope.elementaryStep,
          RelativeCompleteSourceEnvelope.identity, mul_one, add_zero]
  calc
    _ ≤ ∑ J : Subgroup (Equiv.Perm (Fin b)),
        (H.coefficient *
          (2 : ℝ) ^
            ((Real.logb 2 (elementaryChart block P).p /
                (elementaryChart block P).p * H.capacity) * b)) *
          completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J :=
      Finset.sum_le_sum (fun J _ => hpoint J)
    _ = _ := by rw [Finset.mul_sum]

/-- Compose any proved aggregate estimate for the signed quotient with the
literal ternary layer.  The coefficient and ternary exponent remain outside
the sum, which is essential for the hot/cold pair-action rows. -/
theorem translationLayer_summedSource_le_of_signedQuotient
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (b : ℕ)
    (source : Subgroup
      (preE7NonPairAction w U × Equiv.Perm (Fin b)) → Prop)
    (F : ℝ)
    (hF : (∑ J : Subgroup (Equiv.Perm (Fin b)),
      completeQuotientWeight
        (R := preE7NonPairAction w U ⧸ E block P) J) ≤ F) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w U) source J) ≤
      H.coefficient *
        (2 : ℝ) ^
          ((Real.logb 2 (elementaryChart block P).p /
              (elementaryChart block P).p * H.capacity) * b) * F := by
  exact (translationLayer_summedSource_le block P H b source).trans
    (mul_le_mul_of_nonneg_left hF
      (mul_nonneg H.coefficient_nonneg (by positivity)))

/-! ## Prepending to a correlated signed-quotient source -/

/-- Prepend the literal ternary layer to a raw correlated source on its
signed quotient.  Both cold and main exponents receive the *same* retained
ternary cost, and the hot scalar is multiplied by that cost only once.
This is the source-level operation needed by the central-product pair rows;
physical pointing has not yet occurred. -/
noncomputable def prependSignedQuotientSummedSource
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart)
    (S : PreE7DegreeTwoPairQuotientSummedEnvelope
      (preE7NonPairAction w U ⧸ E block P))
    (v : ℕ) (action : S.R →* Equiv.Perm (Fin v))
    (action_injective : Function.Injective action) :
    PreE7DegreeTwoPairSummedSource w U := by
  let tau : ℝ := Real.logb 2 (elementaryChart block P).p /
    (elementaryChart block P).p * H.capacity
  refine
    { R := S.R
      groupR := S.groupR
      finiteR := S.finiteR
      v := v
      action := action
      action_injective := action_injective
      mainCoefficient := H.coefficient * S.mainCoefficient
      coldCoefficient := fun b ↦ H.coefficient * S.coldCoefficient b
      eta := tau + S.eta
      theta := tau + S.theta
      mainCoefficient_nonneg :=
        mul_nonneg H.coefficient_nonneg S.mainCoefficient_nonneg
      coldCoefficient_nonneg := fun b ↦
        mul_nonneg H.coefficient_nonneg (S.coldCoefficient_nonneg b)
      exceptionalRaw := fun b ↦
        (H.coefficient * (2 : ℝ) ^ (tau * b)) * S.exceptionalRaw b
      exceptionalRaw_nonneg := fun b ↦
        mul_nonneg
          (mul_nonneg H.coefficient_nonneg (by positivity))
          (S.exceptionalRaw_nonneg b)
      summed := ?_ }
  intro b source
  let L : ℝ := H.coefficient * (2 : ℝ) ^ (tau * b)
  have hLayer := translationLayer_summedSource_le block P H b source
  have hTop := S.summed b
  have hL : 0 ≤ L :=
    mul_nonneg H.coefficient_nonneg (by positivity)
  calc
    (∑ J : Subgroup (Equiv.Perm (Fin b)),
        fusionCompleteSourceSum (preE7NonPairAction w U) source J) ≤
        L * (∑ J : Subgroup (Equiv.Perm (Fin b)),
          completeQuotientWeight
            (R := preE7NonPairAction w U ⧸ E block P) J) := by
      simpa only [L, tau] using hLayer
    _ ≤ L * ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          ((S.mainCoefficient * (2 : ℝ) ^ (S.eta * b)) *
              completeQuotientWeight (R := S.R) J +
            S.coldCoefficient b * (2 : ℝ) ^ (S.theta * b))) +
          S.exceptionalRaw b) :=
      mul_le_mul_of_nonneg_left hTop hL
    _ = ((∑ J : Subgroup (Equiv.Perm (Fin b)),
          (((H.coefficient * S.mainCoefficient) *
              (2 : ℝ) ^ ((tau + S.eta) * b)) *
                completeQuotientWeight (R := S.R) J +
            (H.coefficient * S.coldCoefficient b) *
              (2 : ℝ) ^ ((tau + S.theta) * b))) +
          (H.coefficient * (2 : ℝ) ^ (tau * b)) *
            S.exceptionalRaw b) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro J _
      rw [mul_add,
        show (tau + S.eta) * (b : ℝ) = tau * b + S.eta * b by ring,
        show (tau + S.theta) * (b : ℝ) = tau * b + S.theta * b by ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      dsimp only [L]
      ring

/-- Raw endpoint data for the signed quotient.  This is deliberately an
envelope, rather than an already padded owner at physical width `2s`, because
the ternary layer must be prepended before the original weight `3s` is
tested. -/
structure DegreeThreeSignedQuotientSourceData
    (H : ElementaryLayerJointCapacityBound
      (elementaryChart block P).p
      (QuotientGroup.mk' (E block P))
      (QuotientGroup.mk'_surjective (E block P))
      (elementaryChart block P).quotientRepresentation
      (elementaryChart block P).originalKernelChart) : Type 1 where
  quotientEnvelope : RelativeCompleteSourceEnvelope
    (preE7NonPairAction w U ⧸ E block P)
  ambientMargin : RelativeCompleteSourceEnvelope.PreE7Margin
    (translationLayerEnvelopeOver block P H quotientEnvelope)

namespace DegreeThreeSignedQuotientSourceData

variable
  {H : ElementaryLayerJointCapacityBound
    (elementaryChart block P).p
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (elementaryChart block P).originalKernelChart}

/-- Final ambient source obtained without changing the action label or the
physical weight. -/
noncomputable def source
    (D : DegreeThreeSignedQuotientSourceData block P H) :
    PreE7RankTailSourceOrYonedaTopData w U :=
  translationLayerSourceOver block P H D.quotientEnvelope D.ambientMargin

end DegreeThreeSignedQuotientSourceData

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
