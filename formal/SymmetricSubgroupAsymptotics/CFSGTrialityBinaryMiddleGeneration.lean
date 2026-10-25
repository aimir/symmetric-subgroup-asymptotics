import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleVectorAction
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryShortWeylTensorAction
import SymmetricSubgroupAsymptotics.CFSGTrialityBinaryRaisedTensor
import SymmetricSubgroupAsymptotics.BinaryRegularTranslationGeneration

/-! Explicit generation of the actual binary middle quotient: regular
translations on its norm-curve basis and one actual Weyl word taking
the nonzero translation-fixed vector to the zero basis vertex. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleGeneration
open CFSGTrialityMiddleFixedTensorSpan CFSGTrialityBinaryMiddleNormalizer
open CFSGTrialityBinaryMiddleVectorAction CFSGTrialityBinaryNormCurveBasis
open CFSGTrialityBinaryTensorTranslationAction CFSGTrialityBinaryRaisedTensor
open CFSGTrialityGeckMiddleFixedTensorImage CFSGTrialityGeckMiddleTensorCovariance
open CFSGTrialityGeckMiddleFirstLayer CFSGTrialityBinaryShortWeylTensorAction
open CFSGTrialityBinaryShortWeylTensorRoots CFSGCubicNormMonomialSeparation
local instance trialityMiddleGenerationRootsDecidableEq :
    DecidableEq (CFSGNormTwoRootPairing.Roots (CartanMatrix.D 4)) := Classical.decEq _

private theorem curve_zero_embedding (q : CFSG.PrimePower) (hq : q.order=2) :
    fixedTensorEmbedding q (curve q 0)=actualTensor (K q) 0 := by
  have hz : normCurve q.order (0 : K q)=Pi.single 0 1 := by
    funext i
    fin_cases i <;> norm_num [normCurve,exponent,hq,Pi.single_apply]
  change tensorCoordinates (K q) (normCurve q.order 0)=_
  rw [hz]
  change (∑ i : Fin 8, (Pi.single 0 (1 : K q) : Fin 8 → K q) i • actualTensor (K q) i)=_
  simp [Pi.single_apply]

theorem weyl_vectorAction_raised (q : CFSG.PrimePower) (hq : q.order=2) :
    vectorAction q hq (weylElement q) (raised q)=curve q 0 := by
  have hp : q.prime=2 := (Nat.Prime.pow_inj' q.prime_isPrime Nat.prime_two
    q.exponent_pos.ne' (by decide : (1 : ℕ)≠0)
    (show q.prime^q.exponent=2^1 from hq)).1
  letI : CharP (K q) 2 := Eq.mp (congrArg (fun p => CharP (K q) p) hp)
    (inferInstance : CharP (K q) q.prime)
  apply fixedTensorEmbedding_injective q
  calc
    _ = CFSGAlgebraConjugationAction.action (K q) (Mat (K q))
        (CFSGTrialityGeckFixedRootWords.shortWeyl (K q))
        (fixedTensorEmbedding q (raised q)) :=
      vectorAction_matrix q hq (weylElement q) (short_word_preserving (K q)) (raised q)
    _ = actualTensor (K q) 0 := by rw [raised_embedding]; exact short_word_raised (K q)
    _ = _ := (curve_zero_embedding q hq).symm

theorem invariant_eq_bot_or_top (q : CFSG.PrimePower) (hq : q.order=2)
    (W : Submodule (F q) (fullEnvelope q))
    (hW : ∀ g : carrier q, ∀ x ∈ W, vectorAction q hq g x ∈ W) : W=⊥ ∨ W=⊤ := by
  have hF : Nat.card (F q)=2 := (CFSGTrialityFixedField.fixedField_card q).trans hq
  have hA : IsPGroup 2 (Multiplicative (K q)) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (K q) ≃ K q),
      CFSGTrialityTripleFixedRoots.extension_three_card,hq])
  apply BinaryRegularTranslationGeneration.eq_bot_or_eq_top hF hA
    (curveBasis q hq) (translationAction q hq) ?_
    (raised q) (raised_ne_zero q) (raised_translation_fixed q hq)
    (vectorAction q hq (weylElement q)).toLinearMap ?_ W ?_ ?_
  · intro a t
    rw [curveBasis_apply,curveBasis_apply,translationAction_curve]
  · exact (weyl_vectorAction_raised q hq).trans (curveBasis_apply q hq 0).symm
  · intro a x hx
    change translationAction q hq (Multiplicative.ofAdd a.toAdd) x ∈ W
    rw [←positive_vectorAction]
    exact hW (positiveElement q a.toAdd) x hx
  · intro x hx
    exact hW (weylElement q) x hx

end SymmetricSubgroupAsymptotics.CFSGTrialityBinaryMiddleGeneration
