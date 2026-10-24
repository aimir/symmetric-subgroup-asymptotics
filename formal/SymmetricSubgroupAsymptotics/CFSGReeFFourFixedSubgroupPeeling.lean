import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeeling
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedPositiveSignFactors
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedBruhatCover
import SymmetricSubgroupAsymptotics.CFSGReeFFourFixedAmbientHom

/-! The one-step opposed peel on the SAME original exceptional-fixed
group. Factor existence and opposed disjointness are proved here. The
remaining structural input for a later residual is the actual inversion
block inclusion in that residual. Every inverse is the original group
inverse; no Weyl-action identification substitutes for it. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourFixedSubgroupPeeling
open CFSGOpposedSubgroupPeeling CFSGReeFFourFixedPositiveSignFactors
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGReeFFourFixedPositiveFamilies CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourFixedBruhatCover CFSGReeFFourOriginalWeylWords
open CFSGReeFFourFixedWordClassification CFSGReeFFourPairedModelWords
open CFSGReeFFourOriginalInversionFactors CFSGReeFFourUniqueInversionCells
open CFSGFFourOriginalBruhatCells CFSGReeFFourOriginalNegativeStability
open CFSGFFourOriginalAmbientHom
open CFSGFFourOriginalMiddleWords CFSGReeFFourFixedAmbientHom

private instance fixed_finite (m : ℕ) : Finite (originalModelFixed m) :=
  Finite.of_injective (fixedAmbientHom m) (fixedAmbientHom_injective m)

theorem fixed_positive_negative_disjoint (m : ℕ) :
    Disjoint (fixedPositive m) (fixedNegative m) := by
  apply Subgroup.disjoint_def.mpr
  intro g hg hn
  apply Subtype.ext
  have hb : g.val∈modelEnvelope (Field m) := by
    change rawHom (Field m) g.val∈
      CFSGTwistedE6GeckNormalizerEnvelope.normalizerEnvelope (Field m)
    exact CFSGTwistedE6GeckNormalizerEnvelope.positive_le_envelope (Field m) hg
  have hneg : g.val∈modelNegative m := hn
  exact Subgroup.disjoint_def.mp (modelEnvelope_negative_disjoint m) hb hneg

theorem fixed_sign_factorization (m : ℕ) (s : List Bool)
    (u : originalModelFixed m) (hu : u∈fixedPositive m) :
    ∃ p∈fixedPositive m,
      ∃ b∈inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m s),
        u=p*b ∧ fixedPairedWord m s*p*(fixedPairedWord m s)⁻¹∈fixedPositive m := by
  obtain ⟨p,hp,hpfixed,v,hv,hvfixed,he,hconj⟩ := exists_fixed_positive_sign_factors m
    (expandPaired s) (paired_model_word_fixed m s) u.val hu u.property
  let pf : originalModelFixed m := ⟨p,hpfixed⟩
  let vf : originalModelFixed m := ⟨v,hvfixed⟩
  refine ⟨pf,hp,vf,?_,Subtype.ext he,?_⟩
  · change v∈modelPositive (Field m) ∧
      modelWeylWord (Field m) (expandPaired s)*v*
        (modelWeylWord (Field m) (expandPaired s))⁻¹∈modelNegative m
    exact hv
  · change modelWeylWord (Field m) (expandPaired s)*p*
      (modelWeylWord (Field m) (expandPaired s))⁻¹∈modelPositive (Field m)
    exact hconj

theorem fixed_card_peel (m : ℕ) (s : List Bool)
    (R : Subgroup (originalModelFixed m)) (hRU : R≤fixedPositive m)
    (hBR : inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m s) ≤ R) :
    Nat.card R =
      Nat.card (remainderPart (fixedPositive m) R (fixedPairedWord m s)) *
      Nat.card (inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m s)) :=
  card_eq_remainder_mul_inversion (fixedPositive m) (fixedNegative m) R
    (fixedPairedWord m s) hRU hBR (fixed_positive_negative_disjoint m)
    (fixed_sign_factorization m s)

theorem fixedPositive_card_first_peel (m : ℕ) (s : List Bool) :
    Nat.card (fixedPositive m) =
      Nat.card (remainderPart (fixedPositive m) (fixedPositive m) (fixedPairedWord m s)) *
      Nat.card (inversionPart (fixedPositive m) (fixedNegative m) (fixedPairedWord m s)) :=
  fixed_card_peel m s (fixedPositive m) le_rfl inf_le_left

end SymmetricSubgroupAsymptotics.CFSGReeFFourFixedSubgroupPeeling
