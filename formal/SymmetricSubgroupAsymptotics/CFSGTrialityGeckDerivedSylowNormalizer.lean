import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedDerivedMatrixLift
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedPositiveSylow
import SymmetricSubgroupAsymptotics.CFSGSylowIntermediateNormalizer
import SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerSurjective

/-! The SAME original triality Derived action range has an actual
defining-characteristic Sylow with soluble normalizer. Its matrix
preimage lies in the genuine fixed matrix group, contains the whole
fixed positive Sylow, and surjects by the proved central fixed lift.
Two-conjugate-Sylow generation is a separate requirement. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedSylowNormalizer
open CFSGTrialityGeckFixedDerivedMatrixLift CFSGTrialityGeckFixedPositiveSylow
open CFSGTrialityGeckSourceWordAction CFSGTrialityGeckMatrixGroupTwist
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckMatrixTwist
open CFSGTrialityGeckLongDerivedImage CFSGTrialityGeckFixedPositiveDerivedImage
open CFSGSerreOrdinaryTwists

private theorem comap_restriction_surjective {G H : Type*} [Group G] [Group H]
    (f : G →* H) (R : Subgroup H) (hR : R ≤ f.range) :
    Function.Surjective (f.subgroupComap R) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := hR hy
  have hxR : x ∈ R.comap f := by
    change f x ∈ R
    rw [hx]
    exact hy
  exact ⟨⟨x, hxR⟩, Subtype.ext hx⟩

def naturalDerivedPreimage (q : CFSG.PrimePower) : Subgroup (FixedMatrixGroup q) :=
  (derivedImageAction q).range.comap (fixedMatrixAction q)

theorem fixed_upper_le_preimage (q : CFSG.PrimePower) :
    FixedUpper (q.Extension 3) (definingFieldAutomorphism q 3) ≤ naturalDerivedPreimage q := by
  intro u hu
  let v : Positive (q.Extension 3) := ⟨u.val.val, hu⟩
  have hv : positiveTwist (q.Extension 3) (definingFieldAutomorphism q 3) v = v := by
    apply Subtype.ext
    have hh := congrArg (fun g : MatrixGroup (q.Extension 3) => g.val) u.property
    dsimp only at hh
    change unitTwist (q.Extension 3) (definingFieldAutomorphism q 3) u.val.val = u.val.val at hh
    exact hh
  have hy := fixed_positive_action_mem_derived_range q v hv
  change fixedMatrixAction q u ∈ (derivedImageAction q).range
  exact hy

def preimageToImage (q : CFSG.PrimePower) :
    naturalDerivedPreimage q →* (derivedImageAction q).range :=
  (fixedMatrixAction q).subgroupComap (derivedImageAction q).range

theorem preimageToImage_val (q : CFSG.PrimePower) (g : naturalDerivedPreimage q) :
    (preimageToImage q g).val = fixedMatrixAction q g.val := rfl

theorem preimageToImage_surjective (q : CFSG.PrimePower) :
    Function.Surjective (preimageToImage q) :=
  comap_restriction_surjective (fixedMatrixAction q) (derivedImageAction q).range
    (derived_action_range_le_fixed_matrix_action q)

def preimageSylow (q : CFSG.PrimePower) : Sylow q.prime (naturalDerivedPreimage q) :=
  (fixedPositiveSylow (q.Extension 3) (definingFieldAutomorphism q 3) q.prime).subtype (by
    rw [fixedPositiveSylow_subgroup]
    exact fixed_upper_le_preimage q)

theorem preimage_sylow_normalizer_soluble (q : CFSG.PrimePower) :
    IsSolvable (Subgroup.normalizer (preimageSylow q : Set (naturalDerivedPreimage q))) := by
  have hPR : (fixedPositiveSylow (q.Extension 3) (definingFieldAutomorphism q 3) q.prime :
      Subgroup (FixedMatrixGroup q)) ≤ naturalDerivedPreimage q := by
    rw [fixedPositiveSylow_subgroup]
    exact fixed_upper_le_preimage q
  exact CFSGSylowIntermediateNormalizer.normalizer_soluble_subtype
    (fixedPositiveSylow (q.Extension 3) (definingFieldAutomorphism q 3) q.prime)
    (naturalDerivedPreimage q) hPR (by
      change IsSolvable (Subgroup.normalizer
        (FixedUpper (q.Extension 3) (definingFieldAutomorphism q 3) : Set (FixedMatrixGroup q)))
      exact fixed_upper_normalizer_soluble (q.Extension 3) (definingFieldAutomorphism q 3) q.prime)

theorem exists_image_sylow_soluble_normalizer (q : CFSG.PrimePower) :
    ∃ P : Sylow q.prime (derivedImageAction q).range,
      IsSolvable (Subgroup.normalizer (P : Set (derivedImageAction q).range)) :=
  CFSGSolubleSylowNormalizerSurjective.exists_sylow_soluble_normalizer_map
    (preimageToImage q) (preimageToImage_surjective q)
    ⟨preimageSylow q, preimage_sylow_normalizer_soluble q⟩

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckDerivedSylowNormalizer
