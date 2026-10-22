import SymmetricSubgroupAsymptotics.CFSGTwistedDSubgroupSylowNormalizer
import SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedImageQuotient
import SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerSurjective

/-! The SAME original twisted-D Derived action image has an actual
defining-characteristic Sylow with soluble normalizer. This does not yet
claim two-conjugate Sylow generation or identify the whole fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedSylowNormalizer
open CFSGTwistedDDerivedPairedRoots CFSGTwistedDDerivedImageQuotient

theorem exists_preimage_sylow_soluble_normalizer (s : ℕ) (q : CFSG.PrimePower) :
    ∃ P : Sylow q.prime (naturalDerivedPreimage s q),
      IsSolvable (Subgroup.normalizer (P : Set (naturalDerivedPreimage s q))) :=
  CFSGTwistedDSubgroupSylowNormalizer.exists_sylow_soluble_normalizer
    (q.Extension 2) s q.prime (naturalDerivedPreimage s q)
    (test_mem_derived_preimage s q)

theorem exists_image_sylow_soluble_normalizer (s : ℕ) (q : CFSG.PrimePower) :
    ∃ P : Sylow q.prime (derivedImageAction s q).range,
      IsSolvable (Subgroup.normalizer (P : Set (derivedImageAction s q).range)) :=
  CFSGSolubleSylowNormalizerSurjective.exists_sylow_soluble_normalizer_map
    (preimageToImage s q) (preimageToImage_surjective s q)
    (exists_preimage_sylow_soluble_normalizer s q)

end SymmetricSubgroupAsymptotics.CFSGTwistedDDerivedSylowNormalizer
