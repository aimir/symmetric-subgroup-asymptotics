import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeAlignment
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalOppositeSylows
import SymmetricSubgroupAsymptotics.CFSGOppositeSylowOfAlignment

/-! Every automorphism of the SAME original simple triality model can
be adjusted by an actual inner automorphism to fix both literal signed
subgroups. Negative Sylow status is a conclusion of the proved opposite
alignment, not a fixed-group recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairAlignment
open CFSGTrialityGeckOriginalOppositeAlignment CFSGTrialityGeckOriginalOppositeSylows
open CFSGTrialityGeckOriginalRootFamily CFSGTrialityGeckDerivedProjectiveImage
open CFSGTrialityGeckFixedPositiveImageSylow CFSGTrialityGeckDerivedSylowNormalizer
local instance (q : CFSG.PrimePower) : Fact q.prime.Prime := ⟨q.prime_isPrime⟩
local instance (q : CFSG.PrimePower) : Finite (DerivedImage q) :=
  Finite.of_surjective (preimageToImage q) (preimageToImage_surjective q)
local instance (q : CFSG.PrimePower) [IsSimpleGroup (CFSG.Models.TrialityD4 q)] :
    Finite (CFSG.Models.TrialityD4 q) :=
  Finite.of_injective (originalProjectiveImageEquiv q) (originalProjectiveImageEquiv q).injective

theorem original_exists_inner_fix_pair (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q)) :
    ∃g : CFSG.Models.TrialityD4 q,
      (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)).map (MulAut.conj g*f).toMonoidHom=
        (originalSylow q : Subgroup (CFSG.Models.TrialityD4 q)) ∧
      (originalNegative q).map (MulAut.conj g*f).toMonoidHom=originalNegative q :=
  CFSGOppositeSylowOfAlignment.exists_inner_fix_pair (originalSylow q) (originalOppositeSylow q)
    (originalNegative q) (original_opposite_sylows_disjoint q)
    (original_opposite_conjugate_by_positive q) f

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairAlignment
