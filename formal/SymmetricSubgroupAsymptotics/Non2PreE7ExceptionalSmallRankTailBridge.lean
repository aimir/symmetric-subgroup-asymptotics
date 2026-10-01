import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure
import SymmetricSubgroupAsymptotics.Non2PreE7S3ExceptionalEnvelope
import SymmetricSubgroupAsymptotics.Non2PreE7FiveExceptional

/-!
# S3EXC and fiveExc at the final T1 source boundary

The two exceptional small-family templates construct ordinary numerical
packages directly.  This file places those packages in the concrete owner
sum consumed by the source-or-joint-top exhaustion theorem.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

noncomputable def PreE7S3ExceptionalSource.toRankTailOwnerSource
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7S3ExceptionalSource w i) :
    PreE7RankTailOwnerSourceData w i :=
  .ordinary .s3exc (.completeSource S.numericalData)

noncomputable def PreE7FiveExceptionalSource.toRankTailOwnerSource
    {kind : PreE7FiveExceptionalKind}
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7FiveExceptionalSource kind w i) :
    PreE7RankTailOwnerSourceData w i :=
  .ordinary .fiveExc (.package S.numericalPackage)

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
