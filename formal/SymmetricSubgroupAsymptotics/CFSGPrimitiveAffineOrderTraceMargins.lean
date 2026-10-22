import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceSmall
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineOrderTraceBinary
import SymmetricSubgroupAsymptotics.PrimitiveAffineNonsolubleSmallNumerics

/-! Exact original nonsoluble half-Schur margins from actual order-charge
budgets. Degree81 has an all-complement full-Schur consumer in a separate
source; no soluble complement cube theorem is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
open Non2UnipotentPrefixFiniteMenu
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    [FaithfulSMul G X] [Nontrivial X]

theorem nonsoluble_margin_of_degree49_order (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (x : X) (he : Nat.card X=49)
    (T : FixedTargetCompositionTrace (P.complement x)) :
    preE7CharacterRho*49 ≤ ((evenWidth 49 : ℝ)-2)/8 -
      (fixedTargetCompositionGamma*T.envelope.abelianLength+P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength (w := 49) (A := 8) T
    (P.complementTrace_abelianLength_le_eight_of_degree49 hp x he T)
  norm_num [preE7CharacterRho,evenWidth,halfDegree]

theorem nonsoluble_margin_of_degree128_order (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (x : X) (he : Nat.card X=128)
    (T : FixedTargetCompositionTrace (P.complement x)) (hn : ¬ IsSolvable (P.complement x)) :
    preE7CharacterRho*128 ≤ ((evenWidth 128 : ℝ)-2)/8 -
      (fixedTargetCompositionGamma*T.envelope.abelianLength+P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength (w := 128) (A := 29) T
    (P.complementTrace_abelianLength_le_twentyNine_of_degree128 hp x he T hn)
  norm_num [preE7CharacterRho,evenWidth,halfDegree]

theorem nonsoluble_margin_of_degree256_order (P : PrimitiveAffineProfile G X)
    (hp : MulAction.IsPreprimitive G X) (x : X) (he : Nat.card X=256)
    (T : FixedTargetCompositionTrace (P.complement x)) :
    preE7CharacterRho*256 ≤ ((evenWidth 256 : ℝ)-2)/8 -
      (fixedTargetCompositionGamma*T.envelope.abelianLength+P.bottomHalfSlope) := by
  apply P.nonsolubleEnvelope_exponent_margin_of_abelianLength (w := 256) (A := 40) T
    (P.complementTrace_abelianLength_le_forty_of_degree256 hp x he T)
  norm_num [preE7CharacterRho,evenWidth,halfDegree]

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile
