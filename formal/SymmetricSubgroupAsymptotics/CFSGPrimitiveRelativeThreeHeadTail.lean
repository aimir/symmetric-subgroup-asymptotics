import SymmetricSubgroupAsymptotics.CFSGPrimitiveNonaffineTernaryTail
import SymmetricSubgroupAsymptotics.CFSGPrimitiveAffineTernaryTail
import SymmetricSubgroupAsymptotics.PrimitiveSocleRawONanScottProof
import SymmetricSubgroupAsymptotics.FaithfulFiniteActionImage

/-! The actual degree≥34 primitive relative-three-head tail is proved from
raw actual socle structure and sufficient simple-index bounds. This does
not assert or assume the stronger ordinary normal-generator theorem. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics
open PrimitiveSocleRawStructure

theorem c1_primitive_relative_tail_faithful_of_sufficient
    (hindex : SufficientSimpleIndexBounds)
    {A Ω : Type} [Group A] [Finite Ω] [MulAction A Ω]
    [FaithfulSMul A Ω] [MulAction.IsPreprimitive A Ω]
    (hw : 34 ≤ Nat.card Ω) (N : Subgroup A) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3*Nat.card Ω := by
  let e : Ω ≃ Fin (Nat.card Ω) := Finite.equivFin Ω
  letI : Finite A := faithfulLabelledAction_finite e
  letI : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  cases Classical.choice (publishedONanScottStructure A Ω) with
  | inl D => exact D.relativeThreeHead_strict_tail hindex hw N
  | inr P => exact P.relativeThreeHead_strict_tail inferInstance hw N

theorem c1_primitive_relative_tail_of_sufficient
    (hindex : SufficientSimpleIndexBounds)
    (w : ℕ) (hw : 34 ≤ w) (U : Subgroup (Equiv.Perm (Fin w)))
    (hprim : MulAction.IsPreprimitive U (Fin w)) (N : Subgroup U) [N.Normal] :
    20*Module.finrank (ZMod 3) (primeRelativeCharacters 3 N) < 3*w := by
  letI : MulAction.IsPreprimitive U (Fin w) := hprim
  simpa only [Nat.card_fin] using
    c1_primitive_relative_tail_faithful_of_sufficient hindex
      (A := U) (Ω := Fin w) (by simpa using hw) N

end SymmetricSubgroupAsymptotics
