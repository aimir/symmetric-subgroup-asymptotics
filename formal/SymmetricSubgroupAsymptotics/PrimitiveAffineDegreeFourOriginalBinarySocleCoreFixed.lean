import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalKleinCore
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFullBinarySection
import SymmetricSubgroupAsymptotics.NormalPSubgroupSemisimpleFixed

/-! Every original normal binary subgroup fixes the actual binary socle
of every original retained quotient. In particular the literal preimage
of canonical Klein acts trivially on the original intersection target. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
    (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
    (P : PrimitiveAffineProfile block.Component block.Fibre)
    [Nontrivial block.Fibre]

local instance primitiveAffineDegreeFourOriginalBinarySocleCoreFixed_localFact1 : Fact P.p.Prime := ⟨P.p_prime⟩

theorem degreeFourFullBinarySocle_original_normal_binary_fixed
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (K : Subgroup (preE7NonPairAction w U)) [K.Normal] (hK : IsPGroup 2 K)
    (g : K) (v : (DegreeFourFullBinarySocleChart block P N).V) :
    (DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ
      (degreeFourFullBinarySocleTopMap block P N g.1) v = v := by
  let Q := DegreeFourRetainedQuotient N
  let A := DegreeFourFullBinarySocle block P N
  let C := DegreeFourFullBinarySocleChart block P N
  letI : Module (ZMod P.p) C.V := C.module
  let sigma : Representation (ZMod P.p) (Q ⧸ A) C.V := C.quotientRepresentation.ρ
  let t := degreeFourFullBinarySocleTopMap block P N
  have ht : Function.Surjective t :=
    (QuotientGroup.mk'_surjective A).comp (QuotientGroup.mk'_surjective N.1)
  let H := K.map t
  letI : H.Normal := Subgroup.Normal.map inferInstance t ht
  have hH : IsPGroup P.p H := by
    exact (congrArg (fun p : ℕ => IsPGroup p H)
      (degreeFour_profilePrime_eq_two block P hr).symm).mp (hK.map t)
  letI : FiniteDimensional (ZMod P.p) C.V := C.finiteDimensional
  letI : Finite C.V := Module.finite_of_finite (ZMod P.p)
  letI : IsSemisimpleModule (ZMod P.p)[Q ⧸ A] sigma.asModule := by
    exact selectedPrimeSoclePart_quotientRepresentation_isSemisimple
      P.p (G := Q) (fun _ => True)
  have hg : t g.1 ∈ H := ⟨g.1, g.2, rfl⟩
  exact normal_pSubgroup_semisimple_representation_fixed sigma H hH ⟨t g.1, hg⟩ v

/-- The same actual normal binary subgroup fixes the literal translation
intersection target, on its unchanged original vector space. -/
theorem degreeFourFullBinaryTargetSection_original_normal_binary_fixed
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (K : Subgroup (preE7NonPairAction w U)) [K.Normal] (hK : IsPGroup 2 K)
    (g : K) (v : (DegreeFourFullBinaryTargetSection block P N).toSubmodule) :
    (DegreeFourFullBinaryTargetSection block P N).toRepresentation
      (degreeFourFullBinarySocleTopMap block P N g.1) v = v := by
  apply Subtype.ext
  exact degreeFourFullBinarySocle_original_normal_binary_fixed block P hr N K hK g v.1

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics

end
