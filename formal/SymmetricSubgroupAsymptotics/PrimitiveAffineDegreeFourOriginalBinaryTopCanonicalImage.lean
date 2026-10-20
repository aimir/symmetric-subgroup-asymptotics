import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourOriginalBinaryTopRange

/-! The actual original top module, its actual canonical normal image,
and its conjugation-compatible injective group coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]
local instance originalBinaryTopCanonicalImagePrime : Fact P.p.Prime := ⟨P.p_prime⟩

abbrev DegreeFourOriginalBinaryTopVector
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ.asModule ⧸
    (DegreeFourFullBinaryTargetSection block P N).toSubmodule

def degreeFourOriginalBinaryTopRepresentation
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Representation (ZMod P.p) (preE7NonPairAction w U)
      (DegreeFourOriginalBinaryTopVector block P N) :=
  (((DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ).quotient
    (DegreeFourFullBinaryTargetSection block P N).toSubmodule
    (fun g => (DegreeFourFullBinaryTargetSection block P N).apply_mem_toSubmodule g)).comp
      (degreeFourFullBinarySocleTopMap block P N)

variable {C : Type} [Group C]
  (e : DegreeFourComplementQuotient block P ≃* C)

def degreeFourCanonicalNormalImage
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) : Subgroup C :=
  (N.1.map (QuotientGroup.mk' (E block P))).map e.toMonoidHom

instance degreeFourCanonicalNormalImage_normal
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (degreeFourCanonicalNormalImage block P e N).Normal := by
  apply Subgroup.Normal.map
    (Subgroup.Normal.map N.2 _ (QuotientGroup.mk'_surjective (E block P)))
    _ e.surjective

def degreeFourCanonicalOriginalMap : preE7NonPairAction w U →* C :=
  e.toMonoidHom.comp (QuotientGroup.mk' (E block P))

def degreeFourOriginalBinaryTopCanonicalInjection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Multiplicative (DegreeFourOriginalBinaryTopVector block P N) →*
      C ⧸ degreeFourCanonicalNormalImage block P e N :=
  (OriginalRetainedTopQuotientEquiv.retainedTopEquiv (E block P) N.1 e).toMonoidHom.comp
    (degreeFourFullBinaryTopInjection block P N)

theorem degreeFourOriginalBinaryTopCanonicalInjection_injective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Injective (degreeFourOriginalBinaryTopCanonicalInjection block P e N) :=
  (OriginalRetainedTopQuotientEquiv.retainedTopEquiv (E block P) N.1 e).injective.comp
    (degreeFourFullBinaryTopInjection_injective block P N)

instance degreeFourOriginalBinaryTopCanonicalInjection_range_normal
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (degreeFourOriginalBinaryTopCanonicalInjection block P e N).range.Normal := by
  unfold degreeFourOriginalBinaryTopCanonicalInjection
  rw [MonoidHom.range_comp]
  exact Subgroup.Normal.map inferInstance _
    (OriginalRetainedTopQuotientEquiv.retainedTopEquiv (E block P) N.1 e).surjective

theorem degreeFourOriginalBinaryTopCanonicalInjection_range_isPGroup
    (hr : Nat.card block.Fibre = 4)
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    IsPGroup 2 (degreeFourOriginalBinaryTopCanonicalInjection block P e N).range := by
  unfold degreeFourOriginalBinaryTopCanonicalInjection
  rw [MonoidHom.range_comp]
  exact (degreeFourFullBinaryTopInjection_range_isPGroup block P hr N).map _

theorem degreeFourOriginalBinaryTopCanonicalInjection_conjugate
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U) (v : DegreeFourOriginalBinaryTopVector block P N) :
    degreeFourOriginalBinaryTopCanonicalInjection block P e N
        (Multiplicative.ofAdd (degreeFourOriginalBinaryTopRepresentation block P N g v)) =
      QuotientGroup.mk' (degreeFourCanonicalNormalImage block P e N)
          (degreeFourCanonicalOriginalMap block P e g) *
        degreeFourOriginalBinaryTopCanonicalInjection block P e N (Multiplicative.ofAdd v) *
      (QuotientGroup.mk' (degreeFourCanonicalNormalImage block P e N)
          (degreeFourCanonicalOriginalMap block P e g))⁻¹ := by
  let T := DegreeFourFullBinaryTargetSection block P N
  obtain ⟨x,rfl⟩ := T.toSubmodule.mkQ_surjective v
  let F := OriginalRetainedTopQuotientEquiv.retainedTopEquiv (E block P) N.1 e
  have h := congrArg F
    (degreeFourFullBinaryTopInjection_conjugate_mk block P N (QuotientGroup.mk' N.1 g) x)
  simpa only [degreeFourOriginalBinaryTopCanonicalInjection,
    degreeFourOriginalBinaryTopRepresentation,
    Representation.quotient,Submodule.mapQ_apply,
    MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,map_mul,map_inv,
    OriginalRetainedTopQuotientEquiv.retainedTopEquiv_mk,
    degreeFourCanonicalOriginalMap,degreeFourCanonicalNormalImage] using h

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
