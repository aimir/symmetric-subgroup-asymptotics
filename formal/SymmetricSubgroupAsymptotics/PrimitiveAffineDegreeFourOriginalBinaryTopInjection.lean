import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreFullBinarySection

/-! Named exact top injection, extracted from the checked dimension proof.
Its source is the ACTUAL socle modulo its ACTUAL translation intersection;
no normal denominator or quotient is replaced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
variable {w : ℕ} {U : PreE7NonPairActionClass w} {basePoint : Fin w}
  (block : OriginalMinimalBlock (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre) [Nontrivial block.Fibre]

noncomputable def degreeFourFullBinaryTopInjectionData
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    {f : Multiplicative
      ((DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ.asModule ⧸
        (DegreeFourFullBinaryTargetSection block P N).toSubmodule) →*
      DegreeFourRetainedQuotient N ⧸ degreeFourTranslationImage block P N // Function.Injective f ∧
        ∀ v : (DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ.asModule,
          f (Multiplicative.ofAdd ((DegreeFourFullBinaryTargetSection block P N).toSubmodule.mkQ v)) =
            QuotientGroup.mk' (degreeFourTranslationImage block P N)
              ((DegreeFourFullBinarySocleChart block P N).equiv.symm (Multiplicative.ofAdd v)).1} := by
  let Q := DegreeFourRetainedQuotient N
  let A := DegreeFourFullBinarySocle block P N
  let C := DegreeFourFullBinarySocleChart block P N
  let sigma := C.quotientRepresentation.ρ
  let H := DegreeFourFullBinaryTranslationIntersection block P N
  let T := DegreeFourFullBinaryTargetSection block P N
  let Vbar := degreeFourTranslationImage block P N
  letI : Fact C.p.Prime := C.primeFact
  letI : FiniteDimensional (ZMod C.p) C.quotientRepresentation :=
    C.finiteDimensional
  letI : Module (ZMod C.p)[Q ⧸ A] sigma.asModule :=
    Representation.instModuleMonoidAlgebraAsModule sigma
  letI : IsScalarTower (ZMod C.p) (ZMod C.p)[Q ⧸ A] sigma.asModule :=
    inferInstanceAs
      (IsScalarTower (ZMod C.p) (ZMod C.p)[Q ⧸ A]
        (Representation.asModule sigma))
  let proj : Multiplicative sigma.asModule →*
      Multiplicative (sigma.asModule ⧸ T.toSubmodule) :=
    T.toSubmodule.mkQ.toAddMonoidHom.toMultiplicative
  have hproj : Function.Surjective proj := by
    intro z
    obtain ⟨v, hv⟩ := T.toSubmodule.mkQ_surjective z.toAdd
    exact ⟨Multiplicative.ofAdd v, congrArg Multiplicative.ofAdd hv⟩
  let topMap : Q →* Q ⧸ Vbar := QuotientGroup.mk' Vbar
  let f : Multiplicative sigma.asModule →* Q ⧸ Vbar :=
    topMap.comp (A.subtype.comp C.equiv.symm.toMonoidHom)
  have hker : proj.ker = f.ker := by
    ext v
    change T.toSubmodule.mkQ v.toAdd = 0 ↔
      QuotientGroup.mk' Vbar (C.equiv.symm v).1 = 1
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    let a : A := C.equiv.symm v
    have ha : C.equiv a = v := C.equiv.apply_symm_apply v
    have hmem := elementaryIntersectionModule_mem_iff A C H a
    rw [ha] at hmem
    have hq := QuotientGroup.eq_one_iff (N := Vbar) (a.1 : Q)
    exact (hmem.trans (and_iff_right a.2)).trans hq.symm
  have hkerRange : proj.ker = f.rangeRestrict.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using hker
  let e : Multiplicative (sigma.asModule ⧸ T.toSubmodule) ≃* f.range :=
    (QuotientGroup.liftEquiv proj.ker hproj rfl).symm.trans
      (QuotientGroup.liftEquiv proj.ker
        f.rangeRestrict_surjective hkerRange)
  let embedding : Multiplicative (sigma.asModule ⧸ T.toSubmodule) →*
      Q ⧸ Vbar := f.range.subtype.comp e.toMonoidHom
  have hembedding : Function.Injective embedding :=
    Subtype.val_injective.comp e.injective
  have heval (v : Multiplicative sigma.asModule) : embedding (proj v) = f v := by
    change ((QuotientGroup.liftEquiv proj.ker f.rangeRestrict_surjective hkerRange)
      ((QuotientGroup.liftEquiv proj.ker hproj rfl).symm (proj v))).1 = f v
    exact congrArg
      (fun z : Multiplicative sigma.asModule ⧸ proj.ker =>
        ((QuotientGroup.liftEquiv proj.ker f.rangeRestrict_surjective hkerRange) z).1)
      ((QuotientGroup.liftEquiv proj.ker hproj rfl).symm_apply_apply
        (QuotientGroup.mk' proj.ker v))
  exact ⟨embedding,hembedding,fun v => heval (Multiplicative.ofAdd v)⟩

noncomputable def degreeFourFullBinaryTopInjection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (degreeFourFullBinaryTopInjectionData block P N).1

theorem degreeFourFullBinaryTopInjection_injective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Injective (degreeFourFullBinaryTopInjection block P N) :=
  (degreeFourFullBinaryTopInjectionData block P N).2.1

theorem degreeFourFullBinaryTopInjection_mk
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (v : (DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ.asModule) :
    degreeFourFullBinaryTopInjection block P N
        (Multiplicative.ofAdd ((DegreeFourFullBinaryTargetSection block P N).toSubmodule.mkQ v)) =
      QuotientGroup.mk' (degreeFourTranslationImage block P N)
        ((DegreeFourFullBinarySocleChart block P N).equiv.symm (Multiplicative.ofAdd v)).1 :=
  (degreeFourFullBinaryTopInjectionData block P N).2.2 v

/-- Equivariance on the actual quotient representatives, under ORIGINAL
retained-quotient conjugation. These representatives cover the full source. -/
theorem degreeFourFullBinaryTopInjection_conjugate_mk
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : DegreeFourRetainedQuotient N)
    (v : (DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ.asModule) :
    degreeFourFullBinaryTopInjection block P N
      (Multiplicative.ofAdd ((DegreeFourFullBinaryTargetSection block P N).toSubmodule.mkQ
        ((DegreeFourFullBinarySocleChart block P N).quotientRepresentation.ρ
          (QuotientGroup.mk' (DegreeFourFullBinarySocle block P N) g) v))) =
    QuotientGroup.mk' (degreeFourTranslationImage block P N) g *
      degreeFourFullBinaryTopInjection block P N
        (Multiplicative.ofAdd ((DegreeFourFullBinaryTargetSection block P N).toSubmodule.mkQ v)) *
      (QuotientGroup.mk' (degreeFourTranslationImage block P N) g)⁻¹ := by
  rw [degreeFourFullBinaryTopInjection_mk,degreeFourFullBinaryTopInjection_mk]
  let C := DegreeFourFullBinarySocleChart block P N
  let q := QuotientGroup.mk' (degreeFourTranslationImage block P N)
  have h := C.quotientRepresentation_apply g (C.equiv.symm (Multiplicative.ofAdd v))
  have hh := congrArg (fun z : C.V => q ((C.equiv.symm (Multiplicative.ofAdd z)).1)) h
  simpa only [MulEquiv.apply_symm_apply,MulEquiv.symm_apply_apply,map_mul,map_inv] using hh

end Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
end SymmetricSubgroupAsymptotics
end
