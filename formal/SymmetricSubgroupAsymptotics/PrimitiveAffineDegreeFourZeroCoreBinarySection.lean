import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreNonbinarySocle
import SymmetricSubgroupAsymptotics.PrimeSocleSemisimple
import SymmetricSubgroupAsymptotics.PrimitiveAffineFixedFrameRelativeHead
import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity

/-!
# The literal translation section of the noncentral binary socle

For a retained quotient `Q = U/N`, intersect the noncentral binary socle
with the actual image of the correlated translation group.  Pulling this
intersection back to the original translation group gives an invariant
subrepresentation of the original correlated module.  The quotient map
induces a literal surjective intertwiner from that subrepresentation onto
the selected socle intersection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance degreeFourBinarySection_profilePrimeFact : Fact P.p.Prime :=
  ⟨P.p_prime⟩

abbrev DegreeFourBinarySocle
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  noncentralPrimeSoclePart P.p (DegreeFourRetainedQuotient N)

noncomputable abbrev DegreeFourBinarySocleChart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  selectedPrimeSoclePartElementaryChart P.p
    (fun M : Subgroup (DegreeFourRetainedQuotient N) ↦
      ¬ M ≤ Subgroup.center (DegreeFourRetainedQuotient N))

abbrev DegreeFourBinaryTranslationIntersection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  DegreeFourBinarySocle block P N ⊓ degreeFourTranslationImage block P N

abbrev DegreeFourBinaryTranslationPreimage
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (DegreeFourBinaryTranslationIntersection block P N).comap
      (QuotientGroup.mk' N.1) ⊓ E block P

noncomputable abbrev DegreeFourBinarySourceSection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (elementaryChart block P).originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (DegreeFourBinaryTranslationPreimage block P N)

noncomputable abbrev DegreeFourBinaryTargetSection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (DegreeFourBinarySocleChart block P N).originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' (DegreeFourBinarySocle block P N))
    (QuotientGroup.mk'_surjective (DegreeFourBinarySocle block P N))
    (DegreeFourBinarySocleChart block P N).quotientRepresentation
    (DegreeFourBinaryTranslationIntersection block P N)

noncomputable abbrev DegreeFourBinarySourceSectionInflated
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  ActualWreathAffineCapacity.subrepresentationComp
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation.ρ
    (DegreeFourBinarySourceSection block P N)

def degreeFourBinarySocleTopMap
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    preE7NonPairAction w U →*
      DegreeFourRetainedQuotient N ⧸ DegreeFourBinarySocle block P N :=
  (QuotientGroup.mk' (DegreeFourBinarySocle block P N)).comp
    (QuotientGroup.mk' N.1)

/-- The literal quotient homomorphism between the two actual elementary
intersections.  Keeping it multiplicative makes zero, addition, and the
ambient conjugation law consequences of the two elementary charts. -/
def degreeFourBinaryTranslationIntersectionHom
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    ↑(DegreeFourBinaryTranslationPreimage block P N ⊓ E block P) →*
      ↑(DegreeFourBinaryTranslationIntersection block P N ⊓
        DegreeFourBinarySocle block P N) where
  toFun x := ⟨QuotientGroup.mk' N.1 x.1, x.2.1.1, x.2.1.1.1⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (QuotientGroup.mk' N.1)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (QuotientGroup.mk' N.1) x.1 y.1

/-- Source intersection in its stored elementary-module coordinates. -/
noncomputable def degreeFourBinarySourceIntersectionEquiv
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  elementaryIntersectionMulEquiv
    (E block P) (elementaryChart block P)
    (DegreeFourBinaryTranslationPreimage block P N)

/-- Target intersection in its stored elementary-module coordinates. -/
noncomputable def degreeFourBinaryTargetIntersectionEquiv
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  elementaryIntersectionMulEquiv
    (DegreeFourBinarySocle block P N)
    (DegreeFourBinarySocleChart block P N)
    (DegreeFourBinaryTranslationIntersection block P N)

/-- In elementary module coordinates, the literal intersection map is a
multiplicative homomorphism. -/
def degreeFourBinaryTranslationSectionMulHom
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Multiplicative
        (DegreeFourBinarySourceSection block P N).toSubmodule →*
      Multiplicative
        (DegreeFourBinaryTargetSection block P N).toSubmodule :=
  (degreeFourBinaryTargetIntersectionEquiv block P N).toMonoidHom.comp
    ((degreeFourBinaryTranslationIntersectionHom block P N).comp
      (degreeFourBinarySourceIntersectionEquiv block P N).symm.toMonoidHom)

/-- Literal additive quotient map between the two elementary intersection
modules. -/
def degreeFourBinaryTranslationSectionAddHom
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourBinarySourceSection block P N).toSubmodule →+
      (DegreeFourBinaryTargetSection block P N).toSubmodule :=
  AddMonoidHom.toMultiplicative.symm
    (degreeFourBinaryTranslationSectionMulHom block P N)

/-- Linear form of the literal quotient map. -/
def degreeFourBinaryTranslationSectionLinearMap
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourBinarySourceSection block P N).toSubmodule →ₗ[ZMod P.p]
      (DegreeFourBinaryTargetSection block P N).toSubmodule :=
  (degreeFourBinaryTranslationSectionAddHom block P N).toZModLinearMap P.p

omit [Nontrivial block.Fibre] in
/-- The literal group homomorphism onto the selected translation
intersection is surjective. -/
theorem degreeFourBinaryTranslationIntersectionHom_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective
      (degreeFourBinaryTranslationIntersectionHom block P N) := by
  let A := DegreeFourBinarySocle block P N
  let H := DegreeFourBinaryTranslationIntersection block P N
  let L := DegreeFourBinaryTranslationPreimage block P N
  let q := QuotientGroup.mk' N.1
  intro y
  obtain ⟨e, heE, he⟩ := y.2.1.2
  have heH : q e ∈ H := by
    rw [he]
    exact y.2.1
  let x : ↑(L ⊓ E block P) := ⟨e, ⟨⟨heH, heE⟩, heE⟩⟩
  refine ⟨x, Subtype.ext ?_⟩
  exact he

/-- Surjectivity survives the two elementary coordinate equivalences. -/
theorem degreeFourBinaryTranslationSectionMulHom_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective
      (degreeFourBinaryTranslationSectionMulHom block P N) := by
  simpa only [degreeFourBinaryTranslationSectionMulHom,
    MonoidHom.coe_comp, Function.comp_apply] using
    (degreeFourBinaryTargetIntersectionEquiv block P N).surjective.comp
      ((degreeFourBinaryTranslationIntersectionHom_surjective block P N).comp
        (degreeFourBinarySourceIntersectionEquiv block P N).symm.surjective)

private theorem additive_surjective_of_multiplicative_surjective
    {V W : Type} [AddMonoid V] [AddMonoid W]
    (f : Multiplicative V →* Multiplicative W)
    (hf : Function.Surjective f) :
    Function.Surjective (AddMonoidHom.toMultiplicative.symm f) := by
  intro w
  obtain ⟨v, hv⟩ := hf (Multiplicative.ofAdd w)
  refine ⟨v.toAdd, ?_⟩
  apply Multiplicative.ofAdd.injective
  simpa only [ofAdd_toAdd] using hv

/-- The original quotient map sees every vector in the selected socle
intersection. -/
theorem degreeFourBinaryTranslationSectionLinearMap_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective
      (degreeFourBinaryTranslationSectionLinearMap block P N) := by
  exact additive_surjective_of_multiplicative_surjective
    (degreeFourBinaryTranslationSectionMulHom block P N)
    (degreeFourBinaryTranslationSectionMulHom_surjective block P N)

omit [Nontrivial block.Fibre] in
/-- The literal intersection homomorphism commutes with ambient
conjugation. -/
theorem degreeFourBinaryTranslationIntersectionHom_conj
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (x : ↑(DegreeFourBinaryTranslationPreimage block P N ⊓ E block P)) :
    degreeFourBinaryTranslationIntersectionHom block P N
        (MulAut.conjNormal g x) =
      MulAut.conjNormal (QuotientGroup.mk' N.1 g)
        (degreeFourBinaryTranslationIntersectionHom block P N x) := by
  apply Subtype.ext
  change QuotientGroup.mk' N.1 (g * x.1 * g⁻¹) =
    QuotientGroup.mk' N.1 g * QuotientGroup.mk' N.1 x.1 *
      (QuotientGroup.mk' N.1 g)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- The source elementary equivalence identifies ambient conjugation with
the inflated source action. -/
theorem degreeFourBinarySourceIntersectionEquiv_action
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (v : Multiplicative
      (DegreeFourBinarySourceSection block P N).toSubmodule) :
    Multiplicative.ofAdd
        ((DegreeFourBinarySourceSectionInflated block P N).toRepresentation
          g v.toAdd) =
      degreeFourBinarySourceIntersectionEquiv block P N
        (MulAut.conjNormal g
          ((degreeFourBinarySourceIntersectionEquiv block P N).symm v)) := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  let C := elementaryChart block P
  let e : E block P := C.equiv.symm (Multiplicative.ofAdd v.toAdd.1)
  have he : (C.equiv e).toAdd = v.toAdd.1 := by
    exact congrArg Multiplicative.toAdd
      (C.equiv.apply_symm_apply (Multiplicative.ofAdd v.toAdd.1))
  change C.quotientRepresentation.ρ
      (QuotientGroup.mk' (E block P) g) v.toAdd.1 =
    (C.equiv (MulAut.conjNormal g e)).toAdd
  rw [← he]
  exact C.quotientRepresentation_apply g e

omit [Nontrivial block.Fibre] in
/-- The target elementary equivalence identifies quotient conjugation with
the retained target action. -/
theorem degreeFourBinaryTargetIntersectionEquiv_action
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (y : ↑(DegreeFourBinaryTranslationIntersection block P N ⊓
      DegreeFourBinarySocle block P N)) :
    degreeFourBinaryTargetIntersectionEquiv block P N
        (MulAut.conjNormal (QuotientGroup.mk' N.1 g) y) =
      Multiplicative.ofAdd
        ((DegreeFourBinaryTargetSection block P N).toRepresentation
          (degreeFourBinarySocleTopMap block P N g)
          (degreeFourBinaryTargetIntersectionEquiv block P N y).toAdd) := by
  simpa only [degreeFourBinaryTargetIntersectionEquiv,
    degreeFourBinarySocleTopMap, MonoidHom.coe_comp,
    Function.comp_apply] using
    elementaryIntersectionMulEquiv_equivariant
      (DegreeFourBinarySocle block P N)
      (DegreeFourBinarySocleChart block P N)
      (DegreeFourBinaryTranslationIntersection block P N)
      (QuotientGroup.mk' N.1 g) y

/-- Pointwise multiplicative equivariance.  This is stated before the linear
packaging so elaboration never unfolds the full retained-section expression
inside an `IntertwiningMap` field. -/
theorem degreeFourBinaryTranslationSectionMulHom_equivariant
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (v : Multiplicative
      (DegreeFourBinarySourceSection block P N).toSubmodule) :
    degreeFourBinaryTranslationSectionMulHom block P N
        (Multiplicative.ofAdd
          ((DegreeFourBinarySourceSectionInflated block P N).toRepresentation
            g v.toAdd)) =
      Multiplicative.ofAdd
        ((DegreeFourBinaryTargetSection block P N).toRepresentation
          (degreeFourBinarySocleTopMap block P N g)
          (degreeFourBinaryTranslationSectionMulHom block P N v).toAdd) := by
  let sourceEquiv := degreeFourBinarySourceIntersectionEquiv block P N
  let targetEquiv := degreeFourBinaryTargetIntersectionEquiv block P N
  let x := sourceEquiv.symm v
  have hsource : Multiplicative.ofAdd
      ((DegreeFourBinarySourceSectionInflated block P N).toRepresentation
        g v.toAdd) = sourceEquiv (MulAut.conjNormal g x) := by
    exact degreeFourBinarySourceIntersectionEquiv_action block P N g v
  have hsourceInv : sourceEquiv.symm (Multiplicative.ofAdd
      ((DegreeFourBinarySourceSectionInflated block P N).toRepresentation
        g v.toAdd)) = MulAut.conjNormal g x := by
    have h := congrArg sourceEquiv.symm hsource
    simpa only [sourceEquiv.symm_apply_apply] using h
  have htarget : targetEquiv
      (MulAut.conjNormal (QuotientGroup.mk' N.1 g)
        (degreeFourBinaryTranslationIntersectionHom block P N x)) =
      Multiplicative.ofAdd
        ((DegreeFourBinaryTargetSection block P N).toRepresentation
          (degreeFourBinarySocleTopMap block P N g)
          (targetEquiv
            (degreeFourBinaryTranslationIntersectionHom block P N x)).toAdd) := by
    exact degreeFourBinaryTargetIntersectionEquiv_action block P N g _
  change targetEquiv
      (degreeFourBinaryTranslationIntersectionHom block P N
        (sourceEquiv.symm (Multiplicative.ofAdd
          ((DegreeFourBinarySourceSectionInflated block P N).toRepresentation
            g v.toAdd)))) = _
  calc
    _ = targetEquiv
        (degreeFourBinaryTranslationIntersectionHom block P N
          (MulAut.conjNormal g x)) :=
      congrArg targetEquiv
        (congrArg (degreeFourBinaryTranslationIntersectionHom block P N)
          hsourceInv)
    _ = targetEquiv
        (MulAut.conjNormal (QuotientGroup.mk' N.1 g)
          (degreeFourBinaryTranslationIntersectionHom block P N x)) :=
      congrArg targetEquiv
        (degreeFourBinaryTranslationIntersectionHom_conj block P N g x)
    _ = _ := htarget

/-- The section map respects the original conjugation action. -/
theorem degreeFourBinaryTranslationSectionLinearMap_equivariant
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (v : (DegreeFourBinarySourceSection block P N).toSubmodule) :
    degreeFourBinaryTranslationSectionLinearMap block P N
      ((DegreeFourBinarySourceSectionInflated block P N).toRepresentation g v) =
    (DegreeFourBinaryTargetSection block P N).toRepresentation
      (degreeFourBinarySocleTopMap block P N g)
      (degreeFourBinaryTranslationSectionLinearMap block P N v) := by
  apply Multiplicative.ofAdd.injective
  exact degreeFourBinaryTranslationSectionMulHom_equivariant
    block P N g (Multiplicative.ofAdd v)

/-- Intertwining-map form used by the exceptional scalar Schur rows. -/
def degreeFourBinaryTranslationSectionIntertwiner
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourBinarySourceSectionInflated block P N).toRepresentation
      |>.IntertwiningMap
        ((DegreeFourBinaryTargetSection block P N).toRepresentation.comp
          (degreeFourBinarySocleTopMap block P N)) where
  toLinearMap := degreeFourBinaryTranslationSectionLinearMap block P N
  isIntertwining' g := by
    apply LinearMap.ext
    exact degreeFourBinaryTranslationSectionLinearMap_equivariant block P N g

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
