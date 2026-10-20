import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeFourZeroCoreNonbinarySocle
import SymmetricSubgroupAsymptotics.PrimeSocleSemisimple
import SymmetricSubgroupAsymptotics.PrimitiveAffineFixedFrameRelativeHead
import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacity

/-!
# The literal translation section of any selected binary socle

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

local instance degreeFourSelectedBinarySection_profilePrimeFact : Fact P.p.Prime :=
  ⟨P.p_prime⟩

variable (select : ∀ N : DegreeFourLiteralNormalAxis (w := w) (U := U),
  Subgroup (DegreeFourRetainedQuotient N) → Prop)

abbrev DegreeFourSelectedBinarySocle
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  minimalNormalSoclePart (DegreeFourRetainedQuotient N)
    (fun M => select N M ∧ IsPGroup P.p M)

noncomputable abbrev DegreeFourSelectedBinarySocleChart
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  selectedPrimeSoclePartElementaryChart P.p
    (select N)

abbrev DegreeFourSelectedBinaryTranslationIntersection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  DegreeFourSelectedBinarySocle block P select N ⊓ degreeFourTranslationImage block P N

abbrev DegreeFourSelectedBinaryTranslationPreimage
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (DegreeFourSelectedBinaryTranslationIntersection block P select N).comap
      (QuotientGroup.mk' N.1) ⊓ E block P

noncomputable abbrev DegreeFourSelectedBinarySourceSection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (elementaryChart block P).originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
    (elementaryChart block P).quotientRepresentation
    (DegreeFourSelectedBinaryTranslationPreimage block P select N)

noncomputable abbrev DegreeFourSelectedBinaryTargetSection
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  (DegreeFourSelectedBinarySocleChart block P select N).originalKernelChart.normalSubrepresentation
    (QuotientGroup.mk' (DegreeFourSelectedBinarySocle block P select N))
    (QuotientGroup.mk'_surjective (DegreeFourSelectedBinarySocle block P select N))
    (DegreeFourSelectedBinarySocleChart block P select N).quotientRepresentation
    (DegreeFourSelectedBinaryTranslationIntersection block P select N)

noncomputable abbrev DegreeFourSelectedBinarySourceSectionInflated
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  ActualWreathAffineCapacity.subrepresentationComp
    (QuotientGroup.mk' (E block P))
    (elementaryChart block P).quotientRepresentation.ρ
    (DegreeFourSelectedBinarySourceSection block P select N)

def degreeFourSelectedBinarySocleTopMap
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    preE7NonPairAction w U →*
      DegreeFourRetainedQuotient N ⧸ DegreeFourSelectedBinarySocle block P select N :=
  (QuotientGroup.mk' (DegreeFourSelectedBinarySocle block P select N)).comp
    (QuotientGroup.mk' N.1)

/-- The literal quotient homomorphism between the two actual elementary
intersections.  Keeping it multiplicative makes zero, addition, and the
ambient conjugation law consequences of the two elementary charts. -/
def degreeFourSelectedBinaryTranslationIntersectionHom
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    ↑(DegreeFourSelectedBinaryTranslationPreimage block P select N ⊓ E block P) →*
      ↑(DegreeFourSelectedBinaryTranslationIntersection block P select N ⊓
        DegreeFourSelectedBinarySocle block P select N) where
  toFun x := ⟨QuotientGroup.mk' N.1 x.1, x.2.1.1, x.2.1.1.1⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (QuotientGroup.mk' N.1)
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (QuotientGroup.mk' N.1) x.1 y.1

/-- Source intersection in its stored elementary-module coordinates. -/
noncomputable def degreeFourSelectedBinarySourceIntersectionEquiv
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  elementaryIntersectionMulEquiv
    (E block P) (elementaryChart block P)
    (DegreeFourSelectedBinaryTranslationPreimage block P select N)

/-- Target intersection in its stored elementary-module coordinates. -/
noncomputable def degreeFourSelectedBinaryTargetIntersectionEquiv
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :=
  elementaryIntersectionMulEquiv
    (DegreeFourSelectedBinarySocle block P select N)
    (DegreeFourSelectedBinarySocleChart block P select N)
    (DegreeFourSelectedBinaryTranslationIntersection block P select N)

/-- In elementary module coordinates, the literal intersection map is a
multiplicative homomorphism. -/
def degreeFourSelectedBinaryTranslationSectionMulHom
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Multiplicative
        (DegreeFourSelectedBinarySourceSection block P select N).toSubmodule →*
      Multiplicative
        (DegreeFourSelectedBinaryTargetSection block P select N).toSubmodule :=
  (degreeFourSelectedBinaryTargetIntersectionEquiv block P select N).toMonoidHom.comp
    ((degreeFourSelectedBinaryTranslationIntersectionHom block P select N).comp
      (degreeFourSelectedBinarySourceIntersectionEquiv block P select N).symm.toMonoidHom)

/-- Literal additive quotient map between the two elementary intersection
modules. -/
def degreeFourSelectedBinaryTranslationSectionAddHom
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourSelectedBinarySourceSection block P select N).toSubmodule →+
      (DegreeFourSelectedBinaryTargetSection block P select N).toSubmodule :=
  AddMonoidHom.toMultiplicative.symm
    (degreeFourSelectedBinaryTranslationSectionMulHom block P select N)

/-- Linear form of the literal quotient map. -/
def degreeFourSelectedBinaryTranslationSectionLinearMap
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourSelectedBinarySourceSection block P select N).toSubmodule →ₗ[ZMod P.p]
      (DegreeFourSelectedBinaryTargetSection block P select N).toSubmodule :=
  (degreeFourSelectedBinaryTranslationSectionAddHom block P select N).toZModLinearMap P.p

omit [Nontrivial block.Fibre] in
/-- The literal group homomorphism onto the selected translation
intersection is surjective. -/
theorem degreeFourSelectedBinaryTranslationIntersectionHom_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective
      (degreeFourSelectedBinaryTranslationIntersectionHom block P select N) := by
  let A := DegreeFourSelectedBinarySocle block P select N
  let H := DegreeFourSelectedBinaryTranslationIntersection block P select N
  let L := DegreeFourSelectedBinaryTranslationPreimage block P select N
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
theorem degreeFourSelectedBinaryTranslationSectionMulHom_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective
      (degreeFourSelectedBinaryTranslationSectionMulHom block P select N) := by
  simpa only [degreeFourSelectedBinaryTranslationSectionMulHom,
    MonoidHom.coe_comp, Function.comp_apply] using
    (degreeFourSelectedBinaryTargetIntersectionEquiv block P select N).surjective.comp
      ((degreeFourSelectedBinaryTranslationIntersectionHom_surjective block P select N).comp
        (degreeFourSelectedBinarySourceIntersectionEquiv block P select N).symm.surjective)

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
theorem degreeFourSelectedBinaryTranslationSectionLinearMap_surjective
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    Function.Surjective
      (degreeFourSelectedBinaryTranslationSectionLinearMap block P select N) := by
  exact additive_surjective_of_multiplicative_surjective
    (degreeFourSelectedBinaryTranslationSectionMulHom block P select N)
    (degreeFourSelectedBinaryTranslationSectionMulHom_surjective block P select N)

omit [Nontrivial block.Fibre] in
/-- The literal intersection homomorphism commutes with ambient
conjugation. -/
theorem degreeFourSelectedBinaryTranslationIntersectionHom_conj
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (x : ↑(DegreeFourSelectedBinaryTranslationPreimage block P select N ⊓ E block P)) :
    degreeFourSelectedBinaryTranslationIntersectionHom block P select N
        (MulAut.conjNormal g x) =
      MulAut.conjNormal (QuotientGroup.mk' N.1 g)
        (degreeFourSelectedBinaryTranslationIntersectionHom block P select N x) := by
  apply Subtype.ext
  change QuotientGroup.mk' N.1 (g * x.1 * g⁻¹) =
    QuotientGroup.mk' N.1 g * QuotientGroup.mk' N.1 x.1 *
      (QuotientGroup.mk' N.1 g)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- The source elementary equivalence identifies ambient conjugation with
the inflated source action. -/
theorem degreeFourSelectedBinarySourceIntersectionEquiv_action
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (v : Multiplicative
      (DegreeFourSelectedBinarySourceSection block P select N).toSubmodule) :
    Multiplicative.ofAdd
        ((DegreeFourSelectedBinarySourceSectionInflated block P select N).toRepresentation
          g v.toAdd) =
      degreeFourSelectedBinarySourceIntersectionEquiv block P select N
        (MulAut.conjNormal g
          ((degreeFourSelectedBinarySourceIntersectionEquiv block P select N).symm v)) := by
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
theorem degreeFourSelectedBinaryTargetIntersectionEquiv_action
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (y : ↑(DegreeFourSelectedBinaryTranslationIntersection block P select N ⊓
      DegreeFourSelectedBinarySocle block P select N)) :
    degreeFourSelectedBinaryTargetIntersectionEquiv block P select N
        (MulAut.conjNormal (QuotientGroup.mk' N.1 g) y) =
      Multiplicative.ofAdd
        ((DegreeFourSelectedBinaryTargetSection block P select N).toRepresentation
          (degreeFourSelectedBinarySocleTopMap block P select N g)
          (degreeFourSelectedBinaryTargetIntersectionEquiv block P select N y).toAdd) := by
  simpa only [degreeFourSelectedBinaryTargetIntersectionEquiv,
    degreeFourSelectedBinarySocleTopMap, MonoidHom.coe_comp,
    Function.comp_apply] using
    elementaryIntersectionMulEquiv_equivariant
      (DegreeFourSelectedBinarySocle block P select N)
      (DegreeFourSelectedBinarySocleChart block P select N)
      (DegreeFourSelectedBinaryTranslationIntersection block P select N)
      (QuotientGroup.mk' N.1 g) y

/-- Pointwise multiplicative equivariance.  This is stated before the linear
packaging so elaboration never unfolds the full retained-section expression
inside an `IntertwiningMap` field. -/
theorem degreeFourSelectedBinaryTranslationSectionMulHom_equivariant
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (v : Multiplicative
      (DegreeFourSelectedBinarySourceSection block P select N).toSubmodule) :
    degreeFourSelectedBinaryTranslationSectionMulHom block P select N
        (Multiplicative.ofAdd
          ((DegreeFourSelectedBinarySourceSectionInflated block P select N).toRepresentation
            g v.toAdd)) =
      Multiplicative.ofAdd
        ((DegreeFourSelectedBinaryTargetSection block P select N).toRepresentation
          (degreeFourSelectedBinarySocleTopMap block P select N g)
          (degreeFourSelectedBinaryTranslationSectionMulHom block P select N v).toAdd) := by
  let sourceEquiv := degreeFourSelectedBinarySourceIntersectionEquiv block P select N
  let targetEquiv := degreeFourSelectedBinaryTargetIntersectionEquiv block P select N
  let x := sourceEquiv.symm v
  have hsource : Multiplicative.ofAdd
      ((DegreeFourSelectedBinarySourceSectionInflated block P select N).toRepresentation
        g v.toAdd) = sourceEquiv (MulAut.conjNormal g x) := by
    exact degreeFourSelectedBinarySourceIntersectionEquiv_action block P select N g v
  have hsourceInv : sourceEquiv.symm (Multiplicative.ofAdd
      ((DegreeFourSelectedBinarySourceSectionInflated block P select N).toRepresentation
        g v.toAdd)) = MulAut.conjNormal g x := by
    have h := congrArg sourceEquiv.symm hsource
    simpa only [sourceEquiv.symm_apply_apply] using h
  have htarget : targetEquiv
      (MulAut.conjNormal (QuotientGroup.mk' N.1 g)
        (degreeFourSelectedBinaryTranslationIntersectionHom block P select N x)) =
      Multiplicative.ofAdd
        ((DegreeFourSelectedBinaryTargetSection block P select N).toRepresentation
          (degreeFourSelectedBinarySocleTopMap block P select N g)
          (targetEquiv
            (degreeFourSelectedBinaryTranslationIntersectionHom block P select N x)).toAdd) := by
    exact degreeFourSelectedBinaryTargetIntersectionEquiv_action block P select N g _
  change targetEquiv
      (degreeFourSelectedBinaryTranslationIntersectionHom block P select N
        (sourceEquiv.symm (Multiplicative.ofAdd
          ((DegreeFourSelectedBinarySourceSectionInflated block P select N).toRepresentation
            g v.toAdd)))) = _
  calc
    _ = targetEquiv
        (degreeFourSelectedBinaryTranslationIntersectionHom block P select N
          (MulAut.conjNormal g x)) :=
      congrArg targetEquiv
        (congrArg (degreeFourSelectedBinaryTranslationIntersectionHom block P select N)
          hsourceInv)
    _ = targetEquiv
        (MulAut.conjNormal (QuotientGroup.mk' N.1 g)
          (degreeFourSelectedBinaryTranslationIntersectionHom block P select N x)) :=
      congrArg targetEquiv
        (degreeFourSelectedBinaryTranslationIntersectionHom_conj block P select N g x)
    _ = _ := htarget

/-- The section map respects the original conjugation action. -/
theorem degreeFourSelectedBinaryTranslationSectionLinearMap_equivariant
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U))
    (g : preE7NonPairAction w U)
    (v : (DegreeFourSelectedBinarySourceSection block P select N).toSubmodule) :
    degreeFourSelectedBinaryTranslationSectionLinearMap block P select N
      ((DegreeFourSelectedBinarySourceSectionInflated block P select N).toRepresentation g v) =
    (DegreeFourSelectedBinaryTargetSection block P select N).toRepresentation
      (degreeFourSelectedBinarySocleTopMap block P select N g)
      (degreeFourSelectedBinaryTranslationSectionLinearMap block P select N v) := by
  apply Multiplicative.ofAdd.injective
  exact degreeFourSelectedBinaryTranslationSectionMulHom_equivariant
    block P select N g (Multiplicative.ofAdd v)

/-- Intertwining-map form used by the exceptional scalar Schur rows. -/
def degreeFourSelectedBinaryTranslationSectionIntertwiner
    (N : DegreeFourLiteralNormalAxis (w := w) (U := U)) :
    (DegreeFourSelectedBinarySourceSectionInflated block P select N).toRepresentation
      |>.IntertwiningMap
        ((DegreeFourSelectedBinaryTargetSection block P select N).toRepresentation.comp
          (degreeFourSelectedBinarySocleTopMap block P select N)) where
  toLinearMap := degreeFourSelectedBinaryTranslationSectionLinearMap block P select N
  isIntertwining' g := by
    apply LinearMap.ext
    exact degreeFourSelectedBinaryTranslationSectionLinearMap_equivariant block P select N g

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
