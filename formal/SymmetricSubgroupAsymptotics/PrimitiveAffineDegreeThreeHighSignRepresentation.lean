import SymmetricSubgroupAsymptotics.BinaryPairFrameDegreeThreeHighSignCyclic
import SymmetricSubgroupAsymptotics.ActualWreathAffineCapacityOne
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreePairFrameBitReflection
import SymmetricSubgroupAsymptotics.PrimitiveAffineTranslationSubmoduleCoordinateTransport

/-!
# The literal high-sign module is the degree-three translation module

The local degree-three translation space is one-dimensional.  Scalarizing
each actual block coordinate identifies the quotient action on the
correlated translation submodule with a subrepresentation of the signed
pair-coordinate module.  This file keeps the native field `ZMod P.p`; the
proved equality `P.p = 3` transports the generic cyclicity theorem back to
that field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer

open OddMarkerTernaryChart

variable {w : ℕ} {U : PreE7NonPairActionClass w}
  {basePoint : Fin w}
  (block : OriginalMinimalBlock
    (A := preE7NonPairAction w U) basePoint)
  (P : PrimitiveAffineProfile block.Component block.Fibre)
  [Nontrivial block.Fibre]

local instance : Fact P.p.Prime := (chart block P).primeFact

/-- A chosen scalar coordinate on the one-dimensional local translation
space. -/
noncomputable def degreeThreeLocalVectorEquiv
    (hr : Nat.card block.Fibre = 3) :
    (chart block P).V ≃ₗ[ZMod P.p] ZMod P.p :=
  LinearEquiv.ofFinrankEq _ _ (by
    have h := (degreeThree_translation_prime_dim block P hr).2
    change Module.finrank (ZMod P.p) (chart block P).V = 1 at h
    rw [h, Module.finrank_self])

/-- The ternary sign scalar, retained over the native but provably equal
prime field of the affine chart. -/
def degreeThreeNativeSignScalar
    (hr : Nat.card block.Fibre = 3)
    (b : Multiplicative (ZMod 2)) : ZMod P.p :=
  (degreeThreeScalarFieldEquiv block P hr).symm (signScalar b)

@[simp] theorem degreeThreeNativeSignScalar_one
    (hr : Nat.card block.Fibre = 3) :
    degreeThreeNativeSignScalar block P hr 1 = 1 := by
  simp only [degreeThreeNativeSignScalar, signScalar_one, map_one]

theorem degreeThreeNativeSignScalar_mul
    (hr : Nat.card block.Fibre = 3)
    (a b : Multiplicative (ZMod 2)) :
    degreeThreeNativeSignScalar block P hr (a * b) =
      degreeThreeNativeSignScalar block P hr a *
        degreeThreeNativeSignScalar block P hr b := by
  simp only [degreeThreeNativeSignScalar, signScalar_mul, map_mul]

/-- The one-dimensional sign action over the native local prime field. -/
def degreeThreeNativeSignRepresentation
    (hr : Nat.card block.Fibre = 3) :
    Representation (ZMod P.p) (Multiplicative (ZMod 2)) (ZMod P.p) where
  toFun b := degreeThreeNativeSignScalar block P hr b • LinearMap.id
  map_one' := by
    ext z
    simp only [degreeThreeNativeSignScalar_one, one_smul,
      LinearMap.id_apply]
  map_mul' a b := by
    ext z
    change degreeThreeNativeSignScalar block P hr (a * b) * z =
      degreeThreeNativeSignScalar block P hr a *
        (degreeThreeNativeSignScalar block P hr b * z)
    rw [degreeThreeNativeSignScalar_mul, mul_assoc]

@[simp] theorem degreeThreeNativeSignRepresentation_apply
    (hr : Nat.card block.Fibre = 3)
    (b : Multiplicative (ZMod 2)) (z : ZMod P.p) :
    degreeThreeNativeSignRepresentation block P hr b z =
      degreeThreeNativeSignScalar block P hr b * z := rfl

/-- The signed pair-coordinate action over the native affine prime field. -/
def degreeThreeNativeSignedRepresentation
    (hr : Nat.card block.Fibre = 3) :
    Representation (ZMod P.p)
      (quotientAction block P).range
      (block.Points → ZMod P.p) :=
  (PermutationalWreathProduct.functionRepresentation
    (Q := (degreeThreeSignedQuotientPairFrame block P hr).top.range)
    (I := block.Points)
    (degreeThreeNativeSignRepresentation block P hr)).comp
      (BinaryPairFrame.affineWreathEmbedding
        (degreeThreeSignedQuotientPairFrame block P hr))

@[simp] theorem degreeThreeNativeSignedRepresentation_apply
    (hr : Nat.card block.Fibre = 3)
    (g : (quotientAction block P).range)
    (v : block.Points → ZMod P.p) (i : block.Points) :
    degreeThreeNativeSignedRepresentation block P hr g v i =
      degreeThreeNativeSignScalar block P hr
          (Multiplicative.ofAdd
            ((degreeThreeSignedQuotientPairFrame block P hr).affineTranslation
              g i)) *
        v (((degreeThreeSignedQuotientPairFrame block P hr).top g)⁻¹ i) := by
  rfl

/-- Scalarize the actual correlated translation submodule coordinatewise. -/
def degreeThreeTranslationScalarInclusion
    (hr : Nat.card block.Fibre = 3) :
    TranslationSubmodule block P →ₗ[ZMod P.p]
      (block.Points → ZMod P.p) where
  toFun v i := degreeThreeLocalVectorEquiv block P hr (v.1 i)
  map_add' _ _ := by funext i; exact map_add _ _ _
  map_smul' _ _ := by funext i; exact map_smul _ _ _

theorem degreeThreeTranslationScalarInclusion_injective
    (hr : Nat.card block.Fibre = 3) :
    Function.Injective (degreeThreeTranslationScalarInclusion block P hr) := by
  intro v z hvz
  apply Subtype.ext
  funext i
  apply (degreeThreeLocalVectorEquiv block P hr).injective
  exact congrFun hvz i

/-- Scalarization intertwines quotient conjugation on the correlated
translation module with the literal signed pair-coordinate action. -/
def degreeThreeTranslationScalarIntertwiner
    (hr : Nat.card block.Fibre = 3) :
    ((elementaryChart block P).quotientRepresentation.ρ).IntertwiningMap
      ((degreeThreeNativeSignedRepresentation block P hr).comp
        (degreeThreeSignedQuotientRangeEquiv block P).toMonoidHom) where
  toLinearMap := degreeThreeTranslationScalarInclusion block P hr
  isIntertwining' q := by
    apply LinearMap.ext
    intro v
    funext i
    let F := degreeThreeSignedQuotientPairFrame block P hr
    let g := degreeThreeSignedQuotientRangeEquiv block P q
    let j := (F.top g)⁻¹ i
    have htop : F.top g = (quotientEmbedding block P q).right :=
      degreeThreeSignedQuotientPairFrame_top_apply block P hr q
    have hij : (quotientEmbedding block P q).right • j = i := by
      rw [← htop]
      exact smul_inv_smul (F.top g) i
    have htransport :=
      translationSubmodule_quotientRepresentation_coordinate_transport_quotient
        block P q v j
    have hbit :=
      degreeThreeSignedQuotientPairFrame_affineTranslation_eq_localBit
        block P hr q i
    have hscalar :
        degreeThreeNativeSignScalar block P hr
            (Multiplicative.ofAdd (F.affineTranslation g i)) =
          degreeThreeLocalScalar block P hr
            ((quotientEmbedding block P q).left i) := by
      apply (degreeThreeScalarFieldEquiv block P hr).injective
      rw [degreeThreeLocalScalar_eq_signScalar block P hr]
      simp only [degreeThreeNativeSignScalar,
        RingEquiv.apply_symm_apply]
      exact congrArg (fun z : ZMod 2 ↦
        signScalar (Multiplicative.ofAdd z)) hbit
    change degreeThreeLocalVectorEquiv block P hr
        (((elementaryChart block P).quotientRepresentation.ρ q v).1 i) =
      degreeThreeNativeSignScalar block P hr
          (Multiplicative.ofAdd (F.affineTranslation g i)) *
        degreeThreeLocalVectorEquiv block P hr (v.1 j)
    rw [← hij, htransport, hij,
      degreeThreeLocalScalar_action block P hr, map_smul]
    change degreeThreeLocalScalar block P hr
        ((quotientEmbedding block P q).left i) *
          degreeThreeLocalVectorEquiv block P hr (v.1 j) = _
    rw [← hscalar]

/-- The quotient translation module is an actual subrepresentation of its
full native signed pair-coordinate module. -/
theorem degreeThreeTranslationScalarIntertwiner_injective
    (hr : Nat.card block.Fibre = 3) :
    Function.Injective (degreeThreeTranslationScalarIntertwiner block P hr) :=
  degreeThreeTranslationScalarInclusion_injective block P hr

/-- The native signed coordinate representation becomes the generic
`F3` signed representation after rewriting by the forced prime equality. -/
theorem degreeThreeNativeSignedRepresentation_dual_uniform_high_sign
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hsize :
      (Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) :
    UniformSubrepresentationGeneratorBound
      (degreeThreeNativeSignedRepresentation block P hr).dual 1 := by
  let F := degreeThreeSignedQuotientPairFrame block P hr
  have htrans := degreeThreeSignedQuotientRange_pretransitive
    block P hr hcomponent
  have hgeneric :=
    BinaryPairFrame.ternarySignedRepresentation_dual_uniform_one_of_six_or_twelve
      F htrans hsize
  have hp : P.p = 3 := (degreeThree_translation_prime_dim block P hr).1
  rw [hp]
  simpa [degreeThreeNativeSignedRepresentation,
    degreeThreeNativeSignRepresentation, degreeThreeNativeSignScalar,
    degreeThreeScalarFieldEquiv] using hgeneric

/-- High sign count makes the actual quotient translation contragredient
uniformly cyclic.  Dualizing the coordinate inclusion is surjective. -/
theorem degreeThreeTranslationQuotient_dual_uniform_high_sign
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hsize :
      (Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) :
    UniformSubrepresentationGeneratorBound
      ((elementaryChart block P).quotientRepresentation.ρ).dual 1 := by
  have hfull := degreeThreeNativeSignedRepresentation_dual_uniform_high_sign
    block P hr hcomponent hsize
  let f := degreeThreeTranslationScalarIntertwiner block P hr
  have hf : Function.Injective f :=
    degreeThreeTranslationScalarIntertwiner_injective block P hr
  apply hfull.of_surjective (RepresentationHeadExact.dualMap f)
  exact LinearMap.dualMap_surjective_of_injective hf

/-- Pull the quotient theorem back to the original affine group, in the
exact ambient representation used by the capacity construction. -/
theorem degreeThreeActualAmbient_dual_uniform_high_sign
    (hTraceyPerm : TraceyPermutationGeneratorInput)
    (hr : Nat.card block.Fibre = 3)
    (hcomponent : Nat.card block.Component = 6)
    (hsize :
      (Nat.card block.Points = 6 ∧
        2 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr))) ∨
      (Nat.card block.Points = 12 ∧
        3 ≤ Nat.card (BinaryPairFrame.CoordinateSign
          (degreeThreeSignedQuotientPairFrame block P hr)))) :
    UniformSubrepresentationGeneratorBound
      (ActualWreathAffineCapacity.ambientRepresentation
        (initialState hTraceyPerm block) (localMap block P)
        (localTranslationChart block P)).dual 1 := by
  have hquot := degreeThreeTranslationQuotient_dual_uniform_high_sign
    block P hr hcomponent hsize
  have hpull := hquot.comp_of_surjective
    ((elementaryChart block P).quotientRepresentation.ρ).dual
    (QuotientGroup.mk' (E block P))
    (QuotientGroup.mk'_surjective (E block P))
  simpa only [Representation.dual_apply, Representation.comp_apply,
    MonoidHom.comp_apply, map_inv,
    ActualWreathAffineCapacity.ambientRepresentation,
    initialState, localTranslationChart, elementaryChart,
    ActualWreathAffineCapacity.E,
    PermutationalWreathProduct.Compression.kernelElementaryChart] using hpull

end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
