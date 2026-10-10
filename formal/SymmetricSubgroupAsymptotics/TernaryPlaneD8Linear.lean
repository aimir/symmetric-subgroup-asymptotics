import SymmetricSubgroupAsymptotics.Non2PreE7LinearThreeGroup
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSemidirect

/-!
# The standard dihedral action on the ternary plane

The fixed degree-six comparator is

`C₃² ⋊ (C₂ ≀ C₂)`.

This file records the linear part of that displayed semidirect product as
an actual subgroup of `GL₂(3)`.  Keeping the same coordinate formula as
`DegreeSixS3Wreath.monomialAction` lets later section-recognition results
transport both the top group and its action, rather than using an abstract
order-eight group isomorphism.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

private abbrev C2 := Multiplicative (ZMod 2)
private abbrev V4 := C2 × C2

/-- The standard monomial `D8` representation on the additive ternary
plane.  This is the linear form of `monomialAction`. -/
def monomialRepresentation :
    Representation (ZMod 3) D8 TernaryPlane where
  toFun d :=
    { toFun := fun v i =>
        let j : Fin 2 :=
          if d.right = 1 then i else ⟨1 - i.val, by omega⟩
        OddMarkerTernaryChart.signScalar
          (if i = 0 then d.left.1 else d.left.2) * v j
      map_add' := by
        intro v w
        funext i
        revert d v w i
        native_decide
      map_smul' := by
        intro c v
        funext i
        revert d c v i
        native_decide }
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    revert v i
    native_decide
  map_mul' d e := by
    apply LinearMap.ext
    intro v
    funext i
    revert d e v i
    native_decide

@[simp] theorem monomialRepresentation_apply
    (d : D8) (v : TernaryPlane) (i : Fin 2) :
    monomialRepresentation d v i =
      let j : Fin 2 :=
        if d.right = 1 then i else ⟨1 - i.val, by omega⟩
      OddMarkerTernaryChart.signScalar
        (if i = 0 then d.left.1 else d.left.2) * v j := rfl

/-- The multiplicative and linear versions of the standard action have
the same underlying coordinate function. -/
theorem monomialAction_toAdd
    (d : D8) (v : TernaryKernel) :
    (monomialAction d v).toAdd = monomialRepresentation d v.toAdd := rfl

/-- The standard monomial representation remembers every element of
`D8`. -/
theorem monomialRepresentation_asGroupHom_injective :
    Function.Injective
      (Representation.asGroupHom monomialRepresentation) := by
  intro d e h
  apply (show ∀ d e : D8,
      (∀ v : TernaryPlane,
        monomialRepresentation d v = monomialRepresentation e v) →
          d = e by native_decide) d e
  intro v
  exact congrArg
    (fun u : (Module.End (ZMod 3) TernaryPlane)ˣ =>
      (u : Module.End (ZMod 3) TernaryPlane) v) h

/-- Matrix form of the standard `D8` action, in the coordinate basis of
`Fin 2 → ZMod 3`. -/
def standardD8LinearMap : D8 →* LinearThree.GL3 :=
  (Matrix.GeneralLinearGroup.toLin'
      (Pi.basisFun (ZMod 3) (Fin 2))).symm.toMonoidHom.comp
    (Representation.asGroupHom monomialRepresentation)

theorem standardD8LinearMap_injective :
    Function.Injective standardD8LinearMap :=
  (Matrix.GeneralLinearGroup.toLin'
      (Pi.basisFun (ZMod 3) (Fin 2))).symm.injective.comp
    monomialRepresentation_asGroupHom_injective

/-- Reading the standard matrix back as a linear operator recovers the
displayed monomial representation. -/
@[simp] theorem standardD8LinearMap_toLin_apply
    (d : D8) (v : TernaryPlane) :
    (Matrix.GeneralLinearGroup.toLin'
      (Pi.basisFun (ZMod 3) (Fin 2))
        (standardD8LinearMap d)).toLinearEquiv v =
      monomialRepresentation d v := by
  change
    (Matrix.GeneralLinearGroup.toLin'
      (Pi.basisFun (ZMod 3) (Fin 2))
        ((Matrix.GeneralLinearGroup.toLin'
          (Pi.basisFun (ZMod 3) (Fin 2))).symm
            (Representation.asGroupHom monomialRepresentation d))).toLinearEquiv v = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The two base signs included in the standard dihedral top. -/
def d8BaseBits : V4 →* D8 := SemidirectProduct.inl

theorem d8BaseBits_injective : Function.Injective d8BaseBits := by
  intro x y h
  exact congrArg SemidirectProduct.left h

/-- The standard diagonal Klein four in `GL₂(3)`. -/
def standardKleinLinearMap : V4 →* LinearThree.GL3 :=
  standardD8LinearMap.comp d8BaseBits

theorem standardKleinLinearMap_injective :
    Function.Injective standardKleinLinearMap :=
  standardD8LinearMap_injective.comp d8BaseBits_injective

/-- The standard dihedral matrix image is exactly the normalizer of its
diagonal Klein four. -/
set_option maxRecDepth 100000 in
theorem standardD8LinearRange_eq_normalizer :
    standardD8LinearMap.range =
      Subgroup.normalizer (standardKleinLinearMap.range : Set LinearThree.GL3) := by
  decide +kernel

end DegreeSixS3Wreath
end SymmetricSubgroupAsymptotics

end
