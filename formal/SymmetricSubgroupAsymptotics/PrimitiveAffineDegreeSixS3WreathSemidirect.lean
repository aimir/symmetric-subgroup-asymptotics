import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathSource
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-!
# Canonical ternary semidirect coordinates on `S₃ ≀ C₂`

The degree-six comparator is used as the universal two-sign ternary
section.  This file exposes its elementary normal layer explicitly:

`S₃ ≀ C₂ ≃ C₃² ⋊ (C₂ ≀ C₂)`.

The coordinates are the affine offsets of the two literal permutations of
`Fin 3`; the binary quotient is the already defined coordinatewise sign
map.  All checks are on the fixed groups of orders `3`, `6`, `8`, and `72`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

private abbrev S3 := Equiv.Perm (Fin 3)

/-- Additive two-coordinate ternary translation space. -/
abbrev TernaryPlane := Fin 2 → ZMod 3

/-- Multiplicative form of the ternary plane. -/
abbrev TernaryKernel := Multiplicative TernaryPlane

/-- Interpret a literal point of `Fin 3` as its residue class. -/
private def finThreeCoordinate (i : Fin 3) : ZMod 3 := i.val

/-- Affine translation offset of a literal permutation of three points. -/
def s3TranslationCoordinate (g : S3) : ZMod 3 :=
  finThreeCoordinate (g 0)

/-- The two affine offsets of the base permutations in the wreath product. -/
def ternaryCoordinates (g : G) : TernaryPlane
  | 0 => s3TranslationCoordinate g.left.1
  | 1 => s3TranslationCoordinate g.left.2

/-- The monomial `D8` action on two ternary coordinates.  Base signs act
by `±1`; the outer binary coordinate exchanges the two entries. -/
def monomialAut (d : D8) : MulAut TernaryKernel where
  toFun v := Multiplicative.ofAdd (fun i =>
    let j : Fin 2 := if d.right = 1 then i else ⟨1 - i.val, by omega⟩
    OddMarkerTernaryChart.signScalar
      (if i = 0 then d.left.1 else d.left.2) * v.toAdd j)
  invFun v := Multiplicative.ofAdd (fun i =>
    let j : Fin 2 := if d.right = 1 then i else ⟨1 - i.val, by omega⟩
    OddMarkerTernaryChart.signScalar
      (if j = 0 then d.left.1 else d.left.2) * v.toAdd j)
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    revert d v i
    native_decide
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    revert d v i
    native_decide
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    revert d v w i
    native_decide

/-- The preceding monomial automorphisms form the literal `D8`
representation on `C₃²`. -/
def monomialAction : D8 →* MulAut TernaryKernel where
  toFun := monomialAut
  map_one' := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    funext i
    revert v i
    native_decide
  map_mul' d e := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    funext i
    revert d e v i
    native_decide

/-- Canonical split model of the degree-six comparator. -/
abbrev SemidirectModel :=
  TernaryKernel ⋊[monomialAction] D8

/-- Literal affine coordinates followed by the coordinatewise sign
quotient. -/
def semidirectMap : G →* SemidirectModel where
  toFun g := ⟨Multiplicative.ofAdd (ternaryCoordinates g), projection g⟩
  map_one' := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      revert i
      native_decide
    · exact map_one projection
  map_mul' g h := by
    apply SemidirectProduct.ext
    · apply Multiplicative.toAdd.injective
      funext i
      revert g h i
      native_decide
    · exact map_mul projection g h

/-- The fixed wreath comparator is exactly its ternary monomial
semidirect model. -/
def semidirectEquiv : G ≃* SemidirectModel :=
  MulEquiv.ofBijective semidirectMap (by
    constructor <;> decide +kernel)

@[simp] theorem semidirectEquiv_right (g : G) :
    (semidirectEquiv g).right = projection g := rfl

@[simp] theorem semidirectEquiv_left (g : G) :
    (semidirectEquiv g).left =
      Multiplicative.ofAdd (ternaryCoordinates g) := rfl

end DegreeSixS3Wreath
end SymmetricSubgroupAsymptotics

end
