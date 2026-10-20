import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeSixS3WreathGroup
import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-!
# Ternary semidirect coordinates on `S₃ ≀ C₂`

This module defines the literal coordinate homomorphism
`S₃ ≀ C₂ → C₃² ⋊ (C₂ ≀ C₂)`.  Its bijectivity and the resulting equivalence
are kept in the small downstream module
`PrimitiveAffineDegreeSixS3WreathSemidirect`.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace DegreeSixS3Wreath

/-- Additive two-coordinate ternary translation space. -/
abbrev TernaryPlane := Fin 2 → ZMod 3

/-- Multiplicative form of the ternary plane. -/
abbrev TernaryKernel := Multiplicative TernaryPlane

/-- Interpret a literal point of `Fin 3` as its residue class. -/
private def finThreeCoordinate (i : Fin 3) : ZMod 3 := i.val

/-- Affine translation offset of a literal permutation of three points. -/
def s3TranslationCoordinate (g : S3) : ZMod 3 :=
  finThreeCoordinate (g 0)

/-- Translation and sign determine a literal permutation of three points. -/
private def s3AffineCoordinates (g : S3) : ZMod 3 × C2 :=
  (s3TranslationCoordinate g, oddMarkerSign g)

private theorem s3AffineCoordinates_injective :
    Function.Injective s3AffineCoordinates := by
  decide +kernel

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

instance : Finite SemidirectModel :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

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

/-- The coordinate homomorphism is injective.  The only finite decision is
the six-element fact that translation and sign determine an `S₃` element;
the full order-72 map is handled structurally. -/
theorem semidirectMap_injective : Function.Injective semidirectMap := by
  intro g h heq
  have hternary : ternaryCoordinates g = ternaryCoordinates h := by
    apply Multiplicative.ofAdd.injective
    exact congrArg SemidirectProduct.left heq
  have hprojection : projection g = projection h :=
    congrArg SemidirectProduct.right heq
  have hcoordinate0 :
      s3TranslationCoordinate g.left.1 =
        s3TranslationCoordinate h.left.1 := by
    simpa only [ternaryCoordinates] using congrFun hternary (0 : Fin 2)
  have hcoordinate1 :
      s3TranslationCoordinate g.left.2 =
        s3TranslationCoordinate h.left.2 := by
    simpa only [ternaryCoordinates] using congrFun hternary (1 : Fin 2)
  have hsign0 : oddMarkerSign g.left.1 = oddMarkerSign h.left.1 := by
    have hs := congrArg (fun d : D8 => d.left.1) hprojection
    change oddMarkerSign g.left.1 = oddMarkerSign h.left.1 at hs
    exact hs
  have hsign1 : oddMarkerSign g.left.2 = oddMarkerSign h.left.2 := by
    have hs := congrArg (fun d : D8 => d.left.2) hprojection
    change oddMarkerSign g.left.2 = oddMarkerSign h.left.2 at hs
    exact hs
  have houter : g.right = h.right := by
    have hs := congrArg SemidirectProduct.right hprojection
    change g.right = h.right at hs
    exact hs
  apply SemidirectProduct.ext
  · apply Prod.ext
    · apply s3AffineCoordinates_injective
      exact Prod.ext hcoordinate0 hsign0
    · apply s3AffineCoordinates_injective
      exact Prod.ext hcoordinate1 hsign1
  · exact houter

/-- The split model and the literal wreath group both have order 72. -/
theorem card_SemidirectModel : Nat.card SemidirectModel = 72 := by
  have hkernel : Nat.card TernaryKernel = 9 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin,
      Nat.card_zmod]
    norm_num
  rw [SemidirectProduct.card, hkernel, card_D8]

end DegreeSixS3Wreath
end SymmetricSubgroupAsymptotics

end
