import SymmetricSubgroupAsymptotics.DistinctDiagonalFullSubmodule
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeThreeFourBlockSignedIsotypeSplit

/-!
# The four distinct-sign ternary module

This file isolates the algebraic conclusion used by the singleton-isotype
branch of the degree-three, four-block affine residual.

For the literal binary pair frame, turn each actual bit character into its
ternary sign scalar.  Four distinct bit characters remain distinct after
this scalar change.  A submodule stable under those literal diagonal
operators is therefore the whole `F₃⁴` as soon as every original coordinate
is nonzero.  Coordinate nonvanishing is deliberately the remaining
action-theoretic premise: in the affine application it must be proved from
the actual translation intersection and block transitivity, rather than
from an independently enlarged direct product.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace DiagonalInvariantSubmodules

variable {k ι J : Type*} [Field k]

/-- In a one-dimensional coordinate over a field, a nonzero value can be
rescaled to any prescribed value.  Thus nonzero projection on every literal
coordinate is exactly the fullness premise used by the distinct-isotype
projector theorem. -/
theorem fullCoordinates_of_each_coordinate_nonzero
    (K : Submodule k (ι → k))
    (hnonzero : ∀ i : ι, ∃ v : K, v.1 i ≠ 0) :
    FullCoordinates K := by
  intro i c
  obtain ⟨v, hv⟩ := hnonzero i
  refine ⟨(c * (v.1 i)⁻¹) • v, ?_⟩
  change (c * (v.1 i)⁻¹) * v.1 i = c
  rw [mul_assoc, inv_mul_cancel₀ hv, mul_one]

/-- Distinct diagonal characters and nonzero projection on each coordinate
force the whole coordinate module. -/
theorem eq_top_of_each_coordinate_nonzero_of_injective
    [Fintype ι]
    (scalar : ι → J → k)
    (hscalar : Function.Injective scalar)
    (K : Stable scalar)
    (hnonzero : ∀ i : ι, ∃ v : K.1, v.1 i ≠ 0) :
    K.1 = ⊤ :=
  eq_top_of_fullCoordinates_of_injective scalar hscalar K
    (fullCoordinates_of_each_coordinate_nonzero K.1 hnonzero)

end DiagonalInvariantSubmodules

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineImprimitiveBlockTransfer
namespace BinaryPairFrame

open OddMarkerTernaryChart

variable {X : Type} {G : Subgroup (Equiv.Perm X)}

/-- The literal ternary scalar character attached to one coordinate of an
actual four-pair frame. -/
def fourCoordinateTernaryScalar
    (F : BinaryPairFrame G (Fin 4)) (i : Fin 4) (k : F.top.ker) : ZMod 3 :=
  signScalar (Multiplicative.ofAdd (F.bits k i))

/-- Passing from an actual binary character to the ternary sign scalar does
not identify two coordinate characters. -/
theorem fourCoordinateTernaryScalar_injective
    (F : BinaryPairFrame G (Fin 4))
    (hsign : Function.Injective (fourCoordinateSign F)) :
    Function.Injective (fourCoordinateTernaryScalar F) := by
  intro i j hij
  apply hsign
  apply Subtype.ext
  funext k
  exact congrArg Multiplicative.toAdd
    (signScalar_injective (congrFun hij k))

/-- The exact singleton-isotype algebra.  The subgroup `K` is stable under
the four literal characters of the pair kernel and has a nonzero value in
every original coordinate.  It is consequently the full `F₃⁴`; no
semisimple decomposition or freely selected character list occurs. -/
theorem fourCoordinateStable_eq_top_of_distinct_signs
    (F : BinaryPairFrame G (Fin 4))
    (hsign : Function.Injective (fourCoordinateSign F))
    (K : DiagonalInvariantSubmodules.Stable
      (fourCoordinateTernaryScalar F))
    (hnonzero : ∀ i : Fin 4, ∃ v : K.1, v.1 i ≠ 0) :
    K.1 = ⊤ :=
  DiagonalInvariantSubmodules.eq_top_of_each_coordinate_nonzero_of_injective
    (fourCoordinateTernaryScalar F)
    (fourCoordinateTernaryScalar_injective F hsign) K hnonzero

end BinaryPairFrame
end PrimitiveAffineImprimitiveBlockTransfer
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
