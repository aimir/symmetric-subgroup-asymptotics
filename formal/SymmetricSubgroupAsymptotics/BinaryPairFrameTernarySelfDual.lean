import SymmetricSubgroupAsymptotics.BinaryPairFrameTernarySignedRepresentation
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators
import Mathlib.LinearAlgebra.Dual.Basis

/-!
# Self-duality of a ternary signed pair-frame module

Signed permutation matrices over `F3` preserve the standard coordinate
pairing.  Consequently the full ternary signed coordinate representation
of every literal binary pair frame is equivalent to its contragredient.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryPairFrame

open OddMarkerTernaryChart

variable {X I : Type} {G : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame G I)

/-- The inverse affine sign at the inverse-transported coordinate equals
the original affine sign. -/
theorem affineTranslation_inv_at_inv_top
    (u : G) (i : I) :
    F.affineTranslation u⁻¹ ((F.top u)⁻¹ i) =
      F.affineTranslation u i := by
  have h := congrFun (F.affineTranslation_mul u u⁻¹) i
  rw [mul_inv_cancel, F.affineTranslation_one] at h
  have hneg := eq_neg_of_add_eq_zero_left h.symm
  simpa only [ZMod.neg_eq_self_mod_two] using hneg

/-- The standard coordinate basis identifies the signed module with its
linear dual. -/
def ternarySignedCoordinateDualEquiv [Finite I] :
    (I → ZMod 3) ≃ₗ[ZMod 3] Module.Dual (ZMod 3) (I → ZMod 3) :=
  (Pi.basisFun (ZMod 3) I).toDualEquiv

/-- The coordinate-dual equivalence intertwines the signed action with its
contragredient. -/
theorem ternarySignedCoordinateDualEquiv_intertwines
    [Finite I] (u : G) :
    (ternarySignedCoordinateDualEquiv (I := I)).toLinearMap.comp
      (ternarySignedRepresentation F u) =
      ((ternarySignedRepresentation F).dual u).comp
        (ternarySignedCoordinateDualEquiv (I := I)).toLinearMap := by
  apply LinearMap.ext
  intro v
  apply (Pi.basisFun (ZMod 3) I).ext
  intro i
  let j := (F.top u)⁻¹ i
  let c := signScalar
    (Multiplicative.ofAdd (F.affineTranslation u⁻¹ j))
  have hsingle := (ternarySignedRepresentation_single F u⁻¹ i).2
  have hj : F.top u⁻¹ i = j := by
    simp only [j, map_inv]
  change
    (Pi.basisFun (ZMod 3) I).toDual
        (ternarySignedRepresentation F u v)
        ((Pi.basisFun (ZMod 3) I) i) =
      (Pi.basisFun (ZMod 3) I).toDual v
        (ternarySignedRepresentation F u⁻¹
          ((Pi.basisFun (ZMod 3) I) i))
  rw [(Pi.basisFun (ZMod 3) I).toDual_apply_left,
    Pi.basisFun_repr, Pi.basisFun_apply, hsingle]
  rw [hj]
  rw [show Pi.single j c = c • (Pi.basisFun (ZMod 3) I) j by
    rw [Pi.basisFun_apply]
    ext k
    by_cases hkj : k = j <;> simp [Pi.single_apply, hkj]]
  rw [map_smul, (Pi.basisFun (ZMod 3) I).toDual_apply_left,
    Pi.basisFun_repr]
  change
    signScalar (Multiplicative.ofAdd (F.affineTranslation u i)) * v j =
      c * v j
  congr 1
  exact congrArg (fun z : ZMod 2 ↦
    signScalar (Multiplicative.ofAdd z))
      (affineTranslation_inv_at_inv_top F u i).symm

/-- The full ternary signed representation is self-dual. -/
def ternarySignedRepresentationDualEquiv [Finite I] :
    (ternarySignedRepresentation F).Equiv
      (ternarySignedRepresentation F).dual :=
  Representation.Equiv.mk (ternarySignedCoordinateDualEquiv (I := I))
    (ternarySignedCoordinateDualEquiv_intertwines F)

/-- Any uniform subrepresentation-generator theorem for the signed module
therefore transfers to its contragredient. -/
theorem ternarySignedRepresentation_dual_uniform_of_primal
    [Finite I] {n : ℕ}
    (h : UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F) n) :
    UniformSubrepresentationGeneratorBound
      (ternarySignedRepresentation F).dual n := by
  exact h.of_injective
    (ternarySignedRepresentationDualEquiv F).symm.toIntertwiningMap
    (ternarySignedRepresentationDualEquiv F).symm.injective

end BinaryPairFrame
end SymmetricSubgroupAsymptotics

end
