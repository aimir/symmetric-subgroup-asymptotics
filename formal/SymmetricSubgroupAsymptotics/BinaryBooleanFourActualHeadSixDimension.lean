import SymmetricSubgroupAsymptotics.BinaryBooleanFourHeadSixDimension
import SymmetricSubgroupAsymptotics.BinaryPairPolynomialCoordinates

/-! The eleven-dimensional lower bound is transported to the literal
original permutation module through its actual point labels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth

variable {G : Type} [Group G] [MulAction G (Fin 16)]

theorem boolean_four_actual_translation_submodule_finrank_ge_eleven_of_head_six
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G (Fin 16)))
    (e : Equiv.Perm (Fin 16))
    (htranslations : ∀ i : Fin 4, ∃ g : G,
      ∀ j, g⁻¹ • e.symm j = e.symm (flipIndex i j))
    (hhead : 6 ≤ Module.finrank (ZMod 2)
      (W.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    11 ≤ Module.finrank (ZMod 2) W.toSubmodule := by
  let P : V ≃ₗ[ZMod 2] V :=
    (BinaryBooleanFourPolynomialCoordinates.reindex e).trans coordinates
  let C : W.toSubmodule →ₗ[ZMod 2] V := P.toLinearMap.comp W.toSubmodule.subtype
  have hC : Function.Injective C := by
    intro a b hab
    apply Subtype.ext
    apply P.injective
    change P a.val = P b.val at hab
    exact hab
  have hdiff (i : Fin 4) : ∃ g : G, ∀ v : W.toSubmodule,
      C (W.toRepresentation g v - v) = derivative i (C v) := by
    obtain ⟨g, hg⟩ := htranslations i
    refine ⟨g, ?_⟩
    intro v
    change evaluate (fun j => v.val (g⁻¹ • e.symm j) - v.val (e.symm j)) =
      derivative i (evaluate (fun j => v.val (e.symm j)))
    rw [derivative_evaluate]
    have he : (fun j => v.val (g⁻¹ • e.symm j) - v.val (e.symm j)) =
        translate i (fun j => v.val (e.symm j)) - (fun j => v.val (e.symm j)) := by
      funext j
      change v.val (g⁻¹ • e.symm j) - v.val (e.symm j) =
        v.val (e.symm (flipIndex i j)) - v.val (e.symm j)
      rw [hg]
    exact congrArg (fun f : V => evaluate f) he
  exact boolean_four_representation_finrank_ge_eleven_of_head_six
    W.toRepresentation C hC hdiff hhead

end SymmetricSubgroupAsymptotics
