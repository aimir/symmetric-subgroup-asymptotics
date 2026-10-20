import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightCoordinateIrreducibility
import SymmetricSubgroupAsymptotics.BinaryThreeInvariantSubspaces

/-! The actual primitive affine complement fixes no nonzero vector and no
nonzero dual vector in its specified binary three-dimensional coordinates. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]
  [Finite L] [Finite Ω] [Nontrivial Ω]
  (P : PrimitiveAffineProfile L Ω)
  (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
  (a : P.V ≃* Multiplicative (Fin 3 → ZMod 2))

include hprimitive

theorem coordinate_no_fixed_vector (v : Fin 3 → ZMod 2) (hv : v ≠ 0)
    (hfix : ∀ k : P.complement x, (P.complementCoordinateMap x a k).val *ᵥ v = v) :
    False := by
  obtain ⟨W, hWb, hWt, hstable⟩ := BinaryThreeInvariantSubspaces.line v hv
  have h := P.invariantCoordinateSubmodule_eq_bot_or_top hprimitive x a W
    (fun k w hw => hstable _ (hfix k) w hw)
  exact h.elim hWb hWt

theorem coordinate_no_fixed_covector (l : Fin 3 → ZMod 2) (hl : l ≠ 0)
    (hfix : ∀ k : P.complement x, l ᵥ* (P.complementCoordinateMap x a k).val = l) :
    False := by
  obtain ⟨W, hWb, hWt, hstable⟩ := BinaryThreeInvariantSubspaces.plane l hl
  have h := P.invariantCoordinateSubmodule_eq_bot_or_top hprimitive x a W
    (fun k w hw => hstable _ (hfix k) w hw)
  exact h.elim hWb hWt

end SymmetricSubgroupAsymptotics.PrimitiveAffineProfile

end
