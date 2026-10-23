import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryStarStandardPlane
import Mathlib.Algebra.Module.Submodule.Equiv

/-! Exact linear coordinates on a maximal plane normalized by an
original natural word. The coordinate vector reconstructs the SAME
normalized ambient vector, rather than just its projective line. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

def unitaryStarCoordinateEquiv (q : CFSG.PrimePower) (s : ℕ) :
    (Fin 2 → q.Extension 2) ≃ₗ[q.Extension 2] starPlane q s :=
  LinearEquiv.ofInjective (starVectorLinear q s) (starVector_injective q s)

theorem unitaryStarCoordinateEquiv_apply (q : CFSG.PrimePower) (s : ℕ)
    (v : Fin 2 → q.Extension 2) :
    (unitaryStarCoordinateEquiv q s v).val = starVector q s v := rfl

def unitaryNormalizedPlaneCoordinates (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (g : naturalFixed (s + 3) q)
    (hg : unitarySubspaceImage q (s + 3) g S = starPlane q s) :
    S ≃ₗ[q.Extension 2] (Fin 2 → q.Extension 2) :=
  ((unitaryNaturalLinearEquiv q (s + 3) g).ofSubmodules S (starPlane q s) hg).trans
    (unitaryStarCoordinateEquiv q s).symm

theorem unitaryNormalizedPlaneCoordinates_reconstruct (q : CFSG.PrimePower) (s : ℕ)
    (S : Submodule (q.Extension 2) (Fin (s + 4) → q.Extension 2))
    (g : naturalFixed (s + 3) q)
    (hg : unitarySubspaceImage q (s + 3) g S = starPlane q s) (x : S) :
    starVector q s (unitaryNormalizedPlaneCoordinates q s S g hg x) =
      unitaryNaturalLinearEquiv q (s + 3) g x.val := by
  let y := (unitaryNaturalLinearEquiv q (s + 3) g).ofSubmodules S (starPlane q s) hg x
  have he := congrArg (fun z : starPlane q s => z.val)
    ((unitaryStarCoordinateEquiv q s).apply_symm_apply y)
  exact he

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
