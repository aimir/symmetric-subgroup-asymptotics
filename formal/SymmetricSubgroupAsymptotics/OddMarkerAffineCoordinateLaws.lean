import SymmetricSubgroupAsymptotics.OddMarkerTernaryChart

/-! Public affine-coordinate laws for the same six literal permutations
of three points. These small local facts support arbitrary coordinate
sets later; no wreath product, action list or subgroup is enumerated. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.OddMarkerAffineCoordinateLaws
open OddMarkerTernaryChart

def offset (g : OddMarkerGroup) : ZMod 3 := (g 0).val

theorem affine_apply (g : OddMarkerGroup) (i : Fin 3) :
    ((g i).val : ZMod 3)=offset g+signScalar (oddMarkerSign g)*(i.val : ZMod 3) := by
  revert g i
  decide +kernel

theorem offset_one : offset 1=0 := by decide +kernel

theorem offset_mul (g h : OddMarkerGroup) :
    offset (g*h)=offset g+signScalar (oddMarkerSign g)*offset h := by
  exact affine_apply g (h 0)

theorem coordinates_injective :
    Function.Injective (fun g : OddMarkerGroup => (offset g,oddMarkerSign g)) := by
  decide +kernel

end SymmetricSubgroupAsymptotics.OddMarkerAffineCoordinateLaws
