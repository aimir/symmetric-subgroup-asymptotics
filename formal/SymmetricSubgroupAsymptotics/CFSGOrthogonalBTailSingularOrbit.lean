import SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailGram
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBSingularVectorOrbit
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBHighestRootCoordinates

/-! Original tail root words normalize a singular tail vector while
fixing the SAME first positive basis vector. This supplies the second
vector step of the actual singular two-plane orbit. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
open CFSGOrthogonalBSerreMatrices CFSGOrthogonalBVectorCoordinates CFSGOrthogonalBUnipotent
variable (K : Type) [Field K]

theorem exists_tail_normalize_singular (h2 : (2 : K) ≠ 0) (s : ℕ)
    (v : Index (s + 3) → K) (hn : v (neg (s + 3) 0) = 0)
    (ht : tailRestriction K (s + 2) v ≠ 0) (hs : (gram K (s + 3)).toBilin' v v = 0) :
    ∃ g : elementaryRootGroup K (s + 3),
      (g.val : Mat K (s + 3)) *ᵥ Pi.single (pos (s + 3) 0) 1 = Pi.single (pos (s + 3) 0) 1 ∧
      (g.val : Mat K (s + 3)) *ᵥ v = v (pos (s + 3) 0) • Pi.single (pos (s + 3) 0) 1 +
        Pi.single (pos (s + 3) (secondIndex s)) 1 := by
  have hs' : (gram K (s + 2)).toBilin' (tailRestriction K (s + 2) v)
      (tailRestriction K (s + 2) v) = 0 :=
    (gram_norm_tail_of_negative_head_zero K (s + 2) v hn).symm.trans hs
  obtain ⟨h, hh⟩ := exists_normalize_singular K h2 s (tailRestriction K (s + 2) v) ht hs'
  let g := tailElementaryHom K (s + 2) h
  let w := (g.val : Mat K (s + 3)) *ᵥ v
  have hw : tailRestriction K (s + 2) w = Pi.single (pos (s + 2) 0) 1 :=
    (tailElementaryHom_tail_action K (s + 2) h v).trans hh
  have hwn : w (neg (s + 3) 0) = 0 :=
    (tailElementaryHom_head_negative K (s + 2) h v).trans hn
  have hwp : w (pos (s + 3) 0) = v (pos (s + 3) 0) :=
    tailElementaryHom_head_positive K (s + 2) h v
  refine ⟨g, tailElementaryHom_fixes_first_positive K (s + 2) h, ?_⟩
  have he := vector_eq_first_add_tail_basis K (s + 1) w hw hwn
  rw [hwp] at he
  exact he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalBTailCoordinates
