import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryLineNormalization
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairedTorus

/-! Actual upper/opposite words normalize the first column to e0,
including its scalar, in every literal A rank at least three. No norm
surjectivity, full-unitary equality, or group-generation premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGTwistedAUpperUnipotent

theorem exists_join_first_column_one (q : CFSG.PrimePower) (s : ℕ)
    (g : naturalFixed (s + 3) q) :
    ∃ h : naturalFixed (s + 3) q,
      h.val ∈ naturalUpperOppositeJoin q (s + 3) ∧
      (fun i => ((h * g).val.val : Mat (q.Extension 2) (s + 3)) i 0) = Pi.single 0 1 := by
  obtain ⟨u, hu, a, ha, hcol⟩ := exists_join_first_column_axis q (s + 1) g
  let T := pairedTorus q s a⁻¹
  refine ⟨T * u, (naturalUpperOppositeJoin q (s + 3)).mul_mem
    (pairedTorus_mem_join q s a⁻¹) hu, ?_⟩
  have hact : (fun i => (((T * u) * g).val.val : Mat (q.Extension 2) (s + 3)) i 0) =
      (T.val.val : Mat (q.Extension 2) (s + 3)) *ᵥ
        (fun i => ((u * g).val.val : Mat (q.Extension 2) (s + 3)) i 0) := by
    funext i
    change ((((T.val.val : Mat (q.Extension 2) (s + 3)) *
      (u.val.val : Mat (q.Extension 2) (s + 3))) *
        (g.val.val : Mat (q.Extension 2) (s + 3))) i 0) =
      (((T.val.val : Mat (q.Extension 2) (s + 3)) *
        ((u.val.val : Mat (q.Extension 2) (s + 3)) *
          (g.val.val : Mat (q.Extension 2) (s + 3)))) i 0)
    simp only [mul_assoc]
  rw [hact, hcol]
  simpa only [inv_mul_cancel₀ ha] using
    pairedTorus_first_axis q s a⁻¹ a (inv_ne_zero ha)

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
