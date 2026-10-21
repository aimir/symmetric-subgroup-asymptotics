import SymmetricSubgroupAsymptotics.BinaryPairModuleLayerGraph

/-! Reversible scalar coordinates on the same original point module.
Both its pair layers and all affine offsets of the original action remain
visible. No splitting of the original permutation group is used. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)}
  (F : BinaryPairFrame U (Fin w))

/-- A function on a binary pair is determined by its zero value and sum. -/
theorem pair_value_eq_zero_add_sum
    (f : X → ZMod 2) (i : Fin w) (b : ZMod 2) :
    f (F.frame (i, b)) = F.pairZeroRestriction f i + b * F.pairSum f i := by
  fin_cases b
  · change f (F.frame (i, 0)) = f (F.frame (i, 0)) + 0 * _
    simp
  · change f (F.frame (i, 1)) = f (F.frame (i, 0)) +
      1 * (f (F.frame (i, 0)) + f (F.frame (i, 1)))
    rw [one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- Coordinates are the actual zero value and pair-sum, on the original
point set. The inverse keeps both layers, including their correlation. -/
def pairLayerCoordinateEquiv : (X → ZMod 2) ≃ₗ[ZMod 2]
    (Fin w → ZMod 2) × (Fin w → ZMod 2) where
  toFun f := (F.pairZeroRestriction f, F.pairSum f)
  invFun a x := a.1 (F.frame.symm x).1 +
    (F.frame.symm x).2 * a.2 (F.frame.symm x).1
  left_inv f := by
    funext x
    obtain ⟨⟨i, b⟩, rfl⟩ := F.frame.surjective x
    simpa only [Equiv.symm_apply_apply] using (F.pair_value_eq_zero_add_sum f i b).symm
  right_inv a := by
    apply Prod.ext
    · funext i
      change a.1 (F.frame.symm (F.frame (i, 0))).1 +
        (F.frame.symm (F.frame (i, 0))).2 *
          a.2 (F.frame.symm (F.frame (i, 0))).1 = a.1 i
      simp only [Equiv.symm_apply_apply, zero_mul, add_zero]
    · funext i
      change (a.1 (F.frame.symm (F.frame (i, 0))).1 +
        (F.frame.symm (F.frame (i, 0))).2 *
          a.2 (F.frame.symm (F.frame (i, 0))).1) +
        (a.1 (F.frame.symm (F.frame (i, 1))).1 +
          (F.frame.symm (F.frame (i, 1))).2 *
            a.2 (F.frame.symm (F.frame (i, 1))).1) = a.2 i
      simp only [Equiv.symm_apply_apply, zero_mul, add_zero, one_mul]
      rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  map_add' f g := Prod.ext (F.pairZeroRestriction.map_add f g) (F.pairSum.map_add f g)
  map_smul' c f := Prod.ext (F.pairZeroRestriction.map_smul c f) (F.pairSum.map_smul c f)

/-- The first layer of the original action includes the actual affine
offset; it is not merely a second copy of the top permutation action. -/
theorem pairZeroRestriction_action (u : U) (f : X → ZMod 2) :
    F.pairZeroRestriction (permutationFunctionRepresentation (ZMod 2) U X u f) =
      fun i => F.pairZeroRestriction f ((F.top u)⁻¹ i) +
        F.offset u⁻¹ i * F.pairSum f ((F.top u)⁻¹ i) := by
  funext i
  change f ((u⁻¹ : U).val (F.frame (i, 0))) = _
  rw [F.action_frame]
  simpa only [zero_add, map_inv] using
    F.pair_value_eq_zero_add_sum f (F.top u⁻¹ i) (F.offset u⁻¹ i)

end SymmetricSubgroupAsymptotics.BinaryPairFrame
