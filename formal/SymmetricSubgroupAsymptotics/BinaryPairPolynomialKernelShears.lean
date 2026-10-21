import SymmetricSubgroupAsymptotics.BinaryPairPolynomialCoordinates

/-! Actual correlated outer-kernel elements act by the pointwise shear
operators. Kernel-vector membership supplies a real original group element. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 16))

theorem exists_kernel_bits (a : Fin 16 → ZMod 2) (ha : a ∈ F.kernelSpace) :
    ∃ k : F.top.ker, F.bits k = a := by
  obtain ⟨k, hk⟩ := F.kernelSpaceHom_bijective.surjective (Multiplicative.ofAdd ⟨a, ha⟩)
  exact ⟨k, congrArg (fun z : Multiplicative F.kernelSpace => z.toAdd.val) hk⟩

theorem polynomialPairCoordinate_kernel_difference
    (e : Equiv.Perm (Fin 16)) (k : F.top.ker) (b : Fin 16)
    (hbits : ∀ j, F.bits k (e.symm j) = monomial (support b) j)
    (f : X → ZMod 2) :
    F.polynomialPairCoordinateEquiv e
      (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f) =
      (monomialMultiplier b (F.polynomialPairCoordinateEquiv e f).2, 0) := by
  have hk : (k.val : Equiv.Perm X) = F.physicalFlip (F.bits k) := by
    apply Equiv.ext
    intro x
    obtain ⟨⟨j, c⟩, rfl⟩ := F.frame.surjective x
    rw [F.kernel_action_frame, F.physicalFlip_apply_frame]
  have hact : F.pairLayerCoordinateEquiv
      (permutationFunctionRepresentation (ZMod 2) U X (k : U) f) =
      affinePairLayerMap 1 (F.bits k) (F.pairLayerCoordinateEquiv f) := by
    change F.pairLayerCoordinateEquiv (fun x => f ((k.val : Equiv.Perm X)⁻¹ x)) = _
    rw [hk]
    exact F.pairLayerCoordinateEquiv_affine_action 1 (F.bits k) f
  have hp : F.pairLayerCoordinateEquiv
      (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f) =
      (fun j => F.bits k j * F.pairSum f j, 0) := by
    rw [map_sub, hact]
    apply Prod.ext
    · funext j
      change (F.pairZeroRestriction f j + F.bits k j * F.pairSum f j) -
        F.pairZeroRestriction f j = _
      abel
    · funext j
      change F.pairSum f j - F.pairSum f j = 0
      exact sub_self _
  apply Prod.ext
  · change evaluate (fun j => (F.pairLayerCoordinateEquiv
      (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f)).1 (e.symm j)) =
        monomialMultiplier b (evaluate (fun j => F.pairSum f (e.symm j)))
    rw [hp]
    have hm : (fun j => F.bits k (e.symm j) * F.pairSum f (e.symm j)) =
        monomial (support b) * (fun j => F.pairSum f (e.symm j)) := by
      funext j
      rw [hbits]
      rfl
    rw [hm]
    change _ = evaluate (monomial (support b) * evaluate
      (evaluate (fun j => F.pairSum f (e.symm j))))
    rw [evaluate_involutive]
  · change evaluate (fun j => (F.pairLayerCoordinateEquiv
      (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f)).2 (e.symm j)) = 0
    rw [hp]
    exact map_zero evaluate

end SymmetricSubgroupAsymptotics.BinaryPairFrame
