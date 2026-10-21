import SymmetricSubgroupAsymptotics.BinaryPairPolynomialKernelShears
import SymmetricSubgroupAsymptotics.BinaryBooleanFourGeneralLeadingProducts

/-! Actual polynomial kernel vectors act by pointwise multiplication,
including all their original lower terms. No pure monomial is substituted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 16))

theorem polynomialPairCoordinate_general_kernel_difference
    (e : Equiv.Perm (Fin 16)) (k : F.top.ker) (a : V)
    (hbits : ∀ j, F.bits k (e.symm j) = evaluate a j)
    (f : X → ZMod 2) :
    F.polynomialPairCoordinateEquiv e
      (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f) =
      (polynomialMultiply a (F.polynomialPairCoordinateEquiv e f).2, 0) := by
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
        polynomialMultiply a (evaluate (fun j => F.pairSum f (e.symm j)))
    rw [hp]
    have hm : (fun j => F.bits k (e.symm j) * F.pairSum f (e.symm j)) =
        evaluate a * (fun j => F.pairSum f (e.symm j)) := by
      funext j
      rw [hbits]
      rfl
    rw [hm]
    change _ = evaluate (evaluate a * evaluate
      (evaluate (fun j => F.pairSum f (e.symm j))))
    rw [evaluate_involutive]
  · change evaluate (fun j => (F.pairLayerCoordinateEquiv
      (permutationFunctionRepresentation (ZMod 2) U X (k : U) f - f)).2 (e.symm j)) = 0
    rw [hp]
    exact map_zero evaluate

end SymmetricSubgroupAsymptotics.BinaryPairFrame

namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth

private theorem unionIndex_comm : ∀ a b : Fin 16,
    unionIndex a b = unionIndex b a := by decide

theorem kernelGeneralShear_hasLeading (f z s : V) (c a : Fin 16)
    (hf : FiniteRowLeadingWeight.HasLeading f c)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a))
    (hdisj : Disjoint (support c) (support a)) :
    FiniteRowLeadingWeight.HasLeading
      (Fin.append (polynomialMultiply f s) (0 : V))
      (Fin.castAdd 16 (unionIndex c a)) := by
  apply (TwoLayerLeadingTerms.lower_iff _ _ _).mpr
  have hprod := polynomialMultiply_hasLeading f s c a hf
    ((TwoLayerLeadingTerms.upper_iff _ _ _).mp hv) hdisj.symm
  rw [unionIndex_comm a c] at hprod
  exact ⟨hprod, rfl⟩

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
