import SymmetricSubgroupAsymptotics.BinaryPairPolynomialPermutationDifference
import SymmetricSubgroupAsymptotics.BinaryCommonEightExtraShearLeading

/-! The additional original top shear acts triangularly on the same two
polynomial layers. Its lift error is arbitrary and never discarded. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
namespace BinaryBooleanFourPolynomialCoordinates
open BinaryCommonEightExtraShearLeading

theorem permutationDifference_extraShear :
    permutationDifference booleanPermutation = operator := by
  exact actualDifference_eq_operator

theorem triangularExtraShear_upper (a : Fin 16) (z s : V)
    (E : V →ₗ[ZMod 2] V)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a))
    (hodd : a.val % 2 = 1) (hsmall : a.val < 8) :
    FiniteRowLeadingWeight.HasLeading
      (Fin.append (operator z + E s) (operator s))
      (Fin.natAdd 16 (target a)) := by
  apply (TwoLayerLeadingTerms.upper_iff _ _ _).mpr
  exact operator_hasLeading s a ((TwoLayerLeadingTerms.upper_iff _ _ _).mp hv) hodd hsmall

theorem triangularExtraShear_lower (a : Fin 16) (z s : V)
    (E : V →ₗ[ZMod 2] V)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.castAdd 16 a))
    (hodd : a.val % 2 = 1) (hsmall : a.val < 8) :
    FiniteRowLeadingWeight.HasLeading
      (Fin.append (operator z + E s) (operator s))
      (Fin.castAdd 16 (target a)) := by
  obtain ⟨hz, hs⟩ := (TwoLayerLeadingTerms.lower_iff _ _ _).mp hv
  rw [hs, map_zero, map_zero, add_zero]
  apply (TwoLayerLeadingTerms.lower_iff _ _ _).mpr
  exact ⟨operator_hasLeading z a hz hodd hsmall, rfl⟩

end BinaryBooleanFourPolynomialCoordinates

namespace BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates BinaryCommonEightExtraShearLeading
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 16))

theorem polynomialPairCoordinate_extra_shear_difference
    (e : Equiv.Perm (Fin 16)) (u : U)
    (hu : ∀ j, (F.top u)⁻¹ (e.symm j) = e.symm (booleanPermutation.symm j))
    (f : X → ZMod 2) :
    F.polynomialPairCoordinateEquiv e
      (permutationFunctionRepresentation (ZMod 2) U X u f - f) =
      (operator (F.polynomialPairCoordinateEquiv e f).1 +
        permutationOffsetError (F.polynomialLiftOffset e u) booleanPermutation
          (F.polynomialPairCoordinateEquiv e f).2,
        operator (F.polynomialPairCoordinateEquiv e f).2) := by
  rw [F.polynomialPairCoordinate_permutation_difference e booleanPermutation u hu f,
    permutationDifference_extraShear]

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
