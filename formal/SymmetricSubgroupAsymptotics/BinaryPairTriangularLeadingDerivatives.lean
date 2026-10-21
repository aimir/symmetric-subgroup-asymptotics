import SymmetricSubgroupAsymptotics.BinaryTriangularPolynomialRepresentation
import SymmetricSubgroupAsymptotics.BinaryMonomialRaisingWords

/-! Actual triangular top flips give leading derivatives in either
layer of the original pair action. Arbitrary original lift offsets stay
below the upper layer and vanish when that layer is zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
open BinaryElementaryPairMonomialWidth

theorem triangularLeadingDerivative_upper
    (D E : V →ₗ[ZMod 2] V) (i : Fin 4)
    (hD : ∀ v a, FiniteRowLeadingWeight.HasLeading v a → i ∈ support a →
      FiniteRowLeadingWeight.HasLeading (D v) (removeIndex i a))
    (a : Fin 16) (z s : V)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a))
    (hi : i ∈ support a) :
    FiniteRowLeadingWeight.HasLeading (Fin.append (D z + E s) (D s))
      (Fin.natAdd 16 (removeIndex i a)) := by
  apply (TwoLayerLeadingTerms.upper_iff _ _ _).mpr
  exact hD s a ((TwoLayerLeadingTerms.upper_iff _ _ _).mp hv) hi

theorem triangularLeadingDerivative_lower
    (D E : V →ₗ[ZMod 2] V) (i : Fin 4)
    (hD : ∀ v a, FiniteRowLeadingWeight.HasLeading v a → i ∈ support a →
      FiniteRowLeadingWeight.HasLeading (D v) (removeIndex i a))
    (a : Fin 16) (z s : V)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.castAdd 16 a))
    (hi : i ∈ support a) :
    FiniteRowLeadingWeight.HasLeading (Fin.append (D z + E s) (D s))
      (Fin.castAdd 16 (removeIndex i a)) := by
  obtain ⟨hz, hs⟩ := (TwoLayerLeadingTerms.lower_iff _ _ _).mp hv
  rw [hs, map_zero, map_zero, add_zero]
  apply (TwoLayerLeadingTerms.lower_iff _ _ _).mpr
  exact ⟨hD z a hz hi, rfl⟩

end BinaryBooleanFourPolynomialCoordinates
namespace BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
open BinaryMonomialRaisingWords (index)
variable {X : Type} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin 16))
    (T : BinaryTriangularPointCoordinates F.top.range (Fin 16) 4)

theorem exists_actual_pair_leading_derivative (i : Fin 4) :
    ∃ u : U, ∀ (f : X → ZMod 2) (l : Bool) (a : Fin 16),
      FiniteRowLeadingWeight.HasLeading
        (pairLayerFlatten (F.polynomialPairCoordinateEquiv T.booleanPointLabels f)) (index (l, a)) →
      i ∈ support a →
      FiniteRowLeadingWeight.HasLeading
        (pairLayerFlatten (F.polynomialPairCoordinateEquiv T.booleanPointLabels
          (permutationFunctionRepresentation (ZMod 2) U X u f - f)))
        (index (l, removeIndex i a)) := by
  obtain ⟨g, hg⟩ := T.exists_actualBooleanPermutation_flip i
  obtain ⟨u, hu⟩ := F.top.rangeRestrict_surjective g⁻¹
  have htop : F.top u = (g⁻¹).val := congrArg Subtype.val hu
  have hp : ∀ j, (F.top u)⁻¹ (T.booleanPointLabels.symm j) =
      T.booleanPointLabels.symm ((T.actualBooleanPermutation g).symm.symm j) := by
    intro j
    rw [htop]
    change ((g.val)⁻¹)⁻¹ (T.booleanPointLabels.symm j) =
      T.booleanPointLabels.symm (T.booleanPointLabels (g.val (T.booleanPointLabels.symm j)))
    rw [inv_inv, Equiv.symm_apply_apply]
  refine ⟨u, ?_⟩
  intro f l a hv hi
  rw [F.polynomialPairCoordinate_permutation_difference T.booleanPointLabels
    (T.actualBooleanPermutation g).symm u hp f]
  have hD : ∀ v a, FiniteRowLeadingWeight.HasLeading v a → i ∈ support a →
      FiniteRowLeadingWeight.HasLeading
        (permutationDifference (T.actualBooleanPermutation g).symm v) (removeIndex i a) :=
    fun v a hv hi => triangular_permutation_difference_hasLeading (T.actualBooleanPermutation g)
      (T.actualBooleanPermutation_triangular g) i hg v a hv hi
  cases l
  · exact triangularLeadingDerivative_lower _ _ i hD a _ _ hv hi
  · exact triangularLeadingDerivative_upper _ _ i hD a _ _ hv hi

end BinaryPairFrame
end SymmetricSubgroupAsymptotics
