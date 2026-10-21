import SymmetricSubgroupAsymptotics.BinaryBooleanFourLeadingProducts
import SymmetricSubgroupAsymptotics.TwoLayerLeadingTerms

/-! Leading behavior of the actual triangular two-layer operators.
The lower-error map E is arbitrary. It records the offset of a genuine
lift of a top translation, rather than imposing a zero-offset lift. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates

open BinaryElementaryPairMonomialWidth

theorem triangularDerivative_upper (i : Fin 4) (a : Fin 16) (z s : V)
    (E : V →ₗ[ZMod 2] V)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a))
    (hi : i ∈ support a) :
    FiniteRowLeadingWeight.HasLeading
      (Fin.append (derivative i z + E s) (derivative i s))
      (Fin.natAdd 16 (removeIndex i a)) := by
  apply (TwoLayerLeadingTerms.upper_iff _ _ _).mpr
  exact derivative_hasLeading i a s ((TwoLayerLeadingTerms.upper_iff _ _ _).mp hv) hi

theorem triangularDerivative_lower (i : Fin 4) (a : Fin 16) (z s : V)
    (E : V →ₗ[ZMod 2] V)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.castAdd 16 a))
    (hi : i ∈ support a) :
    FiniteRowLeadingWeight.HasLeading
      (Fin.append (derivative i z + E s) (derivative i s))
      (Fin.castAdd 16 (removeIndex i a)) := by
  obtain ⟨hz, hs⟩ := (TwoLayerLeadingTerms.lower_iff _ _ _).mp hv
  rw [hs, map_zero, map_zero, add_zero]
  apply (TwoLayerLeadingTerms.lower_iff _ _ _).mpr
  exact ⟨derivative_hasLeading i a z hz hi, rfl⟩

/-- A kernel shear minus the identity kills the entire original lower
component. Its surviving component is pointwise monomial multiplication. -/
theorem kernelShear_hasLeading (b a : Fin 16) (z s : V)
    (hv : FiniteRowLeadingWeight.HasLeading (Fin.append z s) (Fin.natAdd 16 a))
    (hdisj : Disjoint (support b) (support a)) :
    FiniteRowLeadingWeight.HasLeading
      (Fin.append (monomialMultiplier b s) (0 : V))
      (Fin.castAdd 16 (unionIndex b a)) := by
  apply (TwoLayerLeadingTerms.lower_iff _ _ _).mpr
  exact ⟨monomialMultiplier_hasLeading b a s
    ((TwoLayerLeadingTerms.upper_iff _ _ _).mp hv) hdisj, rfl⟩

end SymmetricSubgroupAsymptotics.BinaryBooleanFourPolynomialCoordinates
