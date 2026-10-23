import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddOutsidePointCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOddOutsideConnectivity

/-! Uniform odd-dimensional reconstruction in the literal signed unitary coordinates. The finite field may have order two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

def UnitaryOddOutsidePointAdjacent (q : CFSG.PrimePower) (m : ℕ)
    (R S : UnitaryOddOutsidePoint q m) : Prop :=
  Orthogonal (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) R.val.val S.val.val

private theorem outside_nonzero (q : CFSG.PrimePower) (m : ℕ) (R : UnitaryOddOutside q m) : R.val ≠ 0 := by
  intro h
  exact R.property.2 (h ▸ (unitaryOddHalf q m).zero_mem)

def unitaryOddOutsideRay (q : CFSG.PrimePower) (m : ℕ) (R : UnitaryOddOutside q m) :
    UnitaryOddOutsidePoint q m :=
  ⟨singularRay (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4)) R.val
    (outside_nonzero q m R) R.property.1, by
      intro hle
      exact R.property.2 (hle (Submodule.mem_span_singleton_self _))⟩

def unitaryOddOutsideVertex (q : CFSG.PrimePower) (m : ℕ) (R : UnitaryOddOutsidePoint q m) :
    UnitaryOddOutside q m :=
  ⟨unitaryOddOutsideVector q m R,unitaryOddOutsideVector_norm q m R,
    unitaryOddOutsideVector_outside q m R⟩

theorem unitaryOddOutsideRay_vertex (q : CFSG.PrimePower) (m : ℕ) (R : UnitaryOddOutsidePoint q m) :
    unitaryOddOutsideRay q m (unitaryOddOutsideVertex q m R) = R := by
  apply Subtype.ext
  apply Subtype.ext
  exact (unitaryOddOutsideVector_span q m R).symm

theorem unitaryOdd_outside_point_connected (q : CFSG.PrimePower) (m : ℕ)
    (R S : UnitaryOddOutsidePoint q m) :
    Relation.ReflTransGen (UnitaryOddOutsidePointAdjacent q m) R S := by
  have he (A B : UnitaryOddOutside q m) (h : UnitaryOddOutsideAdjacent q m A B) :
      UnitaryOddOutsidePointAdjacent q m (unitaryOddOutsideRay q m A) (unitaryOddOutsideRay q m B) := by
    apply (orthogonal_iff_singular_representatives (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) (2*m+4) : Mat (q.Extension 2) (2*m+4))
      (unitaryOddOutsideRay q m A).val (unitaryOddOutsideRay q m B).val A.val B.val
      (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)
      (outside_nonzero q m A) (outside_nonzero q m B)).mpr
    exact h
  have hh := Relation.ReflTransGen.lift (unitaryOddOutsideRay q m) he
    (unitaryOdd_outside_connected q m (unitaryOddOutsideVertex q m R) (unitaryOddOutsideVertex q m S))
  simpa only [unitaryOddOutsideRay_vertex] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
