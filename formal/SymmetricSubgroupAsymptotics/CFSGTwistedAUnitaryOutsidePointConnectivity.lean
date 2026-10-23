import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOutsidePointCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryOutsideConnectivity

/-! The checked literal outside-vector paths descend to the original
singular point lines. This is exact projective transport, with no new
building-connectivity or representative-compatibility premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan

def UnitaryRankFourOutsidePointAdjacent (q : CFSG.PrimePower)
    (R S : UnitaryRankFourOutsidePoint q) : Prop :=
  Orthogonal (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) R.val.val S.val.val

private theorem outside_nonzero (q : CFSG.PrimePower) (R : UnitaryRankFourOutside q) : R.val ≠ 0 := by
  intro h
  exact R.property.2 (h ▸ (unitaryRankFourHalf q).zero_mem)

def unitaryRankFourOutsideRay (q : CFSG.PrimePower) (R : UnitaryRankFourOutside q) :
    UnitaryRankFourOutsidePoint q :=
  ⟨singularRay (definingFieldAutomorphism q 2)
    (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4) R.val
    (outside_nonzero q R) R.property.1, by
      intro hle
      exact R.property.2 (hle (Submodule.mem_span_singleton_self _))⟩

def unitaryRankFourOutsideVertex (q : CFSG.PrimePower) (R : UnitaryRankFourOutsidePoint q) :
    UnitaryRankFourOutside q :=
  ⟨unitaryRankFourOutsideVector q R,unitaryRankFourOutsideVector_norm q R,
    unitaryRankFourOutsideVector_outside q R⟩

theorem unitaryRankFourOutsideRay_vertex (q : CFSG.PrimePower) (R : UnitaryRankFourOutsidePoint q) :
    unitaryRankFourOutsideRay q (unitaryRankFourOutsideVertex q R) = R := by
  apply Subtype.ext
  apply Subtype.ext
  exact (unitaryRankFourOutsideVector_span q R).symm

theorem unitaryRankFour_outside_point_connected (q : CFSG.PrimePower)
    (R S : UnitaryRankFourOutsidePoint q) :
    Relation.ReflTransGen (UnitaryRankFourOutsidePointAdjacent q) R S := by
  have he (A B : UnitaryRankFourOutside q) (h : UnitaryRankFourOutsideAdjacent q A B) :
      UnitaryRankFourOutsidePointAdjacent q (unitaryRankFourOutsideRay q A) (unitaryRankFourOutsideRay q B) := by
    apply (orthogonal_iff_singular_representatives (definingFieldAutomorphism q 2)
      (signedReversalUnit (q.Extension 2) 4 : Mat (q.Extension 2) 4)
      (unitaryRankFourOutsideRay q A).val (unitaryRankFourOutsideRay q B).val A.val B.val
      (Submodule.mem_span_singleton_self _) (Submodule.mem_span_singleton_self _)
      (outside_nonzero q A) (outside_nonzero q B)).mpr
    exact h
  have hh := Relation.ReflTransGen.lift (unitaryRankFourOutsideRay q) he
    (unitaryRankFour_outside_connected q (unitaryRankFourOutsideVertex q R) (unitaryRankFourOutsideVertex q S))
  simpa only [unitaryRankFourOutsideRay_vertex] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
