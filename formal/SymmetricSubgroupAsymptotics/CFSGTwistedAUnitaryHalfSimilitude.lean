import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryHalfScale
import SymmetricSubgroupAsymptotics.CFSGHermitianSimilitudeLocalAction

/-! The literal half-scaling equivalence belongs to the actual signed
similitude subgroup. Its action fixes both original opposed point sets
and has the displayed strong-mixed ray formula. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists CFSGHermitianOrthogonalSpan
open CFSGHermitianSimilitudeGroup

def unitaryHalfSimilitude (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htf : definingFieldAutomorphism q 2 t = t)
    (hun : definingFieldAutomorphism q 2 u * u = t) :
    similitudes (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r) :=
  ⟨unitaryHalfScaleEquiv q r t u ht hu,t,ht,unitaryHalfScale_pair q r t u htf hun⟩

theorem unitaryHalfSimilitude_fix_standard_point (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htf : definingFieldAutomorphism q 2 t = t)
    (hun : definingFieldAutomorphism q 2 u * u = t)
    (P : SingularPoint (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r))
    (hP : P.val ≤ unitaryStandardSingularSpace q r) :
    singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r)
      (unitaryHalfSimilitude q r t u ht hu htf hun) P = P := by
  apply Subtype.ext
  rw [singularPointHom_val]
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    change unitaryHalfScale q r t u y ∈ P.val
    simpa only [unitaryHalfScale_fix_standard q r t u y (hP hy)] using hy
  · intro x hx
    refine ⟨x,hx,?_⟩
    exact unitaryHalfScale_fix_standard q r t u x (hP hx)

theorem unitaryHalfSimilitude_fix_opposite_point (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htf : definingFieldAutomorphism q 2 t = t)
    (hun : definingFieldAutomorphism q 2 u * u = t)
    (P : SingularPoint (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r))
    (hP : P.val ≤ unitaryOppositeSingularSpace q r) :
    singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r)
      (unitaryHalfSimilitude q r t u ht hu htf hun) P = P := by
  apply Subtype.ext
  rw [singularPointHom_val]
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    change unitaryHalfScale q r t u y ∈ P.val
    rw [unitaryHalfScale_scale_opposite q r t u y (hP hy)]
    exact P.val.smul_mem t hy
  · intro x hx
    refine ⟨t⁻¹ • x,P.val.smul_mem _ hx,?_⟩
    change unitaryHalfScale q r t u (t⁻¹ • x) = x
    rw [unitaryHalfScale_scale_opposite q r t u _
      ((unitaryOppositeSingularSpace q r).smul_mem _ (hP hx)),smul_smul,mul_inv_cancel₀ ht,one_smul]

theorem unitaryHalfSimilitude_mixed_point (q : CFSG.PrimePower) (r : ℕ) (t u : q.Extension 2)
    (ht : t ≠ 0) (hu : u ≠ 0) (htf : definingFieldAutomorphism q 2 t = t)
    (hun : definingFieldAutomorphism q 2 u * u = t)
    (x y : Fin (r+1) → q.Extension 2) (hx : x ∈ unitaryStandardSingularSpace q r)
    (hy : y ∈ unitaryOppositeSingularSpace q r)
    (P : SingularPoint (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r))
    (hP : P.val = (q.Extension 2) ∙ (x+y)) :
    (singularPointHom (definingFieldAutomorphism q 2) (signedReversalUnit (q.Extension 2) r)
      (unitaryHalfSimilitude q r t u ht hu htf hun) P).val = (q.Extension 2) ∙ (x+t • y) := by
  rw [singularPointHom_val,hP,Submodule.map_span,Set.image_singleton]
  change (q.Extension 2) ∙ unitaryHalfScale q r t u (x+y) = _
  rw [map_add,unitaryHalfScale_fix_standard q r t u x hx,unitaryHalfScale_scale_opposite q r t u y hy]

end SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryCoordinates
