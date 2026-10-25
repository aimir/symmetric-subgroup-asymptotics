import SymmetricSubgroupAsymptotics.CFSGTwistedAUnitaryPairReciprocity
import SymmetricSubgroupAsymptotics.CFSGTwistedAQuadraticTrace
import SymmetricSubgroupAsymptotics.CFSGHermitianMatrixPullback

/-! One scalar normalization works for the literal signed reversal in
EVERY rank and characteristic. A nonzero skew element t gives c=t^r;
the two signs in sigma(c)*(-1)^r cancel without any division by two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGUnitarySignedHermitianNormalization
open CFSGTwistedANaturalMatrices CFSGSerreOrdinaryTwists
open CFSGTwistedAUnitaryParameters CFSGTwistedAUnitaryCoordinates

theorem exists_scalar_reciprocal (q : CFSG.PrimePower) (r : ℕ) :
    ∃ c : q.Extension 2, c ≠ 0 ∧
      ∀ x y : Fin (r+1) → q.Extension 2,
        definingFieldAutomorphism q 2
          (hermitianPair (definingFieldAutomorphism q 2)
            (c • (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)) x y)=
        hermitianPair (definingFieldAutomorphism q 2)
          (c • (signedReversalUnit (q.Extension 2) r : Mat (q.Extension 2) r)) y x := by
  obtain ⟨t,ht,hts⟩ := CFSGTwistedAQuadraticTrace.exists_skew_nonzero q
  let c := t^r
  have hcs : definingFieldAutomorphism q 2 c*((-1 : q.Extension 2)^r)=c := by
    change definingFieldAutomorphism q 2 (t^r)*((-1 : q.Extension 2)^r)=t^r
    rw [map_pow,hts,←mul_pow]
    simp only [neg_mul_neg,mul_one]
  have hrec (x y : Fin (r+1) → q.Extension 2) :
      definingFieldAutomorphism q 2 (unitaryNaturalPair q r x y)=
        ((-1 : q.Extension 2)^r)*unitaryNaturalPair q r y x := by
    have hh := congrArg (definingFieldAutomorphism q 2)
      (unitaryNaturalPair_signed_reciprocal q r x y)
    have hs : definingFieldAutomorphism q 2
        (definingFieldAutomorphism q 2 (unitaryNaturalPair q r y x))=
        unitaryNaturalPair q r y x := extension_two_pow_twice q _
    rw [map_mul,map_pow,map_neg,map_one,hs] at hh
    exact hh
  refine ⟨c,pow_ne_zero r ht,?_⟩
  intro x y
  rw [CFSGHermitianMatrixPullback.scalar_form,
    CFSGHermitianMatrixPullback.scalar_form,map_mul]
  change definingFieldAutomorphism q 2 c*
    definingFieldAutomorphism q 2 (unitaryNaturalPair q r x y)=c*unitaryNaturalPair q r y x
  rw [hrec,←mul_assoc,hcs]

end SymmetricSubgroupAsymptotics.CFSGUnitarySignedHermitianNormalization
