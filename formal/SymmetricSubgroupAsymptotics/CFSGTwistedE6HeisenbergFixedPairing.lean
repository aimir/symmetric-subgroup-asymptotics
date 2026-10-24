import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergTwistCompatibility
import SymmetricSubgroupAsymptotics.CFSGQuadraticSignedFixedCoordinates

/-! The descended Heisenberg cocycle has the SAME central sign as the
actual matrix twist.  Its two weights are coupled by the actual group
law, not chosen independently.  Fixed vector coordinates therefore
pair into the literal signed fixed central line. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergFixedPairing
open CFSGHeisenbergCoordinateGroup CFSGCommutingParameterTwist
open CFSGTwistedE6HeisenbergStableRootFamilies CFSGTwistedE6HeisenbergCoordinateTwist
open CFSGTwistedE6HeisenbergTwistCompatibility CFSGQuadraticSignedFixedCoordinates
open CFSGSerreOrdinaryTwists

theorem dot_twist (K : Type) [Field K] (sigma : K ≃+* K) (b a : Fin 10 → K) :
    dot (coefficientMap sigma partner secondWeight b)
        (coefficientMap sigma partner firstWeight a) =
      (centralWeight : K) * sigma (dot b a) := by
  have hh := congrArg (fun z : Element K 10 => z.c)
    (coordinateTwist_mul K sigma (⟨0, b, 0⟩ : Element K 10) (⟨a, 0, 0⟩ : Element K 10))
  change (centralWeight : K) * sigma (0 + 0 + dot b a) =
    (centralWeight : K) * sigma 0 + (centralWeight : K) * sigma 0 +
      dot (coefficientMap sigma partner secondWeight b)
        (coefficientMap sigma partner firstWeight a) at hh
  simpa only [zero_add, map_zero, mul_zero] using hh.symm

private theorem dot_single {K : Type} [CommRing K] (i : Fin 10) (a b : K) :
    dot (Pi.single i b) (Pi.single i a) = b * a := by
  simp [dot, Pi.single_apply, mul_ite, ite_mul]

theorem weight_pair_product (K : Type) [Field K] (i : Fin 10) :
    (secondWeight i : K) * (firstWeight i : K) = (centralWeight : K) := by
  have hh := dot_twist K (RingEquiv.refl K) (Pi.single i 1) (Pi.single i 1)
  simpa only [coefficientMap_single, RingEquiv.refl_apply, mul_one, dot_single] using hh

private theorem scalar_flip {K : Type*} [CommRing K] {s x y : K}
    (hs : s * s = 1) (h : x = s * y) : y = s * x := by
  calc
    y = (s * s) * y := by rw [hs, one_mul]
    _ = s * (s * y) := mul_assoc _ _ _
    _ = s * x := congrArg (fun z => s * z) h.symm

theorem dot_signed_fixed (q : CFSG.PrimePower) (b a : Fin 10 → q.Extension 2)
    (hb : coefficientMap (definingFieldAutomorphism q 2) partner secondWeight b = b)
    (ha : coefficientMap (definingFieldAutomorphism q 2) partner firstWeight a = a) :
    dot b a ∈ signedLine q centralWeight := by
  have hh := dot_twist (q.Extension 2) (definingFieldAutomorphism q 2) b a
  rw [hb, ha] at hh
  have hs : (centralWeight : q.Extension 2) * (centralWeight : q.Extension 2) = 1 := by
    rcases centralWeight_unit with h | h <;> simp only [h, Int.cast_one, Int.cast_neg] <;> ring
  exact scalar_flip hs hh

end SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergFixedPairing
