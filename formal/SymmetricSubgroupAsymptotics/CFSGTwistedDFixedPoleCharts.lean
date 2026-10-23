import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedVectorParametrization
import SymmetricSubgroupAsymptotics.CFSGSplitQuadraticPoleCoordinates
import SymmetricSubgroupAsymptotics.CFSGTwistedDTailTwist

/-! Two explicit affine charts in the actual fixed singular cone.
Both retain the full smaller defining-fixed vector as a recoverable
tail, so no projective fibre or orthogonal order formula is needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleCharts
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedDNaturalQuadraticTwist CFSGTwistedDFixedVectorCardinality
open CFSGOrthogonalDIndexBundledQuadratic CFSGSerreOrdinaryTwists
open CFSGSplitQuadraticPoleCoordinates CFSGTwistedDNaturalFork
open CFSGOrthogonalDIndexTailCoordinates

theorem fromCoordinates_fixed (n : ℕ) (q : CFSG.PrimePower)
    (a b : q.Extension 2)
    (ha : definingFieldAutomorphism q 2 a = a)
    (hb : definingFieldAutomorphism q 2 b = b) (w : fixedVectors n q) :
    vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2)
      (fromCoordinates (q.Extension 2) (n + 2) (a, (w.val, b))) =
        fromCoordinates (q.Extension 2) (n + 2) (a, (w.val, b)) := by
  let K := q.Extension 2
  let v := fromCoordinates K (n + 2) (a, (w.val, b))
  have h0 : (0 : Fin (n + 3)) ≠ last (n + 1) := by
    intro h
    have he := congrArg Fin.val h
    change 0 = n + 2 at he
    omega
  apply (coordinateEquiv K (n + 2)).injective
  change coordinates K (n + 2)
    (vectorTwist K (n + 1) (definingFieldAutomorphism q 2) v) =
      coordinates K (n + 2) v
  have hc : coordinates K (n + 2) v = (a, (w.val, b)) := coordinates_from K (n + 2) _
  rw [hc]
  apply Prod.ext
  · change definingFieldAutomorphism q 2
      (v (CFSGOrthogonalDGenerationForkTorus.flip (n + 1) (Sum.inl 0))) = a
    rw [flip_pos, if_neg h0]
    exact ha
  · apply Prod.ext
    · change vectorTwist K (n + 1) (definingFieldAutomorphism q 2) v ∘
        tailIndex (n + 2) = w.val
      rw [← CFSGTwistedDTailTwist.vectorTwist_tail]
      have hv : v ∘ tailIndex (n + 2) = w.val := congrArg (fun z => z.2.1) hc
      rw [hv]
      exact w.property
    · change definingFieldAutomorphism q 2
        (v (CFSGOrthogonalDGenerationForkTorus.flip (n + 1) (Sum.inr 0))) = b
      rw [flip_neg, if_neg h0]
      exact hb

theorem norm_fixed (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    definingFieldAutomorphism q 2 (splitQuadraticForm (q.Extension 2) (n + 2) w.val) =
      splitQuadraticForm (q.Extension 2) (n + 2) w.val := by
  have h := quadratic_covariance (q.Extension 2) n (definingFieldAutomorphism q 2) w.val
  rw [w.property] at h
  exact h.symm

def positiveChart (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    Index (n + 3) → q.Extension 2 :=
  fromCoordinates (q.Extension 2) (n + 2)
    (1, (w.val, -splitQuadraticForm (q.Extension 2) (n + 2) w.val))

def negativeChart (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    Index (n + 3) → q.Extension 2 :=
  fromCoordinates (q.Extension 2) (n + 2)
    (-splitQuadraticForm (q.Extension 2) (n + 2) w.val, (w.val, 1))

theorem positiveChart_fixed (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2)
      (positiveChart n q w) = positiveChart n q w :=
  fromCoordinates_fixed n q _ _ (map_one _) (by rw [map_neg, norm_fixed]) w

theorem negativeChart_fixed (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    vectorTwist (q.Extension 2) (n + 1) (definingFieldAutomorphism q 2)
      (negativeChart n q w) = negativeChart n q w :=
  fromCoordinates_fixed n q _ _ (by rw [map_neg, norm_fixed]) (map_one _) w

theorem positiveChart_singular (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    splitQuadraticForm (q.Extension 2) (n + 3) (positiveChart n q w) = 0 := by
  rw [splitQuadraticForm_apply, splitQ_coordinates]
  simp only [positiveChart, coordinates_from, CFSGQuadraticHyperbolicShear.norm,
    one_mul, neg_add_cancel]

theorem negativeChart_singular (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    splitQuadraticForm (q.Extension 2) (n + 3) (negativeChart n q w) = 0 := by
  rw [splitQuadraticForm_apply, splitQ_coordinates]
  simp only [negativeChart, coordinates_from, CFSGQuadraticHyperbolicShear.norm,
    mul_one, neg_add_cancel]

theorem positiveChart_first (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    positiveChart n q w (Sum.inl 0) = 1 := rfl

theorem negativeChart_last (n : ℕ) (q : CFSG.PrimePower) (w : fixedVectors n q) :
    negativeChart n q w (Sum.inr 0) = 1 := rfl

theorem positiveChart_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (positiveChart n q) := by
  intro w z h
  apply Subtype.ext
  have he := congrArg (fun v : Index (n + 3) → q.Extension 2 =>
    (coordinates (q.Extension 2) (n + 2) v).2.1) h
  simpa only [positiveChart, coordinates_from] using he

theorem negativeChart_injective (n : ℕ) (q : CFSG.PrimePower) :
    Function.Injective (negativeChart n q) := by
  intro w z h
  apply Subtype.ext
  have he := congrArg (fun v : Index (n + 3) → q.Extension 2 =>
    (coordinates (q.Extension 2) (n + 2) v).2.1) h
  simpa only [negativeChart, coordinates_from] using he

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedPoleCharts
