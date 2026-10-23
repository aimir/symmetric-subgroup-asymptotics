import SymmetricSubgroupAsymptotics.CFSGOrderedCubeOperatorExpansion
import SymmetricSubgroupAsymptotics.CFSGCubicNormCurveSpan

/-! A cubic Frobenius-parameter orbit spans all eight ordered tensor
words over the extension field; its differences span the seven raised
words. The passage to a particular fixed group and its base field is
deliberately separate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrderedCubeNormOrbitSpan
open CFSGOrderedCubeOperatorExpansion CFSGCubicNormMonomialSeparation CFSGCubicNormCurveSpan
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem ordered_orbit_span [Finite K] (N0 N1 N2 : V →ₗ[K] V) (v : V)
    (q : ℕ) (hq : 2 ≤ q) (hcard : Nat.card K = q^3) :
    Submodule.span K (Set.range (fun t : K => orderedAction N0 N1 N2 v t (t^q) (t^(q^2)))) =
      Submodule.span K (Set.range (tensorWord N0 N1 N2 v)) := by
  have hfun : (fun t : K => orderedAction N0 N1 N2 v t (t^q) (t^(q^2))) =
      tensorMap N0 N1 N2 v ∘ normCurve q := by
    funext t
    exact orderedAction_normCurve N0 N1 N2 v q t
  rw [hfun, Set.range_comp, Submodule.span_image, normCurve_span_eq_top K q hq hcard,
    Submodule.map_top]
  exact Fintype.range_linearCombination K (tensorWord N0 N1 N2 v)

def augmentationMap (N0 N1 N2 : V →ₗ[K] V) (v : V) : (Fin 7 → K) →ₗ[K] V :=
  Fintype.linearCombination K (fun i : Fin 7 => tensorWord N0 N1 N2 v i.succ)

theorem orderedAction_sub_initial (N0 N1 N2 : V →ₗ[K] V) (v : V)
    (q : ℕ) (hq : 2 ≤ q) (t : K) :
    orderedAction N0 N1 N2 v t (t^q) (t^(q^2)) - v =
      augmentationMap N0 N1 N2 v (augmentationCurve q t) := by
  rw [orderedAction_normCurve]
  change (∑ i : Fin 8, normCurve q t i • tensorWord N0 N1 N2 v i) - v =
    ∑ i : Fin 7, augmentationCurve q t i • tensorWord N0 N1 N2 v i.succ
  rw [Fin.sum_univ_succ]
  have h0 : normCurve q t 0 = 1 := by simp [normCurve, exponent]
  simp only [h0, one_smul, augmentationCurve, normCurve_zero_succ K q hq, sub_zero]
  change (v + _) - v = _
  module

theorem ordered_orbit_difference_span [Finite K] (N0 N1 N2 : V →ₗ[K] V) (v : V)
    (q : ℕ) (hq : 2 ≤ q) (hcard : Nat.card K = q^3) :
    Submodule.span K
      (Set.range (fun t : K => orderedAction N0 N1 N2 v t (t^q) (t^(q^2)) - v)) =
        Submodule.span K (Set.range (fun i : Fin 7 => tensorWord N0 N1 N2 v i.succ)) := by
  have hfun : (fun t : K => orderedAction N0 N1 N2 v t (t^q) (t^(q^2)) - v) =
      augmentationMap N0 N1 N2 v ∘ augmentationCurve q := by
    funext t
    exact orderedAction_sub_initial N0 N1 N2 v q hq t
  rw [hfun, Set.range_comp, Submodule.span_image, augmentationCurve_span_eq_top K q hq hcard,
    Submodule.map_top]
  exact Fintype.range_linearCombination K (fun i : Fin 7 => tensorWord N0 N1 N2 v i.succ)

end SymmetricSubgroupAsymptotics.CFSGOrderedCubeNormOrbitSpan
