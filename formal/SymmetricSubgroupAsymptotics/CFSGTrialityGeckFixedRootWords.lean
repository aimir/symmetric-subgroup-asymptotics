import SymmetricSubgroupAsymptotics.CFSGTrialityGeckRootSubgroupTwist
import SymmetricSubgroupAsymptotics.CFSGTrialityTripleFixedRoots
import SymmetricSubgroupAsymptotics.CFSGNormTwoGeckOrthogonalWeyl

/-! Explicit fixed natural root and Weyl words for actual triality.
The three-root orbit retains all cubic-extension parameters. Fixedness
is proved from the literal diagram--field formula and orthogonal root
commutation, not a fixed-class lifting assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootWords
open CFSGTrialityD4NormTwo CFSGTrialityGeckDiagramCovariance
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord
open CFSGTrialityGeckMatrixTwist CFSGTrialityGeckRootSubgroupTwist
open CFSGNormTwoGeckOrthogonalWeyl CFSGSerreOrdinaryTwists

private theorem cartan_zero (i j : Fin 4) (h : CartanMatrix.D 4 i j = 0) :
    CFSGGeckSerreRepresentation.cartan Base Index i j = 0 := by
  rw [CFSGTrialityD4NormTwo.cartan_eq]
  exact h

def shortWeyl (K : Type) [CommRing K] := canonicalWord rawData K [0,2,3]
def longWeyl (K : Type) [CommRing K] := canonicalWord rawData K [1]

theorem shortWeyl_fixed (K : Type) [CommRing K] (σ : K ≃+* K) :
    unitTwist K σ (shortWeyl K) = shortWeyl K := by
  rw [shortWeyl, unitTwist_word]
  change canonicalWeyl rawData K 2 * (canonicalWeyl rawData K 3 *
      (canonicalWeyl rawData K 0 * 1)) =
    canonicalWeyl rawData K 0 * (canonicalWeyl rawData K 2 *
      (canonicalWeyl rawData K 3 * 1))
  have hc₂ := orthogonal_weyls (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 0 2 (cartan_zero 0 2 (by decide))
  have hc₃ := orthogonal_weyls (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 0 3 (cartan_zero 0 3 (by decide))
  simpa only [mul_one, mul_assoc] using (hc₂.mul_right hc₃).eq.symm

theorem longWeyl_fixed (K : Type) [CommRing K] (σ : K ≃+* K) :
    unitTwist K σ (longWeyl K) = longWeyl K := by
  rw [longWeyl, unitTwist_word]
  rfl

def shortOrbit (K : Type) [CommRing K] (σ : K ≃+* K) (neg : Bool) (t : K) :=
  canonicalRoot rawData K neg 0 t * canonicalRoot rawData K neg 2 (σ t) *
    canonicalRoot rawData K neg 3 (σ (σ t))

theorem shortOrbit_fixed (K : Type) [CommRing K] (σ : K ≃+* K)
    (neg : Bool) (t : K) (ht : σ (σ (σ t)) = t) :
    unitTwist K σ (shortOrbit K σ neg t) = shortOrbit K σ neg t := by
  simp only [shortOrbit, map_mul, unitTwist_raw_root]
  change canonicalRoot rawData K neg 2 (σ t) *
      canonicalRoot rawData K neg 3 (σ (σ t)) *
      canonicalRoot rawData K neg 0 (σ (σ (σ t))) = _
  rw [ht]
  have hc₂ := orthogonal_signed_roots (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 0 2 (cartan_zero 0 2 (by decide)) neg neg t (σ t)
  have hc₃ := orthogonal_signed_roots (CartanMatrix.D 4) (CartanMatrix.D_transpose 4)
    D4_positive_definite Base Index K 0 3 (cartan_zero 0 3 (by decide)) neg neg t (σ (σ t))
  simpa only [mul_assoc] using (hc₂.mul_right hc₃).eq.symm

theorem actual_shortOrbit_fixed (q : CFSG.PrimePower) (neg : Bool) (t : q.Extension 3) :
    unitTwist (q.Extension 3) (definingFieldAutomorphism q 3)
      (shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg t) =
        shortOrbit (q.Extension 3) (definingFieldAutomorphism q 3) neg t :=
  shortOrbit_fixed _ _ neg t (CFSGTrialityTripleFixedRoots.extension_three_pow_thrice q t)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedRootWords
