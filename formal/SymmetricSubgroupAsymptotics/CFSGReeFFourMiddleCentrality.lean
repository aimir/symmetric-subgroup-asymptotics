import SymmetricSubgroupAsymptotics.CFSGFFourOriginalMiddleLongCentrality
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleRootCovariance

/-! Centrality of both higher middle factors in the literal Ree field.
The short factor is transported by the checked original exceptional
automorphism; no root-characteristic cancellation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleCentrality
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourOriginalMiddleWords CFSGFFourOriginalMiddleLongCentrality
open CFSGReeFFourFieldParameters CFSGReeFFourOriginalAutomorphism
open CFSGReeFFourMiddleRootCovariance CFSGE6GeckMiddleAThreeCollecting
open CFSGTwistedE6GeckDiagramCovariance
local notation "A" => CartanMatrix.F₄

theorem middleShort_commute_one (m : ℕ) (r t : Field m) :
    Commute (middleShort (Field m) r) (modelRoot A (Field m) false 1 t) := by
  have h := (middleLong_commute_two (Field m) (alpha m r) (alpha m t)).map
    (reeAutomorphism m)
  rw [middleLong_twist,reeAutomorphism_root] at h
  change Commute (middleShort (Field m) (beta m (alpha m r)))
    (modelRoot A (Field m) false 1 (beta m (alpha m t))) at h
  simpa only [beta_alpha] using h

theorem middleShort_commute_two (m : ℕ) (r t : Field m) :
    Commute (middleShort (Field m) r) (modelRoot A (Field m) false 2 t) := by
  have h := (middleLong_commute_one (Field m) (alpha m r) (beta m t)).map
    (reeAutomorphism m)
  rw [middleLong_twist,reeAutomorphism_root] at h
  change Commute (middleShort (Field m) (beta m (alpha m r)))
    (modelRoot A (Field m) false 2 (alpha m (beta m t))) at h
  simpa only [beta_alpha,alpha_beta] using h

private theorem long_same_line (K : Type) [Field K] [Finite K] [CharP K 2] (r s : K) :
    Commute (middleLong K r) (middleLong K s) := by
  apply Commute.of_map (rawHom_injective K)
  rw [rawHom_middleLong,rawHom_middleLong]
  have h := (Commute.all (Multiplicative.ofAdd r) (Multiplicative.ofAdd s)).map
    (CFSGE6GeckSignedSimpleParameters.rawSimpleHom K false 3)
  exact h.map (MulAut.conj (canonicalWeyl rawData K 2*canonicalWeyl rawData K 4))

theorem middleLong_commute_middleShort (m : ℕ) (r s : Field m) :
    Commute (middleLong (Field m) r) (middleShort (Field m) s) := by
  have hx := middleLong_commute_one (Field m) r 1
  have hy := middleLong_commute_two (Field m) r s
  have hc := ((hx.mul_right hy).mul_right hx.inv_right).mul_right hy.inv_right
  change Commute (middleLong (Field m) r)
    ⁅modelRoot A (Field m) false 1 1,modelRoot A (Field m) false 2 s⁆ at hc
  rw [CFSGFFourOriginalMiddleWords.middle_commutator] at hc
  simp only [one_pow,one_mul] at hc
  have hp := (long_same_line (Field m) r s).inv_right.mul_right hc
  simpa only [inv_mul_cancel_left] using hp

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleCentrality
