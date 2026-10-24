import SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergCoordinateTwist
import SymmetricSubgroupAsymptotics.CFSGDiagramFieldTwistInvolution

/-! Compatibility of the literal Heisenberg coordinate twist is derived
from its actual faithful matrix realization.  In particular the paired
signs are not additional hypotheses on a fixed-coordinate chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergTwistCompatibility
open CFSGTwistedE6HeisenbergCoordinateTwist CFSGTwistedE6HeisenbergStableRootFamilies
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckDiagramCovariance
open CFSGExceptionalHeisenbergProduct CFSGExceptionalHeisenbergPositive
open CFSGExceptionalCartanPositiveDefinite CFSGSerreDiagram
open CFSGHeisenbergCoordinateGroup CFSGCommutingParameterTwist
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos

theorem diagramIndex_involutive : Function.Involutive diagramIndex := by
  apply CFSGDiagramFieldTwistInvolution.combinedIndex_involutive
    A hd hs hp ho e6Permutation e6_preserves
  intro i
  fin_cases i <;> rfl

theorem actual_unitTwist_involutive (K : Type) [CommRing K] (sigma : K ≃+* K)
    (hSigma : Function.Involutive sigma) : Function.Involutive (unitTwist K sigma) :=
  CFSGDiagramFieldTwistInvolution.unitTwist_involutive
    diagramIndex diagramIndex_involutive sigma hSigma

private theorem intertwined_mul {D G : Type*} [Group D] [Group G]
    (f : D →* G) (hf : Function.Injective f) (t : MulAut G) (c : D → D)
    (hc : ∀ g, t (f g) = f (c g)) (g h : D) : c (g * h) = c g * c h := by
  apply hf
  calc
    f (c (g * h)) = t (f (g * h)) := (hc _).symm
    _ = t (f g * f h) := congrArg t (f.map_mul g h)
    _ = t (f g) * t (f h) := t.map_mul _ _
    _ = f (c g) * f (c h) := congrArg₂ (fun a b : G => a * b) (hc g) (hc h)
    _ = f (c g * c h) := (f.map_mul _ _).symm

private theorem intertwined_involutive {D G : Type*} [Group D] [Group G]
    (f : D →* G) (hf : Function.Injective f) (t : MulAut G) (c : D → D)
    (hc : ∀ g, t (f g) = f (c g)) (ht : Function.Involutive t) :
    Function.Involutive c := by
  intro g
  apply hf
  exact (hc (c g)).symm.trans ((congrArg t (hc g).symm).trans (ht (f g)))

theorem coordinateTwist_mul (K : Type) [Field K] (sigma : K ≃+* K) (g h : Element K 10) :
    coordinateTwist K sigma (g * h) = coordinateTwist K sigma g * coordinateTwist K sigma h :=
  intertwined_mul (rawHom A hd hs hp ho configuration K)
    (rawHom_injective A hd hs hp ho configuration K) (unitTwist K sigma)
    (coordinateTwist K sigma) (rawHom_twist K sigma) g h

theorem coordinateTwist_involutive (K : Type) [Field K] (sigma : K ≃+* K)
    (hSigma : Function.Involutive sigma) : Function.Involutive (coordinateTwist K sigma) :=
  intertwined_involutive (rawHom A hd hs hp ho configuration K)
    (rawHom_injective A hd hs hp ho configuration K) (unitTwist K sigma)
    (coordinateTwist K sigma) (rawHom_twist K sigma)
    (actual_unitTwist_involutive K sigma hSigma)

private theorem coefficient_at_partner {K : Type} [CommRing K] (sigma : K ≃+* K)
    (w : Fin 10 → ℤ) (v : Fin 10 → K) (i : Fin 10) :
    coefficientMap sigma partner w v (partner i) = (w i : K) * sigma (v i) := by
  change (w (partner.symm (partner i)) : K) * sigma (v (partner.symm (partner i))) = _
  rw [partner.symm_apply_apply]

theorem firstWeight_partner_mul (K : Type) [Field K] (i : Fin 10) :
    (firstWeight (partner i) : K) * (firstWeight i : K) = 1 := by
  let g : Element K 10 := ⟨fun _ => 1, 0, 0⟩
  have hh := congrArg (fun z : Element K 10 => z.a (partner (partner i)))
    (coordinateTwist_involutive K (RingEquiv.refl K) (fun _ => rfl) g)
  change coefficientMap (RingEquiv.refl K) partner firstWeight
      (coefficientMap (RingEquiv.refl K) partner firstWeight (fun _ => 1))
      (partner (partner i)) = 1 at hh
  rw [coefficient_at_partner, coefficient_at_partner] at hh
  simpa only [RingEquiv.refl_apply, mul_one] using hh

theorem secondWeight_partner_mul (K : Type) [Field K] (i : Fin 10) :
    (secondWeight (partner i) : K) * (secondWeight i : K) = 1 := by
  let g : Element K 10 := ⟨0, fun _ => 1, 0⟩
  have hh := congrArg (fun z : Element K 10 => z.b (partner (partner i)))
    (coordinateTwist_involutive K (RingEquiv.refl K) (fun _ => rfl) g)
  change coefficientMap (RingEquiv.refl K) partner secondWeight
      (coefficientMap (RingEquiv.refl K) partner secondWeight (fun _ => 1))
      (partner (partner i)) = 1 at hh
  rw [coefficient_at_partner, coefficient_at_partner] at hh
  simpa only [RingEquiv.refl_apply, mul_one] using hh

end SymmetricSubgroupAsymptotics.CFSGTwistedE6HeisenbergTwistCompatibility
