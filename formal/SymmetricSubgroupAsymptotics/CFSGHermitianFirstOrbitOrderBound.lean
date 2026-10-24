import SymmetricSubgroupAsymptotics.FinitePairingFirstOrbitOrderBound
import SymmetricSubgroupAsymptotics.CFSGHermitianIsometryOrderBound

/-! A matrix-level adapter for the actual first-vector carrier. The
representation is abstract here, so no concrete classical-group model
has to unfold through the linear-equivalence transport. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianIsometryOrderBound
open CFSGTwistedAUnitaryParameters
open scoped Matrix

theorem card_le_pairing_first_carrier {K G : Type*} [Field K] [Finite K]
    [Group G] [Finite G] {n : ℕ}
    (rho : G →* (Matrix (Fin (n+1)) (Fin (n+1)) K)ˣ)
    (hinj : Function.Injective rho) (sigma : K ≃+* K)
    (H : (Matrix (Fin (n+1)) (Fin (n+1)) K)ˣ)
    (hpres : ∀ g : G, (((rho g).val.map sigma).transpose * H.val * (rho g).val)=H.val)
    (S : Set (Fin (n+1) → K))
    (hS : ∀ g : G, (rho g).val *ᵥ Pi.single (0:Fin (n+1)) 1 ∈ S) :
    Nat.card G ≤ Nat.card S * Nat.card K ^ (n*(n+1)/2) := by
  refine FinitePairingFirstOrbitOrderBound.card_le_of_first_orbit
    (Pi.basisFun K (Fin (n+1))) (matrixLinearHom rho)
    (((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin (n+1) → K))).injective).comp hinj)
    (hermitianPair sigma H.val) ?_ ?_ S ?_
  · intro x y hxy
    have hh : H.val *ᵥ x=H.val *ᵥ y := by
      funext i
      have hi := hxy i
      simp only [Pi.basisFun_apply] at hi
      simpa only [hermitianPair_single] using hi
    have hi := congrArg (fun v : Fin (n+1) → K => H⁻¹.val *ᵥ v) hh
    simpa only [Matrix.mulVec_mulVec,Units.inv_mul,Matrix.one_mulVec] using hi
  · intro g x y
    simp only [matrixLinearHom_apply]
    exact hermitianPair_isometry sigma H.val (rho g).val (hpres g) x y
  · intro g
    simpa only [matrixLinearHom_apply,Pi.basisFun_apply] using hS g

end SymmetricSubgroupAsymptotics.CFSGHermitianIsometryOrderBound
