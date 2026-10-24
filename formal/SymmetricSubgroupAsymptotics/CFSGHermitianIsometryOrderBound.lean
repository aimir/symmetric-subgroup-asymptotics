import SymmetricSubgroupAsymptotics.FiniteBilinearIsometryOrderBound
import SymmetricSubgroupAsymptotics.CFSGHermitianPairTransport
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! A faithful finite matrix group preserving an actual nonsingular
sesquilinear pairing satisfies the same basis-prefix bound as a bilinear
isometry group. No involution or unitary order formula is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHermitianIsometryOrderBound
open Module CFSGTwistedAUnitaryParameters
open scoped Matrix
variable {K G : Type*} [Field K] [Group G] {n : ℕ}

def matrixLinearHom (rho : G →* (Matrix (Fin n) (Fin n) K)ˣ) :
    G →* ((Fin n → K) ≃ₗ[K] (Fin n → K)) :=
  ((Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K))).toMonoidHom).comp rho

theorem matrixLinearHom_apply (rho : G →* (Matrix (Fin n) (Fin n) K)ˣ)
    (g : G) (x : Fin n → K) : matrixLinearHom rho g x = (rho g).val *ᵥ x := rfl

theorem hermitianPair_single (sigma : K ≃+* K) (H : Matrix (Fin n) (Fin n) K)
    (i : Fin n) (x : Fin n → K) :
    hermitianPair sigma H (Pi.single i 1) x = (H *ᵥ x) i := by
  have hs : sigma ∘ (Pi.single i (1 : K)) = Pi.single i 1 := by
    funext j
    by_cases hj : j = i <;> simp only [Function.comp_apply, Pi.single_apply, hj,
      if_true, if_false, map_one, map_zero]
  change dotProduct (sigma ∘ Pi.single i 1) (H *ᵥ x) = _
  rw [hs, single_dotProduct, one_mul]

theorem card_le_pairing_power [Finite K] [Finite G]
    (rho : G →* (Matrix (Fin n) (Fin n) K)ˣ) (hinj : Function.Injective rho)
    (sigma : K ≃+* K) (H : (Matrix (Fin n) (Fin n) K)ˣ)
    (hpres : ∀ g : G, (((rho g).val.map sigma).transpose * H.val * (rho g).val) = H.val) :
    Nat.card G ≤ Nat.card K ^ (n*(n+1)/2) := by
  apply FiniteBilinearIsometryOrderBound.card_le_of_separating_pairing
    (Pi.basisFun K (Fin n)) (matrixLinearHom rho)
    (((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin n → K))).injective).comp hinj)
    (hermitianPair sigma H.val)
  · intro x y hxy
    have hh : H.val *ᵥ x = H.val *ᵥ y := by
      funext i
      have hi := hxy i
      simp only [Pi.basisFun_apply] at hi
      simpa only [hermitianPair_single] using hi
    have hi := congrArg (fun v : Fin n → K => H⁻¹.val *ᵥ v) hh
    simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using hi
  · intro g x y
    simp only [matrixLinearHom_apply]
    exact hermitianPair_isometry sigma H.val (rho g).val (hpres g) x y

end SymmetricSubgroupAsymptotics.CFSGHermitianIsometryOrderBound
