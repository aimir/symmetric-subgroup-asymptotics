import SymmetricSubgroupAsymptotics.FiniteHermitianPrefixOrbits
import SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalCoordinates
import SymmetricSubgroupAsymptotics.CFSGQuadraticDiagonalNormShell
import SymmetricSubgroupAsymptotics.FiniteHermitianFrameEnvelope
import SymmetricSubgroupAsymptotics.CFSGHermitianIsometryOrderBound

/-! Genuine orthonormal-prefix orbit counts pay a uniform Hermitian
isometry order bound over the actual quadratic finite-field extension.
The faithful original representation is retained; an orthonormal basis
is structural input, not a cardinality or class-budget assumption. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalOrderBound
open Module FiniteHermitianBasisCoordinates FiniteBilinearPrefixOrbits
open CFSGSerreOrdinaryTwists

private def frameCost (B : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | d+1 => B (d+1)*frameCost B d

theorem card_le_three_mul_square_power (q : CFSG.PrimePower)
    {V G : Type*} [AddCommGroup V] [Module (q.Extension 2) V] [Group G] [Finite G]
    {n : ℕ} (b : Basis (Fin n) (q.Extension 2) V)
    (rho : G →* (V ≃ₗ[q.Extension 2] V)) (hinj : Function.Injective rho)
    (hpres : ∀ g : G, ∀ x y : V,
      coordinatePair (definingFieldAutomorphism q 2) b (rho g x) (rho g y)=
        coordinatePair (definingFieldAutomorphism q 2) b x y) :
    Nat.card G ≤ 3*q.order^(n^2) := by
  let B := fun d => FiniteDiagonalNormShellRecurrence.shellCard
    (fun a : q.Extension 2 => definingFieldAutomorphism q 2 a*a) d
  have hcount (d : ℕ) : ∀ k : ℕ, k+d=n →
      Nat.card (prefixSubgroup rho b k) ≤ frameCost B d := by
    induction d with
    | zero =>
      intro k hk
      have hk' : k=n := by omega
      subst k
      rw [prefix_end_card rho b hinj]
      exact le_rfl
    | succ d ih =>
      intro k hk
      have hkn : k<n := by omega
      have hdim : n-k=d+1 := by omega
      calc
        _ ≤ B (n-k)*Nat.card (prefixSubgroup rho b (k+1)) :=
          FiniteHermitianPrefixOrbits.next_step_card rho b
            (definingFieldAutomorphism q 2) hpres k hkn
        _ ≤ B (n-k)*frameCost B d := Nat.mul_le_mul_left _ (ih (k+1) (by omega))
        _ = frameCost B (d+1) := by rw [hdim]; rfl
  have hgroup : Nat.card G ≤ frameCost B n := by
    have hh := hcount n 0 (by omega)
    rwa [prefix_zero_card rho b] at hh
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans
    (Nat.le_self_pow q.exponent_pos.ne' q.prime)
  exact hgroup.trans (FiniteHermitianFrameEnvelope.frame_card_le q.order hq B (frameCost B)
    (CFSGQuadraticDiagonalNormShell.raw_shell_zero q)
    (CFSGQuadraticDiagonalNormShell.raw_shell_succ_recurrence q) rfl
    (fun _ => le_rfl) n)

theorem matrix_card_le_of_orthonormal_basis (q : CFSG.PrimePower)
    {I G : Type*} [Fintype I] [DecidableEq I] [Group G] [Finite G]
    (rho : G →* (Matrix I I (q.Extension 2))ˣ) (hinj : Function.Injective rho)
    (H : (Matrix I I (q.Extension 2))ˣ)
    (hpres : ∀ g : G,
      (((rho g).val.map (definingFieldAutomorphism q 2)).transpose*H.val*(rho g).val)=H.val)
    {n : ℕ} (b : Basis (Fin n) (q.Extension 2) (I → q.Extension 2))
    (hb : ∀ i j,
      CFSGTwistedAUnitaryParameters.hermitianPair (definingFieldAutomorphism q 2) H.val
        (b i) (b j)=if i=j then 1 else 0) :
    Nat.card G ≤ 3*q.order^(n^2) := by
  classical
  let rhoL : G →* ((I → q.Extension 2) ≃ₗ[q.Extension 2] (I → q.Extension 2)) :=
    ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (q.Extension 2) (I → q.Extension 2))).toMonoidHom).comp rho
  have hi : Function.Injective rhoL :=
    ((Matrix.GeneralLinearGroup.toLin.trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (q.Extension 2) (I → q.Extension 2))).injective).comp hinj
  apply card_le_three_mul_square_power q b rhoL hi
  intro g x y
  rw [←FiniteHermitianOrthonormalCoordinates.pairing_eq_coordinatePair
    (definingFieldAutomorphism q 2) H.val b hb,
    ←FiniteHermitianOrthonormalCoordinates.pairing_eq_coordinatePair
      (definingFieldAutomorphism q 2) H.val b hb]
  change CFSGTwistedAUnitaryParameters.hermitianPair (definingFieldAutomorphism q 2) H.val
    ((rho g).val *ᵥ x) ((rho g).val *ᵥ y)=_
  exact CFSGTwistedAUnitaryParameters.hermitianPair_isometry
    (definingFieldAutomorphism q 2) H.val (rho g).val (hpres g) x y

end SymmetricSubgroupAsymptotics.FiniteHermitianOrthonormalOrderBound
