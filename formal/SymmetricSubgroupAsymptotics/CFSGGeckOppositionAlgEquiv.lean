import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
import Mathlib.Tactic.NoncommRing

/-! The actual Geck opposition is multiplicative as well as a Lie map.
This transfers polynomial identities between positive and negative roots. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGeckOppositionAlgEquiv
variable {ι M N : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
    {P : RootPairing ι ℚ M N} [P.IsCrystallographic] (b : P.Base)

def opposition : Matrix (b.support⊕ι) (b.support⊕ι) ℚ≃ₐ[ℚ]
    Matrix (b.support⊕ι) (b.support⊕ι) ℚ :=
  AlgEquiv.ofLinearEquiv (RootPairing.GeckConstruction.ωConj b).toLinearEquiv
    (by
      change RootPairing.GeckConstruction.ω b*1*RootPairing.GeckConstruction.ω b=1
      simpa only [mul_one] using (RootPairing.GeckConstruction.ω_mul_ω (b:=b)))
    (by
      intro x y
      change RootPairing.GeckConstruction.ω b*(x*y)*RootPairing.GeckConstruction.ω b=
        (RootPairing.GeckConstruction.ω b*x*RootPairing.GeckConstruction.ω b)*
        (RootPairing.GeckConstruction.ω b*y*RootPairing.GeckConstruction.ω b)
      calc
        _=RootPairing.GeckConstruction.ω b*x*
          (RootPairing.GeckConstruction.ω b*RootPairing.GeckConstruction.ω b)*y*
          RootPairing.GeckConstruction.ω b := by
            rw [RootPairing.GeckConstruction.ω_mul_ω]
            simp only [mul_one,mul_assoc]
        _=_ := by noncomm_ring)

theorem opposition_E (i : b.support) :
    opposition b (RootPairing.GeckConstruction.e i)=RootPairing.GeckConstruction.f i := by
  change RootPairing.GeckConstruction.ω b*RootPairing.GeckConstruction.e i*
    RootPairing.GeckConstruction.ω b=RootPairing.GeckConstruction.f i
  rw [RootPairing.GeckConstruction.ω_mul_e,mul_assoc,
    RootPairing.GeckConstruction.ω_mul_ω,mul_one]

theorem opposition_F (i : b.support) :
    opposition b (RootPairing.GeckConstruction.f i)=RootPairing.GeckConstruction.e i := by
  change RootPairing.GeckConstruction.ω b*RootPairing.GeckConstruction.f i*
    RootPairing.GeckConstruction.ω b=RootPairing.GeckConstruction.e i
  rw [RootPairing.GeckConstruction.ω_mul_f,mul_assoc,
    RootPairing.GeckConstruction.ω_mul_ω,mul_one]

end SymmetricSubgroupAsymptotics.CFSGGeckOppositionAlgEquiv
