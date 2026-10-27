import SymmetricSubgroupAsymptotics.PrimePeriodSimpleQuotientIndex
import SymmetricSubgroupAsymptotics.MatrixNaturalRowDotReflection
import SymmetricSubgroupAsymptotics.SmallNaturalMatrixProductReflection
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! One prime vector period in a genuine representation implies a prime
order divisor of the original finite group. Injectivity, image order,
and whole-operator powers are unnecessary. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.LinearRepresentationSelectedPrimePeriod
variable {G R : Type*} [Group G] [CommRing R] {n : ℕ}

 def action (ρ : G →* Matrix.GeneralLinearGroup (Fin n) R) :
    G →* ((Fin n → R) ≃ₗ[R] (Fin n → R)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R (Fin n → R)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

 def linearEnd (ρ : G →* Matrix.GeneralLinearGroup (Fin n) R) :
    G →* Module.End R (Fin n → R) :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (action ρ)

 theorem end_apply (ρ : G →* Matrix.GeneralLinearGroup (Fin n) R)
    (g : G) (v : Fin n → R) : linearEnd ρ g v=(ρ g : Matrix (Fin n) (Fin n) R) *ᵥ v := rfl

 theorem prime_dvd_card [Finite G]
    (ρ : G →* Matrix.GeneralLinearGroup (Fin n) R) (g : G)
    (p : ℕ) (hp : p.Prime) (v : Fin n → R)
    (hreturn : (linearEnd ρ g ^ p) v=v) (hmoved : linearEnd ρ g v≠v) : p∣Nat.card G := by
  letI : MulAction G (Fin n → R) := MulAction.compHom _ (action ρ)
  have hpow (k : ℕ) : g^k • v=(linearEnd ρ g ^ k) v := by
    change linearEnd ρ (g^k) v=(linearEnd ρ g ^ k) v
    rw [map_pow]
  apply PrimePeriodSimpleQuotientIndex.prime_dvd_card_of_point_period p hp g v
  · exact (hpow p).trans hreturn
  · have hone : g • v=linearEnd ρ g v := by simpa only [pow_one] using hpow 1
    exact fun he => hmoved (hone.symm.trans he)

 theorem packed_vector_step (p n bits : ℕ)
    (raw : Matrix (Fin n) (Fin n) ℕ) (rowCode : ℕ → ℕ) (inputCode nextCode : ℕ)
    (hrow : ∀ i j : Fin n, raw i j=
      MatrixNaturalRowDotReflection.packedDigit bits (rowCode i.val) j.val)
    (hcheck : ∀ i : Fin n,
      MatrixNaturalRowDotReflection.packedDot bits (rowCode i.val) inputCode n % p=
        MatrixNaturalRowDotReflection.packedDigit bits nextCode i.val % p) :
    SmallNaturalMatrixProductReflection.castMatrix p n raw *ᵥ
      (fun j : Fin n => (MatrixNaturalRowDotReflection.packedDigit bits inputCode j.val : ZMod p))=
      fun i : Fin n => (MatrixNaturalRowDotReflection.packedDigit bits nextCode i.val : ZMod p) := by
  funext i
  change (∑ j : Fin n, (raw i j : ZMod p)*
    (MatrixNaturalRowDotReflection.packedDigit bits inputCode j.val : ZMod p))=_
  calc
    _=∑ j : Fin n,
        (MatrixNaturalRowDotReflection.packedDigit bits (rowCode i.val) j.val : ZMod p)*
          (MatrixNaturalRowDotReflection.packedDigit bits inputCode j.val : ZMod p) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hrow i j]
    _=(MatrixNaturalRowDotReflection.packedDot bits (rowCode i.val) inputCode n : ZMod p) :=
      (MatrixNaturalRowDotReflection.cast_natDot p n
        (MatrixNaturalRowDotReflection.packedDigit bits (rowCode i.val))
        (MatrixNaturalRowDotReflection.packedDigit bits inputCode)).symm
    _=_ := (ZMod.natCast_eq_natCast_iff' _ _ p).mpr (hcheck i)

end SymmetricSubgroupAsymptotics.LinearRepresentationSelectedPrimePeriod
