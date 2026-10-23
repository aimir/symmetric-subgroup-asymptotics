import SymmetricSubgroupAsymptotics.CFSGPolynomialZeroCardinality
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-! Literal projective representatives retain a full unit-scalar fibre.
Combining their injection with the proved polynomial zero count gives a
fraction-free bound for any actual projective carrier of polynomial zeros. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace SymmetricSubgroupAsymptotics.CFSGProjectivePolynomialCount
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def scalarRep (x : Projectivization K V × Kˣ) : V := x.2 • x.1.rep

theorem scalarRep_injective : Function.Injective (scalarRep (K := K) (V := V)) := by
  rintro ⟨p, a⟩ ⟨q, b⟩ he
  change a • p.rep = b • q.rep at he
  have hpq : p = q := by
    rw [← Projectivization.mk_rep p, ← Projectivization.mk_rep q]
    apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
    refine ⟨a⁻¹ * b, ?_⟩
    rw [mul_smul, ← he, inv_smul_smul]
  subst q
  have hab : a = b := by
    apply Units.ext
    exact smul_left_injective K p.rep_nonzero he
  exact Prod.ext rfl hab

theorem projective_carrier_card_mul_units_le [Finite K] [Finite V]
    (P : Set (Projectivization K V)) (W : Set V)
    (hW : ∀ p : P, ∀ a : Kˣ, a • p.val.rep ∈ W) :
    Nat.card P * (Nat.card K - 1) ≤ Nat.card W := by
  let f : P × Kˣ → W := fun x => ⟨x.2 • x.1.val.rep, hW x.1 x.2⟩
  have hf : Function.Injective f := by
    rintro ⟨p, a⟩ ⟨q, b⟩ he
    have hh : (p.val, a) = (q.val, b) := scalarRep_injective (congrArg Subtype.val he)
    have hpq : p = q := Subtype.ext
      (congrArg (fun z : Projectivization K V × Kˣ => z.1) hh)
    have hab : a = b := congrArg (fun z : Projectivization K V × Kˣ => z.2) hh
    exact Prod.ext hpq hab
  simpa only [Nat.card_prod, Nat.card_units] using Nat.card_le_card_of_injective f hf

theorem projective_polynomial_carrier_bound [Finite K] (n D : ℕ)
    (p : MvPolynomial (Fin (n + 1)) K) (hp : p ≠ 0) (hD : p.totalDegree ≤ D)
    (P : Set (Projectivization K (Fin (n + 1) → K)))
    (hP : ∀ x : P, ∀ a : Kˣ, MvPolynomial.eval (a • x.val.rep) p = 0) :
    Nat.card P * (Nat.card K - 1) ≤ D * Nat.card K ^ n :=
  (projective_carrier_card_mul_units_le P {v | MvPolynomial.eval v p = 0} hP).trans
    (CFSGPolynomialZeroCardinality.polynomial_zero_card_le n D p hp hD)

end SymmetricSubgroupAsymptotics.CFSGProjectivePolynomialCount
