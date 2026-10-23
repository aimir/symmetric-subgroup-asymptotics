import SymmetricSubgroupAsymptotics.CFSGTwistedDLinearParameters
import SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeNormScaling

/-! Linear parameter changes on the actual nonsplit quadratic space.
The anisotropic extension coordinate is retained. In particular every
nonzero fixed-field dilation of the negative half extends by a literal
norm lift to a similitude, including in characteristic two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDParameterSimilitudes
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDLinearParameters
open CFSGTwistedA2FixedField CFSGTwistedDRelativeTorusParameters
open CFSGTwistedDRelativeNormScaling

def parameterChange (n : ℕ) (q : CFSG.PrimePower)
    (A B : (Fin (n + 1) → fixedField q) ≃ₗ[fixedField q] (Fin (n + 1) → fixedField q))
    (c : (q.Extension 2)ˣ) : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q :=
  (linearParameters n q).trans
    ((A.prodCongr (B.prodCongr (Units.mulLeftLinearEquiv (fixedField q) (q.Extension 2) c))).trans
      (linearParameters n q).symm)

theorem parameterChange_coordinates (n : ℕ) (q : CFSG.PrimePower)
    (A B : (Fin (n + 1) → fixedField q) ≃ₗ[fixedField q] (Fin (n + 1) → fixedField q))
    (c : (q.Extension 2)ˣ) (v : fixedSpace n q) :
    linearParameters n q (parameterChange n q A B c v) =
      (A (linearParameters n q v).1,
        (B (linearParameters n q v).2.1, (c : q.Extension 2) * (linearParameters n q v).2.2)) :=
  (linearParameters n q).apply_symm_apply _

theorem parameterChange_quadratic (n : ℕ) (q : CFSG.PrimePower)
    (A B : (Fin (n + 1) → fixedField q) ≃ₗ[fixedField q] (Fin (n + 1) → fixedField q))
    (c : (q.Extension 2)ˣ)
    (hcross : ∀ x y, dotProduct (A x) (B y) =
      (normHom q c : fixedField q) * dotProduct x y) (v : fixedSpace n q) :
    fixedQuadraticForm n q (parameterChange n q A B c v) =
      (normHom q c : fixedField q) * fixedQuadraticForm n q v := by
  have hQ (w : fixedSpace n q) := quadratic_parameters n q (linearParameters n q w)
  simp only [LinearEquiv.symm_apply_apply] at hQ
  rw [hQ, hQ, parameterChange_coordinates]
  change dotProduct (A _) (B _) + Algebra.norm (fixedField q) ((c : q.Extension 2) * _) = _
  rw [hcross, map_mul, mul_add]
  rfl

def negativeDilation (n : ℕ) (q : CFSG.PrimePower) (c : (q.Extension 2)ˣ) :
    fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q :=
  parameterChange n q (LinearEquiv.refl (fixedField q) _)
    (LinearEquiv.smulOfUnit (normHom q c)) c

theorem negativeDilation_coordinates (n : ℕ) (q : CFSG.PrimePower)
    (c : (q.Extension 2)ˣ) (v : fixedSpace n q) :
    linearParameters n q (negativeDilation n q c v) =
      ((linearParameters n q v).1,
        ((normHom q c : fixedField q) • (linearParameters n q v).2.1,
          (c : q.Extension 2) * (linearParameters n q v).2.2)) :=
  parameterChange_coordinates n q _ _ c v

theorem negativeDilation_quadratic (n : ℕ) (q : CFSG.PrimePower)
    (c : (q.Extension 2)ˣ) (v : fixedSpace n q) :
    fixedQuadraticForm n q (negativeDilation n q c v) =
      (normHom q c : fixedField q) * fixedQuadraticForm n q v := by
  apply parameterChange_quadratic
  intro x y
  change dotProduct x ((normHom q c : fixedField q) • y) = _
  simp only [dotProduct_smul, smul_eq_mul]

theorem exists_negativeDilation (n : ℕ) (q : CFSG.PrimePower) (t : (fixedField q)ˣ) :
    ∃ (c : (q.Extension 2)ˣ) (L : fixedSpace n q ≃ₗ[fixedField q] fixedSpace n q),
      normHom q c = t ∧
      (∀ v, linearParameters n q (L v) =
        ((linearParameters n q v).1,
          ((t : fixedField q) • (linearParameters n q v).2.1,
            (c : q.Extension 2) * (linearParameters n q v).2.2))) ∧
      (∀ v, fixedQuadraticForm n q (L v) = (t : fixedField q) * fixedQuadraticForm n q v) := by
  obtain ⟨c, hc⟩ := normHom_surjective q t
  refine ⟨c, negativeDilation n q c, hc, ?_, ?_⟩
  · intro v
    rw [negativeDilation_coordinates, hc]
  · intro v
    rw [negativeDilation_quadratic, hc]

end SymmetricSubgroupAsymptotics.CFSGTwistedDParameterSimilitudes
