import SymmetricSubgroupAsymptotics.CFSGTwistedDFixedScalarSpanDescent
import SymmetricSubgroupAsymptotics.CFSGQuadraticFixedSpanForm

/-! Literal scalar extension of fixed-field subspaces preserves sums
and actual quadratic singularity, in both characteristics. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDFixedScalarSpanDescent
open CFSGTwistedDFixedQuadraticSpace CFSGTwistedDDisplacementScalarSpan
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists CFSGOrthogonalDIndexBundledQuadratic

theorem scalarSpan_sup (n : ℕ) (q : CFSG.PrimePower)
    (P Q : Submodule (fixedField q) (fixedSpace n q)) :
    scalarSpan n q (P ⊔ Q) = scalarSpan n q P ⊔ scalarSpan n q Q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
    change u.val + v.val ∈ scalarSpan n q P ⊔ scalarSpan n q Q
    exact Submodule.add_mem _
      ((show scalarSpan n q P ≤ scalarSpan n q P ⊔ scalarSpan n q Q from le_sup_left)
        ((fixed_mem_scalarSpan_iff n q P u).mpr hu))
      ((show scalarSpan n q Q ≤ scalarSpan n q P ⊔ scalarSpan n q Q from le_sup_right)
        ((fixed_mem_scalarSpan_iff n q Q v).mpr hv))
  · exact sup_le ((scalarSpan_le_iff n q P (P ⊔ Q)).mpr le_sup_left)
      ((scalarSpan_le_iff n q Q (P ⊔ Q)).mpr le_sup_right)

theorem scalarSpan_singular_iff (n : ℕ) (q : CFSG.PrimePower)
    (P : Submodule (fixedField q) (fixedSpace n q)) :
    (∀ x ∈ scalarSpan n q P, splitQuadraticForm (q.Extension 2) (n + 2) x = 0) ↔
      ∀ x ∈ P, fixedQuadraticForm n q x = 0 := by
  obtain ⟨theta, htheta⟩ := CFSGTwistedAQuadraticTrace.exists_nonfixed q
  rw [scalarSpan_eq_underlying_span,
    CFSGQuadraticFixedSpanDescent.quadratic_zero_span_iff (definingFieldAutomorphism q 2)
      theta htheta (fixedField q)
      (fun a => CFSGTwistedANaturalMatrices.extension_two_pow_twice q a) (fun _ => Iff.rfl)]
  constructor
  · intro h x hx
    apply Subtype.ext
    change splitQuadraticForm (q.Extension 2) (n + 2) x.val = 0
    exact h x.val ((underlying_mem_iff n q P x).mpr hx)
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact congrArg (fun a : fixedField q => a.val) (h v hv)

theorem scalarSpan_sup_singular_iff (n : ℕ) (q : CFSG.PrimePower)
    (P Q : Submodule (fixedField q) (fixedSpace n q)) :
    (∀ x ∈ scalarSpan n q P ⊔ scalarSpan n q Q,
      splitQuadraticForm (q.Extension 2) (n + 2) x = 0) ↔
      ∀ x ∈ P ⊔ Q, fixedQuadraticForm n q x = 0 := by
  rw [← scalarSpan_sup]
  exact scalarSpan_singular_iff n q (P ⊔ Q)

end SymmetricSubgroupAsymptotics.CFSGTwistedDFixedScalarSpanDescent
