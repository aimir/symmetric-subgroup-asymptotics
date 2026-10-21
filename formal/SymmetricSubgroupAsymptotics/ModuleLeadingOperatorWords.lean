import Mathlib.Algebra.Module.Basic

/-! Compose genuine algebra operators along a finite leading-label path.
Only products in the original acting ring are used. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.ModuleLeadingOperatorWords

variable {A M I O : Type} [Ring A] [AddCommGroup M] [Module A M]

def run (step : O → I → Option I) : List O → I → Option I
  | [], a => some a
  | op :: ops, a => (step op a).bind (run step ops)

theorem exists_operator_of_run (step : O → I → Option I) (P : M → I → Prop)
    (hstep : ∀ op a b, step op a = some b → ∀ v, P v a → ∃ r : A, P (r • v) b)
    (ops : List O) (a b : I) (hab : run step ops a = some b)
    (v : M) (hv : P v a) : ∃ r : A, P (r • v) b := by
  induction ops generalizing a b v with
  | nil =>
      have he : a = b := Option.some.inj hab
      subst b
      exact ⟨1, by simpa only [one_smul] using hv⟩
  | cons op ops ih =>
      cases he : step op a with
      | none =>
          simp only [run, he, Option.bind_none] at hab
          cases hab
      | some c =>
          have hrest : run step ops c = some b := by
            simpa only [run, he, Option.bind_some] using hab
          obtain ⟨r, hr⟩ := hstep op a c he v hv
          obtain ⟨s, hs⟩ := ih c b hrest (r • v) hr
          exact ⟨s * r, by simpa only [mul_smul] using hs⟩

end SymmetricSubgroupAsymptotics.ModuleLeadingOperatorWords
