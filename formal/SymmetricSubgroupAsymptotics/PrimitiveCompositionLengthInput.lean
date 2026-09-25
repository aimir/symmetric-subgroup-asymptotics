import SymmetricSubgroupAsymptotics.ChiefCompositionLength
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The literal primitive composition-length input and its proved
consequence for the actual chief weight used by the block recurrence.

External input: Glasby–Praeger–Rosa–Verret, "Bounding the composition
length of primitive permutation groups and completely reducible linear
groups", J. London Math. Soc.98 (2018), 557–572, Theorem1.3 (p.2 of the
March28,2018 author PDF). It bounds the length of a composition series
of a primitive degree-r group by (8/3)log₂r−4/3. Our series below is
proved to have actual normal inclusions and simple quotient factors.
We use degrees r≥2; no project chief-count inequality is an input. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

def PrimitiveCompositionLengthInput : Prop :=
  ∀ (r:ℕ), 2 ≤ r → ∀ (U:Subgroup (Equiv.Perm (Fin r))),
    MulAction.IsPreprimitive U (Fin r) → ∀t:SubnormalCompositionSeries U,
      (t.chain.length:ℝ) ≤ (8/3:ℝ)*Real.logb 2 r-4/3

/-- The chosen actual chief series satisfies the published bound because
we construct its actual composition refinement and compare the weights.
There is no Jordan–Hölder or abstract a₃ equality hypothesis. -/
theorem primitiveChiefWeight_le_log (hcomp:PrimitiveCompositionLengthInput)
    (r:ℕ) (hr:2 ≤ r) (U:Subgroup (Equiv.Perm (Fin r)))
    (hprim:MulAction.IsPreprimitive U (Fin r)) (s:ActualChiefSeries U) :
    (actualChiefSeriesTernaryWeight s:ℝ) ≤ (8/3:ℝ)*Real.logb 2 r-4/3 := by
  obtain ⟨t,ht⟩ := actualChiefWeight_le_some_compositionLength s
  exact (show (actualChiefSeriesTernaryWeight s:ℝ) ≤ (t.chain.length:ℝ) by
    exact_mod_cast ht).trans (hcomp r hr U hprim t)

end SymmetricSubgroupAsymptotics
