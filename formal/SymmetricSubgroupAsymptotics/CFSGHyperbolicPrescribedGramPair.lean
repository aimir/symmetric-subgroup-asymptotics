import Mathlib.Data.Matrix.Mul

/-! Two literal hyperbolic coordinates realize arbitrary two quadratic
values and their polar cross value, over every field. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGHyperbolicPrescribedGramPair
variable {K I : Type*} [Field K] [Fintype I] [DecidableEq I]

theorem exists_pair (i j : I) (hij : i ≠ j) (a b c : K) :
    ∃ h k : (I → K) × (I → K),
      dotProduct h.1 h.2 = a ∧ dotProduct k.1 k.2 = b ∧
        dotProduct h.1 k.2 + dotProduct k.1 h.2 = c := by
  refine ⟨(Pi.single i 1, Pi.single i a),
    (Pi.single j 1, Pi.single i c + Pi.single j b), ?_, ?_, ?_⟩
  · simp only [single_dotProduct, Pi.single_eq_same, one_mul]
  · simp [single_dotProduct, Pi.single_apply, hij, Ne.symm hij]
  · simp [single_dotProduct, Pi.single_apply, hij, Ne.symm hij]

end SymmetricSubgroupAsymptotics.CFSGHyperbolicPrescribedGramPair
