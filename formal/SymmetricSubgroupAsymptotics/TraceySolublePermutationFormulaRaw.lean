import SymmetricSubgroupAsymptotics.TraceySolubleOrbitInducedInput
import SymmetricSubgroupAsymptotics.InducedSubrepresentationCount

/-! Raw permutation specialization of Tracey, *Minimal generation of
transitive permutation groups*, J. Algebra 509 (2018), Definition 1.5 and
Theorem 1.6 (the soluble-transitive `E_sol` branch).

Mathematical identification: take the trivial one-dimensional module of
an actual point stabilizer (`a = 1`); its induced module is the permutation
module on the transitive point set. This is a specialization of the
published theorem, not a verbatim quotation. We retain both defining
integer inequalities for `E_sol`; no fractional capacity is imported. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

/-- The exact published `E_sol` formula and its uniform generator meaning. -/
def TraceySolublePermutationFormulaRawInput : Prop :=
  ∀ (G X : Type) [Group G] [Finite G] [IsSolvable G]
    [Finite X] [MulAction G X] [MulAction.IsPretransitive G X],
    ∃ d : ℕ, TraceyBinarySolubleFormulaBounds (Nat.card X) d ∧
      UniformSubrepresentationGeneratorBound
        (permutationFunctionRepresentation (ZMod 2) G X) d

/-- Derive invariant-head arithmetic from the module generator statement. -/
theorem traceySolublePermutation_head_formula
    (h : TraceySolublePermutationFormulaRawInput)
    (G X : Type) [Group G] [Finite G] [IsSolvable G]
    [Finite X] [MulAction G X] [MulAction.IsPretransitive G X]
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X)) :
    TraceyBinarySolubleFormulaBounds (Nat.card X)
      (Module.finrank (ZMod 2) (M.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))) := by
  obtain ⟨d, hd, hgen⟩ := h G X
  obtain ⟨v, hv⟩ := hgen M
  have hr := representationHead_finrank_le_generators M.toRepresentation v hv
  exact ⟨hr.trans hd.1, (Nat.mul_le_mul_left _ hr).trans hd.2⟩

end SymmetricSubgroupAsymptotics
