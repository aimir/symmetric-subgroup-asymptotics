import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers

/-! Every ambient-invariant scalar character is determined by the same
original normal generators, without a p-group hypothesis. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

theorem primeRelativeHead_le_normalGen (p : ℕ) [Fact p.Prime]
    {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal] :
    Module.finrank (ZMod p) (primeRelativeCharacters p N) ≤ MarkedC4.normalGen N := by
  obtain ⟨S, hS, _, hcl⟩ := MarkedC4.normalGen_spec N
  let x : Fin S.card → G := fun i => ((S.equivFin.symm i : S) : G)
  have hrange : Set.range x = (S : Set G) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (S.equivFin.symm i).property
    · intro hg
      refine ⟨S.equivFin ⟨g, hg⟩, ?_⟩
      exact congrArg Subtype.val (S.equivFin.symm_apply_apply ⟨g, hg⟩)
  have h := primeRelativeHead_le_normal_generating_tuple p N x
    (by rw [hrange]; exact hcl)
  exact h.trans_eq hS

end SymmetricSubgroupAsymptotics
