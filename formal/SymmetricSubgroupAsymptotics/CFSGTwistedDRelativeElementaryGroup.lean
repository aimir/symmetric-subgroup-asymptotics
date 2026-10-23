import SymmetricSubgroupAsymptotics.CFSGTwistedA2FixedField
import SymmetricSubgroupAsymptotics.CFSGTwistedDSingularPrefix

/-! The literal natural relative-root subgroup in every rank at least
two. Its generators are untouched fixed-field chain roots and the
Frobenius-paired terminal roots. This is a definition by actual root
words, not an identification with the whole fixed group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDGenerationForkTorus
open CFSGTwistedA2FixedField CFSGSerreOrdinaryTwists CFSGTwistedDSingularPrefix

def pairedRoot (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    (Mat (q.Extension 2) (s + 2))ˣ :=
  rootTransvection (q.Extension 2) (s + 2) neg (pen s) a *
    rootTransvection (q.Extension 2) (s + 2) neg (last s) (definingFieldAutomorphism q 2 a)

def relativeGenerators (s : ℕ) (q : CFSG.PrimePower) :
    Set ((Mat (q.Extension 2) (s + 2))ˣ) :=
  {g | (∃ (neg : Bool) (i : Fin s) (a : fixedField q),
      g = rootTransvection (q.Extension 2) (s + 2) neg (chainNode s i) (a : q.Extension 2)) ∨
    ∃ (neg : Bool) (a : q.Extension 2), g = pairedRoot s q neg a}

def relativeRootGroup (s : ℕ) (q : CFSG.PrimePower) :
    Subgroup ((Mat (q.Extension 2) (s + 2))ˣ) := Subgroup.closure (relativeGenerators s q)

theorem chain_mem (s : ℕ) (q : CFSG.PrimePower) (neg : Bool)
    (i : Fin s) (a : fixedField q) :
    rootTransvection (q.Extension 2) (s + 2) neg (chainNode s i) (a : q.Extension 2) ∈
      relativeRootGroup s q := Subgroup.subset_closure (Or.inl ⟨neg, i, a, rfl⟩)

theorem paired_mem (s : ℕ) (q : CFSG.PrimePower) (neg : Bool) (a : q.Extension 2) :
    pairedRoot s q neg a ∈ relativeRootGroup s q :=
  Subgroup.subset_closure (Or.inr ⟨neg, a, rfl⟩)

theorem relativeRootGroup_le_elementary (s : ℕ) (q : CFSG.PrimePower) :
    relativeRootGroup s q ≤ elementaryRootGroup (q.Extension 2) (s + 2) := by
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨neg, i, a, rfl⟩ | ⟨neg, a, rfl⟩
  · exact rootTransvection_mem _ _ _ _ _
  · exact (elementaryRootGroup (q.Extension 2) (s + 2)).mul_mem
      (rootTransvection_mem _ _ _ _ _) (rootTransvection_mem _ _ _ _ _)

end SymmetricSubgroupAsymptotics.CFSGTwistedDRelativeElementaryGroup
