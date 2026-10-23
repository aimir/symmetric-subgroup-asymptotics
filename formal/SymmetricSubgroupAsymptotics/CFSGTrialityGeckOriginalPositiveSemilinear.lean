import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPairScalarAction
import SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalSimpleParameterRanges
import SymmetricSubgroupAsymptotics.CFSGRootParameterScalarNormalizer

/-! Actual positive simple parameter maps induced by a pair-fixing
original automorphism are scalar times automorphisms of the literal
cubic and fixed fields. The fields are not yet identified with each
other: their restriction coupling and the opposite signs are later
obligations. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPositiveSemilinear
open CFSGTrialityGeckOriginalSimpleParameters CFSGTrialityGeckOriginalSimpleParameterRanges
open CFSGTrialityGeckOriginalSignedRootAction CFSGTrialityGeckOriginalOppositionAxes
open CFSGTrialityGeckOriginalRootFamily CFSGTrialityGeckOriginalOppositeAlignment
open CFSGTrialityGeckOriginalPairNormalizer CFSGTrialityGeckOriginalPairScalarAction
open CFSGTrialityFixedField CFSGRootParameterAutomorphism CFSGRootParameterScalarNormalizer
open CFSGFiniteFieldScalarNormalizer

theorem positive_short_range_map (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    (originalShortHom q false).range.map f.toMonoidHom=(originalShortHom q false).range := by
  have hr : (originalShortHom q false).range=originalPositiveOrbitRoot q false :=
    originalShortHom_range q false
  rw [hr]
  exact (original_pair_fixer_fixes_signed_roots q f hp hn).1 false

theorem positive_middle_range_map (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    (originalMiddleHom q false).range.map f.toMonoidHom=(originalMiddleHom q false).range := by
  have hr : (originalMiddleHom q false).range=originalPositiveOrbitRoot q true :=
    originalMiddleHom_range q false
  rw [hr]
  exact (original_pair_fixer_fixes_signed_roots q f hp hn).1 true

theorem positive_parameters_semilinear (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.TrialityD4 q)] (f : MulAut (CFSG.Models.TrialityD4 q))
    (hp : (originalSylow q).map f.toMonoidHom=originalSylow q)
    (hn : (originalNegative q).map f.toMonoidHom=originalNegative q) :
    ∃sigma:q.Extension 3≃+*q.Extension 3,∃tau:fixedField q≃+*fixedField q,
      ∃c:(q.Extension 3)ˣ,∃a:(fixedField q)ˣ,
      (∀t,f (originalShortHom q false (Multiplicative.ofAdd t))=
        originalShortHom q false (Multiplicative.ofAdd ((c:q.Extension 3)*sigma t)))∧
      (∀t:fixedField q,f (originalMiddleHom q false (Multiplicative.ofAdd t))=
        originalMiddleHom q false (Multiplicative.ofAdd ((a:fixedField q)*tau t))) := by
  let X := originalShortHom q false
  let Y := originalMiddleHom q false
  have hX := positive_short_range_map q f hp hn
  have hY := positive_middle_range_map q f hp hn
  have hx := originalShortHom_injective q false
  have hy := originalMiddleHom_injective q false
  have hT := originalPairNormalizer_map q f hp hn
  have hnx := parameterAut_mem_scalar_normalizer X hx f hX (originalPairNormalizer q)
    (by
      intro d hd
      obtain ⟨c,a,hc,ha⟩ := originalPairNormalizer_positive_scalars q d hd
      exact ⟨c,hc⟩)
    (by
      intro c
      obtain ⟨d,hd,hc,ha⟩ := originalPairNormalizer_realizes_scalars q c 1
      exact ⟨d,hd,hc⟩) hT
  have hny := parameterAut_mem_scalar_normalizer Y hy f hY (originalPairNormalizer q)
    (by
      intro d hd
      obtain ⟨c,a,hc,ha⟩ := originalPairNormalizer_positive_scalars q d hd
      exact ⟨a,ha⟩)
    (by
      intro a
      obtain ⟨d,hd,hc,ha⟩ := originalPairNormalizer_realizes_scalars q 1 a
      exact ⟨d,hd,ha⟩) hT
  obtain ⟨⟨c,sigma⟩,hsigma,_⟩ := exists_unique_scalar_ringAut (parameterAut X hx f hX) hnx
  obtain ⟨⟨a,tau⟩,htau,_⟩ := exists_unique_scalar_ringAut (parameterAut Y hy f hY) hny
  refine ⟨sigma,tau,c,a,?_,?_⟩
  · intro t
    calc
      f (X (Multiplicative.ofAdd t))=X (Multiplicative.ofAdd (parameterAut X hx f hX t)) :=
        (parameterAut_apply X hx f hX t).symm
      _=X (Multiplicative.ofAdd ((c:q.Extension 3)*sigma t)) := congrArg
        (fun z=>X (Multiplicative.ofAdd z)) (hsigma t)
  · intro t
    calc
      f (Y (Multiplicative.ofAdd t))=Y (Multiplicative.ofAdd (parameterAut Y hy f hY t)) :=
        (parameterAut_apply Y hy f hY t).symm
      _=Y (Multiplicative.ofAdd ((a:fixedField q)*tau t)) := congrArg
        (fun z=>Y (Multiplicative.ofAdd z)) (htau t)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckOriginalPositiveSemilinear
