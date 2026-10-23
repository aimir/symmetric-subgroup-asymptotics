import SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerSurjective

/-! Solubility of one actual Sylow normalizer gives solubility for every
Sylow normalizer at that prime, through literal inner conjugation. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerConjugacy

theorem all_of_exists {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (h : ∃ P : Sylow p G, IsSolvable (Subgroup.normalizer (P : Set G)))
    (Q : Sylow p G) : IsSolvable (Subgroup.normalizer (Q : Set G)) := by
  obtain ⟨P, hP⟩ := h
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have he : (P : Subgroup G).map (MulAut.conj g).toMonoidHom = (Q : Subgroup G) := by
    have hh := congrArg (fun R : Sylow p G => (R : Subgroup G)) hg
    simpa only [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def] using hh
  have hs := CFSGSolubleSylowNormalizerSurjective.normalizer_soluble_map
    (MulAut.conj g).toMonoidHom (MulAut.conj g).surjective P hP
  have hN := congrArg (fun S : Subgroup G => Subgroup.normalizer (S : Set G)) he
  change IsSolvable (Subgroup.normalizer
    (((P : Subgroup G).map (MulAut.conj g).toMonoidHom) : Set G)) at hs
  let e := MulEquiv.subgroupCongr hN
  letI : IsSolvable (Subgroup.normalizer
    (((P : Subgroup G).map (MulAut.conj g).toMonoidHom) : Set G)) := hs
  exact solvable_of_surjective (f := e.toMonoidHom) e.surjective

end SymmetricSubgroupAsymptotics.CFSGSolubleSylowNormalizerConjugacy
