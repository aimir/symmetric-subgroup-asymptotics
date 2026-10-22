import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! Conjugating one subgroup by a normalizer of the other preserves
trivial intersection. The statement concerns actual subgroup images. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint
open CFSGSubgroupConjugateOrbitCardinality
variable {G : Type*} [Group G]

theorem inf_conjugate_eq_bot_iff (R S : Subgroup G) (g : G)
    (hg : g∈Subgroup.normalizer (R : Set G)) :
    R ⊓ S.map (MulAut.conj g).toMonoidHom=⊥ ↔ R⊓S=⊥ := by
  have he : (R⊓S).map (MulAut.conj g).toMonoidHom=
      R⊓S.map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulEquiv.injective _),
      conjugate_eq_of_mem_normalizer R g hg]
  rw [←he]
  constructor
  · intro h
    apply Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (MulEquiv.injective (MulAut.conj g))
    simpa only [Subgroup.map_bot] using h
  · intro h
    rw [h,Subgroup.map_bot]

end SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateDisjoint
