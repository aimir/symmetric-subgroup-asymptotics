import SymmetricSubgroupAsymptotics.FiniteGeneratorWord
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Bidirectional generator words certify the exact image of one literal
generated subgroup under a specified ambient equivalence. In particular,
an actual point conjugator can be checked without enumerating either group
or comparing their orders. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

variable {G H ι κ : Type*} [Group G] [Group H]

structure FiniteGeneratorEquivWordCertificate
    (e : G ≃* H) (source : ι → G) (target : κ → H) where
  forward : FiniteGeneratorWordCertificate (fun i => e (source i)) target
  backward : FiniteGeneratorWordCertificate (fun j => e.symm (target j)) source

namespace FiniteGeneratorEquivWordCertificate

variable {e : G ≃* H} {source : ι → G} {target : κ → H}
  (C : FiniteGeneratorEquivWordCertificate e source target)

include C in
/-- Both inclusions use the actual word equations, with no order or
abstract-isomorphism substitute. -/
theorem map_closure_eq :
    (Subgroup.closure (Set.range source)).map e.toMonoidHom =
      Subgroup.closure (Set.range target) := by
  apply le_antisymm
  · apply Subgroup.map_le_iff_le_comap.mpr
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change e (source i) ∈ Subgroup.closure (Set.range target)
    rw [← C.forward.equations i]
    exact (C.forward.words i).eval_mem_closure target
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨e.symm (target j), ?_, e.apply_symm_apply (target j)⟩
    rw [← C.backward.equations j]
    exact (C.backward.words j).eval_mem_closure source

end FiniteGeneratorEquivWordCertificate
end SymmetricSubgroupAsymptotics

end
