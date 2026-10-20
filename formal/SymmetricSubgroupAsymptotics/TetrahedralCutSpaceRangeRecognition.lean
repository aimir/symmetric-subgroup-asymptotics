import SymmetricSubgroupAsymptotics.TetrahedralCutSpaceEdgeEmbedding
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TetrahedralCutSpaceEdgeEmbedding
open TetrahedralCutSpaceCoinvariantHead (Vector)

private theorem decomposition : ∀ v : Vector,embedding v=
    v 0 • embedding (Pi.single 0 1)+v 1 • embedding (Pi.single 1 1)+
      v 2 • embedding (Pi.single 2 1) := by decide +kernel

theorem range_eq_of_upper_and_basis
    (S : Subrepresentation AlternatingEdgeOriginalProjectorHeads.beta)
    (hupper : S≤embedding.range)
    (hbasis : ∀ i : Fin 3,embedding (Pi.single i 1)∈S) : S=embedding.range := by
  apply le_antisymm hupper
  rintro _ ⟨v,rfl⟩
  change embedding v ∈ S
  rw [decomposition]
  exact S.toSubmodule.add_mem
    (S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ (hbasis 0))
      (S.toSubmodule.smul_mem _ (hbasis 1)))
    (S.toSubmodule.smul_mem _ (hbasis 2))
end SymmetricSubgroupAsymptotics.TetrahedralCutSpaceEdgeEmbedding
