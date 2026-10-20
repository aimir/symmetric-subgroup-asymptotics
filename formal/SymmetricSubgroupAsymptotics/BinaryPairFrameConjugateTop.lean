import SymmetricSubgroupAsymptotics.BinaryPairFrameTransport

/-! Reindexing pair labels transports the literal top action by the same
permutation. The original physical source group and actual kernel stay
identified, so the original normal subgroup can be retained throughout a
degree-eight action-classification argument. -/
set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X I J : Type*} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U I)

theorem reindex_top_ker (e : I ≃ J) : (F.reindex e).top.ker = F.top.ker :=
  MonoidHom.ker_mulEquiv_comp F.top e.permCongrHom

theorem reindex_top_range (e : I ≃ J) :
    (F.reindex e).top.range = F.top.range.map e.permCongrHom.toMonoidHom :=
  MonoidHom.range_comp e.permCongrHom.toMonoidHom F.top

theorem reindex_top_range_conjugation (g : Equiv.Perm I) :
    (F.reindex g).top.range = MulAut.conj g • F.top.range := by
  rw [reindex_top_range]
  have hg : g.permCongrHom.toMonoidHom = (MulAut.conj g).toMonoidHom := by
    ext p x
    rfl
  rw [hg, Subgroup.pointwise_smul_def]
  rfl

end SymmetricSubgroupAsymptotics.BinaryPairFrame
