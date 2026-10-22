import SymmetricSubgroupAsymptotics.CFSGSimpleProjectiveDescent

/-! The literal quotient by the full centre is functorial under an
actual group equivalence, without any simplicity assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv
variable {G H : Type*} [Group G] [Group H]

theorem map_center (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact CFSGSimpleProjectiveDescent.map_mem_center e.toMonoidHom e.surjective x hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    exact CFSGSimpleProjectiveDescent.map_mem_center e.symm.toMonoidHom e.symm.surjective y hy

def equiv (e : G ≃* H) :
    G ⧸ Subgroup.center G ≃* H ⧸ Subgroup.center H :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (map_center e)

end SymmetricSubgroupAsymptotics.CFSGCenterQuotientEquiv
