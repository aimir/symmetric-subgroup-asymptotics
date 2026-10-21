import SymmetricSubgroupAsymptotics.MarkedC4ActualNormalFMarkedPeel

/-! Transport the same normal target subgroup and both of its actual
logarithmic invariants through a group equivalence. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport
open MarkedC4.RDTNormalFInterface MarkedC4.ActualNormalFMarkedPeel
variable {G H : Type} [Group G] [Group H]

theorem centralizer_map (e : G ≃* H) (F : Subgroup G) :
    (targetCentralizer F).map e.toMonoidHom=targetCentralizer (F.map e.toMonoidHom) := by
  apply le_antisymm
  · exact Subgroup.map_centralizer_le_centralizer_image (F : Set G) e.toMonoidHom
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using
      Subgroup.mem_centralizer_iff.mp hy (e x) ⟨x,hx,rfl⟩

theorem commutator_map (e : G ≃* H) (F : Subgroup G) :
    (targetCommutator F).map e.toMonoidHom=targetCommutator (F.map e.toMonoidHom) := by
  change (⁅F,⊤⁆ : Subgroup G).map e.toMonoidHom=⁅F.map e.toMonoidHom,⊤⁆
  rw [Subgroup.map_commutator]
  congr 1
  rw [←MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr e.surjective

theorem centralLog_map [Finite G] [Finite H] (e : G ≃* H) (F : Subgroup G) :
    centralLog (F.map e.toMonoidHom)=centralLog F := by
  unfold centralLog
  rw [←centralizer_map e F]
  exact congrArg (fun n : ℕ => Real.logb 2 (n : ℝ))
    (Nat.card_congr (e.subgroupMap (targetCentralizer F)).toEquiv).symm

theorem commutatorLog_map [Finite G] [Finite H] (e : G ≃* H) (F : Subgroup G) :
    commutatorLog (F.map e.toMonoidHom)=commutatorLog F := by
  unfold commutatorLog
  rw [←commutator_map e F]
  exact congrArg (fun n : ℕ => Real.logb 2 (n : ℝ))
    (Nat.card_congr (e.subgroupMap (targetCommutator F)).toEquiv).symm

end SymmetricSubgroupAsymptotics.NormalFEquivalenceTransport
