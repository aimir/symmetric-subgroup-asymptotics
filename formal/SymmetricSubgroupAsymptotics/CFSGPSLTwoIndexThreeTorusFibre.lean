import SymmetricSubgroupAsymptotics.CFSGPSLTwoTorusCosetFibre
import SymmetricSubgroupAsymptotics.NormalSubgroupCoprimeIndexContainment

/-! Actual normal index-three Borel subgroups kill the characteristic
root group, hence the torus fills the original Weyl fibre. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPSLTwoIndexThreeTorusFibre
open CFSGPSLTwoGeometry CFSGPSLTwoRootCoordinates CFSGPSLTwoTorusCosetFibre
variable {F : Type*} [Field F]

theorem root_le_actual_index_three
    (H : Subgroup (projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3) :
    projectiveRoot (F:=F) ≤ H.map (projectiveBorel (F:=F)).subtype := by
  let U := (projectiveRoot (F:=F)).subgroupOf (projectiveBorel (F:=F))
  have hcard : Nat.card U = Nat.card F :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (projectiveRoot_le_borel (F:=F))).toEquiv).trans projectiveRoot_card
  have hc : (Nat.card U).Coprime H.index := by rw [hcard,hindex]; exact hcop
  have hle : U ≤ H :=
    NormalSubgroupCoprimeIndexContainment.le_of_coprime_card_index U H hc
  intro u hu
  let ub : projectiveBorel (F:=F) := ⟨u,projectiveRoot_le_borel hu⟩
  have hub : ub ∈ U := hu
  exact ⟨ub,hle hub,rfl⟩

theorem actual_index_three_weyl_fibre
    (H : Subgroup (projectiveBorel (F:=F))) [H.Normal]
    (hindex : H.index = 3) (hcop : (Nat.card F).Coprime 3)
    (b : projectiveBorel (F:=F)) :
    ∃ n : pairTorus (F:=F),
      n.val • (QuotientGroup.mk (projectiveWeyl (F:=F)) :
        PSL (F:=F) ⧸ H.map (projectiveBorel (F:=F)).subtype) =
      QuotientGroup.mk (projectiveWeyl*b.val) :=
  exists_torus_move_over_weyl _ (root_le_actual_index_three H hindex hcop) b

end SymmetricSubgroupAsymptotics.CFSGPSLTwoIndexThreeTorusFibre
