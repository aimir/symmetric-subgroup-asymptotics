import SymmetricSubgroupAsymptotics.CFSGRightInvariantImageCardinality
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

/-! Actual conjugate-subgroup image sizes charged to their pointwise
centralizers. The conjugating subgroup need not normalize the target. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality
variable {G : Type*} [Group G]

theorem conjugate_eq_of_mem_normalizer (R : Subgroup G) (g : G)
    (hg : g∈Subgroup.normalizer (R : Set G)) :
    R.map (MulAut.conj g).toMonoidHom=R := by
  apply SetLike.coe_injective
  change MulAut.conj g '' (R : Set G)=(R : Set G)
  exact Subgroup.mem_normalizer_iff_conj_image_eq.mp hg

theorem conjugate_mul (R : Subgroup G) (g c : G) :
    R.map (MulAut.conj (g*c)).toMonoidHom=
      (R.map (MulAut.conj c).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  change (g*c)*x*(g*c)⁻¹=g*(c*x*c⁻¹)*g⁻¹
  group

theorem conjugate_image_card_mul_centralizer_le (U R : Subgroup G) [Finite U] :
    Nat.card (Set.range (fun u : U=>R.map (MulAut.conj (u:G)).toMonoidHom))*
      Nat.card ((Subgroup.centralizer (R : Set G)).subgroupOf U)≤Nat.card U := by
  apply CFSGRightInvariantImageCardinality.image_card_mul_subgroup_le
  intro u c
  change R.map (MulAut.conj ((u:G)*(c.val:G))).toMonoidHom=_
  rw [conjugate_mul,conjugate_eq_of_mem_normalizer R (c.val:G)
    (Subgroup.centralizer_le_normalizer (R : Set G) c.property)]

end SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality
