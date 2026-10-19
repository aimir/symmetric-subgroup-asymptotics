import SymmetricSubgroupAsymptotics.MarkedC4GeneratorNumbers
import Mathlib.Data.Nat.Log

/-! Ordinary local normal-generator density for actual finite subgroups.
The bound is derived from actual generators; no published enumeration or
project-owned density premise is introduced. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalGeneratorDensity

variable {G : Type} [Group G] [Finite G]

/-- A normal generating set can be chosen no larger than an ordinary
minimal doubling generating set of the SAME actual subgroup. -/
theorem two_pow_normalGen_le_card (N : Subgroup G) [N.Normal] :
    2^normalGen N≤Nat.card N := by
  obtain ⟨S,hS,hcard⟩ := exists_generating_finset_card_le N
  let T : Finset G := S.image N.subtype
  have hcl : Subgroup.closure (T : Set G)=N := by
    change Subgroup.closure ((S.image N.subtype : Finset G) : Set G)=N
    rw [Finset.coe_image,← MonoidHom.map_closure,hS,← MonoidHom.range_eq_map,N.range_subtype]
  have hT : (T : Set G) ⊆ N := by
    intro g hg
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hg
    exact x.property
  have hn : Subgroup.normalClosure (T : Set G)=N := by
    rw [← Subgroup.normalClosure_closure_eq_normalClosure,hcl,Subgroup.normalClosure_eq_self]
  have hgen : normalGen N≤S.card :=
    (normalGen_le hT hn).trans (Finset.card_image_le)
  exact (Nat.pow_le_pow_right (by omega : 0<2) hgen).trans hcard

theorem normalGen_le_log_card (N : Subgroup G) [N.Normal] :
    normalGen N≤Nat.log 2 (Nat.card N) :=
  (Nat.le_log_iff_pow_le (by omega) (Nat.card_pos.ne')).mpr
    (two_pow_normalGen_le_card N)

/-- In particular the local rank is bounded by its actual log-order
packet, the density condition needed by the joint two-column splice. -/
theorem normalGen_le_clog_card (N : Subgroup G) [N.Normal] :
    normalGen N≤Nat.clog 2 (Nat.card N) := by
  apply (Nat.pow_le_pow_iff_right (by omega : 1<2)).mp
  exact (two_pow_normalGen_le_card N).trans (Nat.le_pow_clog (by omega) _)

end SymmetricSubgroupAsymptotics.MarkedC4.ActualNormalGeneratorDensity
