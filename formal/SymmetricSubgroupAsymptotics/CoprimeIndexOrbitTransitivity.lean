import SymmetricSubgroupAsymptotics.IntravariantNormalizerOrbitTransitivity
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Set.Card

/-! Coprime subgroup indices fill actual orbits, without normality of the
subgroup. This is the coprime-index step in the nonsplit-torus exclusions. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CoprimeIndexOrbitTransitivity
variable {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]

/-- This concerns arbitrary actual subgroups, not merely normal subgroups. -/
theorem index_inf_eq_mul (H K : Subgroup G) (hcop : H.index.Coprime K.index) :
    (H ⊓ K).index=H.index*K.index := by
  apply Nat.le_antisymm (Subgroup.index_inf_le (H:=H) (K:=K))
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (H ⊓ K).index_ne_zero_of_finite)
  exact hcop.mul_dvd_of_dvd_of_dvd
    (Subgroup.index_dvd_of_le inf_le_left) (Subgroup.index_dvd_of_le inf_le_right)

/-- Coprimality is with the actual orbit degree, which need not be the degree
of the entire possibly intransitive point set. -/
theorem orbit_eq (H : Subgroup G) (x : X)
    (hcop : H.index.Coprime (MulAction.stabilizer G x).index) :
    MulAction.orbit H x=MulAction.orbit G x := by
  let K := MulAction.stabilizer G x
  have hi := index_inf_eq_mul H K hcop
  have hm := Subgroup.relIndex_mul_index (H:=H ⊓ K) (K:=H) inf_le_left
  rw [Subgroup.inf_relIndex_left,hi] at hm
  have hr : K.relIndex H=K.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero H.index_ne_zero_of_finite)
    simpa only [mul_comm] using hm
  have hs : MulAction.stabilizer H x=K.subgroupOf H := rfl
  apply Set.eq_of_subset_of_ncard_le
  · rintro y ⟨h,hh⟩
    exact ⟨h.val,hh⟩
  · rw [←MulAction.index_stabilizer G x,←MulAction.index_stabilizer H x,hs]
    exact hr.ge
  · exact Set.toFinite _

/-- An intravariant normalizer of coprime actual local index forces the same
mapped subgroup to be normal in the original minimally transitive group. -/
theorem mapped_normal_of_coprime_normalizer_index [MulAction.IsPretransitive G X]
    (hmin : ∀ N : Subgroup G,MulAction.IsPretransitive N X → N=⊤)
    (L : Subgroup G) [L.Normal] (H : Subgroup L) (hInv : CFSGReduction.Intravariant H)
    (hcop : ∀ x : X,(Subgroup.normalizer (H : Set L)).index.Coprime
      (MulAction.stabilizer L x).index) : (H.map L.subtype).Normal := by
  apply IntravariantNormalizerOrbitTransitivity.mapped_subgroup_normal_of_minimal_transitive
    hmin L H hInv
  intro x l
  let N := Subgroup.normalizer (H : Set L)
  have he := orbit_eq N x (hcop x)
  have hm : l • x ∈ MulAction.orbit N x := he.symm ▸ MulAction.mem_orbit x l
  obtain ⟨n,hn⟩ := hm
  refine ⟨n.val,?_,hn⟩
  exact H.le_normalizer_map L.subtype ⟨n.val,n.property,rfl⟩

end SymmetricSubgroupAsymptotics.CoprimeIndexOrbitTransitivity
