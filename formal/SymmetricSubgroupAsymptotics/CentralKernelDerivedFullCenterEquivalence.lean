import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.IsPerfect
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-! Genuine central extensions identify FULL centers, including after derived restriction. -/
noncomputable section
namespace SymmetricSubgroupAsymptotics.CentralKernelDerivedFullCenterEquivalence
variable {G S : Type*} [Group G] [Group S]

theorem normal_two_le_center (N : Subgroup G) [N.Normal] (hN : Nat.card N=2) :
    N ≤ Subgroup.center G := by
  obtain ⟨k,hk,huniq⟩ := (Nat.card_eq_two_iff' (1:N)).mp hN
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  let u : N := ⟨x,hx⟩
  by_cases hu : u=1
  · have hx1 : x=1 := congrArg Subtype.val hu
    simp only [hx1,mul_one,one_mul]
  let c : N := ⟨g*x*g⁻¹,(inferInstance : N.Normal).conj_mem x hx g⟩
  have hc : c≠1 := by
    intro h
    apply hu
    apply Subtype.ext
    have he := congrArg (fun z : G => g⁻¹*z*g) (congrArg Subtype.val h)
    simpa only [c,u,Subgroup.coe_one,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_left,
      mul_one,one_mul,inv_mul_cancel] using he
  have hcu : c=u := (huniq c hc).trans (huniq u hu).symm
  have he := congrArg (fun z : G => z*g) (congrArg Subtype.val hcu)
  simpa only [c,u,mul_assoc,inv_mul_cancel,one_mul,mul_one] using he

theorem kernel_eq_center (f : G →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center G) (hS : Subgroup.center S=⊥) :
    f.ker=Subgroup.center G := by
  apply le_antisymm hk
  intro x hx
  have hm : f x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨g, rfl⟩ := hf y
    exact (map_mul f g x).symm.trans
      ((congrArg f (Subgroup.mem_center_iff.mp hx g)).trans (map_mul f x g))
  rw [hS,Subgroup.mem_bot] at hm
  exact hm

def quotientFullCenterEquiv (f : G →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center G) (hS : Subgroup.center S=⊥) :
    G ⧸ Subgroup.center G ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq (kernel_eq_center f hf hk hS).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

theorem derived_surjective (f : G →* S) (hf : Function.Surjective f)
    [Group.IsPerfect S] : Function.Surjective (f.comp (commutator G).subtype) := by
  have hm : (commutator G).map f=⊤ := by
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr hf,←commutator_def,
      Group.IsPerfect.commutator_eq_top]
  intro z
  have hz : z ∈ (commutator G).map f := by rw [hm]; exact Subgroup.mem_top z
  obtain ⟨x,hx,rfl⟩ := hz
  exact ⟨⟨x,hx⟩,rfl⟩

def derivedFullCenterEquiv (f : G →* S) (hf : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center G) (hS : Subgroup.center S=⊥)
    [Group.IsPerfect S] :
    (commutator G) ⧸ Subgroup.center (commutator G) ≃* S := by
  let d := f.comp (commutator G).subtype
  apply quotientFullCenterEquiv d (derived_surjective f hf) _ hS
  intro x hx
  have hc : (x:G) ∈ Subgroup.center G := hk hx
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  exact Subtype.ext (hc (y:G))
end SymmetricSubgroupAsymptotics.CentralKernelDerivedFullCenterEquivalence
