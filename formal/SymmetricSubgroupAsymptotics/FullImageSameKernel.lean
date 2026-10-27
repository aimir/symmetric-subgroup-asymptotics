import SymmetricSubgroupAsymptotics.FiniteAbelianExtensionWholeLayerCount

/-! Onto-image subgroup families depend on the literal kernel, not the
chosen isomorphic target. This binds fixed-image preimage extensions to
the actual quotient chart used by the closed elementary-layer count. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FullImageSameKernel
open FiniteAbelianExtensionWholeLayerCount

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

variable {E B C : Type} [Group E] [Group B] [Group C]

def code (pi : E →* B) (psi : E →* C) (hpsi : Function.Surjective psi)
    (hker : pi.ker=psi.ker) (L : FullImage pi) : FullImage psi := by
  refine ⟨L.val,?_⟩
  apply top_unique
  intro c _
  obtain ⟨g,rfl⟩ := hpsi c
  have hg : pi g∈L.val.map pi := by rw [L.property]; exact Subgroup.mem_top _
  obtain ⟨u,hu,hug⟩ := hg
  have hk : u*g⁻¹∈pi.ker := by
    change pi (u*g⁻¹)=1
    rw [map_mul,map_inv,hug,mul_inv_cancel]
  rw [hker] at hk
  have he : psi u=psi g := by
    have hm : psi (u*g⁻¹)=1 := hk
    rw [map_mul,map_inv] at hm
    exact mul_inv_eq_one.mp hm
  exact ⟨u,hu,he⟩

theorem code_injective (pi : E →* B) (psi : E →* C) (hpsi : Function.Surjective psi)
    (hker : pi.ker=psi.ker) : Function.Injective (code pi psi hpsi hker) := by
  intro L M h
  exact Subtype.ext (congrArg (fun z : FullImage psi => z.val) h)

theorem card_le [Finite E] (pi : E →* B) (psi : E →* C)
    (hpsi : Function.Surjective psi) (hker : pi.ker=psi.ker) :
    Nat.card (FullImage pi)≤Nat.card (FullImage psi) :=
  Nat.card_le_card_of_injective (code pi psi hpsi hker)
    (code_injective pi psi hpsi hker)

end SymmetricSubgroupAsymptotics.FullImageSameKernel
