import SymmetricSubgroupAsymptotics.FiniteExtensionSubgroupLiftCount
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Group
import Mathlib.Data.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Complete one-layer count, including every subgroup lift in a possibly
nonsplit abelian extension. The kernel intersection is proved invariant
under the WHOLE ambient extension, not merely under the lifted subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteAbelianExtensionWholeLayerCount
open FiniteExtensionSubgroupLiftCount
variable {E Q : Type} [Group E] [Group Q]

local instance subgroupFinite [Finite E] : Finite (Subgroup E) :=
  Finite.of_injective (fun K : Subgroup E => (K : Set E)) SetLike.coe_injective

abbrev FullImage (π : E →* Q) := {L : Subgroup E // L.map π=⊤}
abbrev InvariantKernel (π : E →* Q) := {K : Subgroup E // K≤π.ker ∧ K.Normal}

theorem intersection_normal (π : E →* Q) (hV : IsMulCommutative π.ker)
    (L : FullImage π) : (L.val⊓π.ker).Normal := by
  constructor
  intro n hn e
  have he : π e∈L.val.map π := by rw [L.property]; exact Subgroup.mem_top _
  obtain ⟨l,hl,hle⟩ := he
  have hv : l⁻¹*e∈π.ker := by
    change π (l⁻¹*e)=1
    rw [map_mul,map_inv,hle,inv_mul_cancel]
  have hc : (l⁻¹*e)*n=n*(l⁻¹*e) :=
    congrArg (fun z : π.ker => (z : E))
      ((isMulCommutative_iff.mp hV) ⟨l⁻¹*e,hv⟩ ⟨n,hn.2⟩)
  have hconj : e*n*e⁻¹=l*n*l⁻¹ := by
    calc
      e*n*e⁻¹=l*((l⁻¹*e)*n)*e⁻¹ := by group
      _=l*(n*(l⁻¹*e))*e⁻¹ := by rw [hc]
      _=l*n*l⁻¹ := by group
  constructor
  · rw [hconj]
    exact L.val.mul_mem (L.val.mul_mem hl hn.1) (L.val.inv_mem hl)
  · exact (inferInstance : π.ker.Normal).conj_mem n hn.2 e

private def encode (π : E →* Q) (hV : IsMulCommutative π.ker)
    (L : FullImage π) : Σ K : InvariantKernel π,LiftFamily π K.val :=
  ⟨⟨L.val⊓π.ker,inf_le_right,intersection_normal π hV L⟩,L.val,L.property,rfl⟩

private def forget (π : E →* Q)
    (a : Σ K : InvariantKernel π,LiftFamily π K.val) : FullImage π :=
  ⟨a.2.val,a.2.property.1⟩

private theorem encode_injective (π : E →* Q) (hV : IsMulCommutative π.ker) :
    Function.Injective (encode π hV) := by
  intro L M h
  exact congrArg (forget π) h

/-- Kernel choices AND ALL lift fibres are charged. No extension splitting,
semisimplicity, complete-lift assumption or capacity hypothesis is added. -/
theorem card_fullImage_le [Finite E] (π : E →* Q) (hπ : Function.Surjective π)
    (hV : IsMulCommutative π.ker) {d : ℕ} (f : Fin d → Q)
    (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (FullImage π) ≤ Nat.card (InvariantKernel π)*(Nat.card π.ker)^d := by
  letI : Fintype (InvariantKernel π) := Fintype.ofFinite _
  calc
    Nat.card (FullImage π) ≤ Nat.card (Σ K : InvariantKernel π,LiftFamily π K.val) :=
      Nat.card_le_card_of_injective (encode π hV) (encode_injective π hV)
    _ = ∑ K : InvariantKernel π,Nat.card (LiftFamily π K.val) := Nat.card_sigma
    _ ≤ ∑ _K : InvariantKernel π,(Nat.card π.ker)^d :=
      Finset.sum_le_sum (fun K _ => card_liftFamily_le π hπ K.val f hf)
    _ = Nat.card (InvariantKernel π)*(Nat.card π.ker)^d := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.FiniteAbelianExtensionWholeLayerCount
