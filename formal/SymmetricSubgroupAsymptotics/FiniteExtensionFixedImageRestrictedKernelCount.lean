import SymmetricSubgroupAsymptotics.FiniteExtensionRestrictedKernelCount

/-! At one fixed actual full quotient image, count all admissible kernels
and all whole lifts. The ACTUAL quotient generating tuple is retained:
no log of the top group order or count of other quotient images is charged. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteExtensionFixedImageRestrictedKernelCount
open FiniteExtensionFixedImageKernelLiftCount

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
local instance subtypeFintype {G : Type} [Finite G] (P : G → Prop) : Fintype {x // P x} :=
  Fintype.ofFinite _

variable {E Q : Type} [Group E] [Group Q] (π : E →* Q) (P : Subgroup E → Prop)
    (H : Subgroup Q)

abbrev Family := {L : Subgroup E // L.map π=H ∧ P (L⊓π.ker)}

def encode (L : Family π P H) :
    Σ K : FiniteExtensionRestrictedKernelCount.KernelFamily π P,Fibre π H K.val :=
  ⟨⟨L.val⊓π.ker,inf_le_right,L.property.2⟩,⟨L.val,L.property.1,rfl⟩⟩

theorem encode_injective : Function.Injective (encode π P H) := by
  intro L M h
  apply Subtype.ext
  exact congrArg
    (fun z : Σ K : FiniteExtensionRestrictedKernelCount.KernelFamily π P,Fibre π H K.val =>
      z.2.val) h

theorem card_family_le [Finite E] (hπ : Function.Surjective π) {d : ℕ}
    (f : Fin d → H) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (Family π P H)≤
      Nat.card (FiniteExtensionRestrictedKernelCount.KernelFamily π P)*(Nat.card π.ker)^d := by
  calc
    Nat.card (Family π P H)≤
        Nat.card (Σ K : FiniteExtensionRestrictedKernelCount.KernelFamily π P,Fibre π H K.val) :=
      Nat.card_le_card_of_injective (encode π P H) (encode_injective π P H)
    _=∑ K : FiniteExtensionRestrictedKernelCount.KernelFamily π P,Nat.card (Fibre π H K.val) :=
      Nat.card_sigma
    _≤∑ _K : FiniteExtensionRestrictedKernelCount.KernelFamily π P,(Nat.card π.ker)^d :=
      Finset.sum_le_sum (fun K _ => card_fibre_le π hπ H K.val f hf)
    _=Nat.card (FiniteExtensionRestrictedKernelCount.KernelFamily π P)*(Nat.card π.ker)^d := by
      simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul,Nat.card_eq_fintype_card]

end SymmetricSubgroupAsymptotics.FiniteExtensionFixedImageRestrictedKernelCount
