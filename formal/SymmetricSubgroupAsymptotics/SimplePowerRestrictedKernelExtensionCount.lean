import SymmetricSubgroupAsymptotics.FiniteExtensionFullImageRestrictedKernelCount
import SymmetricSubgroupAsymptotics.SimpleCoordinateSupportCount

/-! Complete extension counts when actual kernel intersections have normal
simple-coordinate images. Every literal support, diagonal, quotient image
and whole lift is retained. The quotient-order version is intended for
base quotients such as (R/Soc R)^t; fixed-top images instead retain their
actual generating tuple, never a log of the permutation-top order. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SimplePowerRestrictedKernelExtensionCount

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective

variable {E Q J T : Type} [Group E] [Group Q] [Group T] [Finite T] [IsSimpleGroup T]
    [Finite J] (π : E →* Q) (e : π.ker ≃* (J → T))

def KernelPredicate (K : Subgroup E) : Prop :=
  ∀ j : J,(SimpleCoordinateSupportCover.coordinate (fun _ : J => T)
    ((K.subgroupOf π.ker).map e.toMonoidHom) j).range.Normal

def kernelCode (K : FiniteExtensionRestrictedKernelCount.KernelFamily π (KernelPredicate π e)) :
    SimpleCoordinateSupportCover.Family (fun _ : J => T) :=
  ⟨(K.val.subgroupOf π.ker).map e.toMonoidHom,K.property.2⟩

theorem kernelCode_injective : Function.Injective (kernelCode π e) := by
  intro K M h
  have hm := congrArg (fun U : SimpleCoordinateSupportCover.Family (fun _ : J => T) => U.val) h
  have hs := Subgroup.map_injective e.injective hm
  have ha := congrArg (fun U : Subgroup π.ker => U.map π.ker.subtype) hs
  apply Subtype.ext
  simpa only [Subgroup.map_subgroupOf_eq_of_le K.property.1,
    Subgroup.map_subgroupOf_eq_of_le M.property.1] using ha

theorem card_kernelFamily_le (hZ : IsCenterless T) :
    Nat.card (FiniteExtensionRestrictedKernelCount.KernelFamily π (KernelPredicate π e))≤
      2^(Nat.card J)*(2*(1+Nat.card J*Nat.card (T ≃* T)))^(Nat.card J) :=
  (Nat.card_le_card_of_injective (kernelCode π e) (kernelCode_injective π e)).trans
    (SimpleCoordinateSupportCount.card_family_le T hZ J)

theorem card_family_le_of_quotient_card [Finite E] [Finite Q]
    (hπ : Function.Surjective π) (hZ : IsCenterless T)
    (d : ℕ) (hQ : Nat.card Q≤2^d) :
    Nat.card (FiniteExtensionRestrictedKernelCount.Family π (KernelPredicate π e))≤
      2^(d*d)*(2^(Nat.card J)*(2*(1+Nat.card J*Nat.card (T ≃* T)))^(Nat.card J))*
        (Nat.card T)^(Nat.card J*d) := by
  have hb := FiniteExtensionRestrictedKernelCount.card_family_le_of_quotient_card
    π (KernelPredicate π e) hπ d hQ
  have hk := card_kernelFamily_le π e hZ
  have hc : Nat.card π.ker=(Nat.card T)^(Nat.card J) :=
    (Nat.card_congr e.toEquiv).trans Nat.card_fun
  calc
    _≤2^(d*d)*
        Nat.card (FiniteExtensionRestrictedKernelCount.KernelFamily π (KernelPredicate π e))*
          (Nat.card π.ker)^d := hb
    _≤2^(d*d)*(2^(Nat.card J)*(2*(1+Nat.card J*Nat.card (T ≃* T)))^(Nat.card J))*
        (Nat.card π.ker)^d := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hk)
    _=_ := by rw [hc,←pow_mul]

theorem card_fullImage_family_le [Finite E] (hπ : Function.Surjective π)
    (hZ : IsCenterless T) {d : ℕ} (f : Fin d → Q)
    (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (FiniteExtensionFullImageRestrictedKernelCount.Family π (KernelPredicate π e))≤
      (2^(Nat.card J)*(2*(1+Nat.card J*Nat.card (T ≃* T)))^(Nat.card J))*
        (Nat.card T)^(Nat.card J*d) := by
  have hb := FiniteExtensionFullImageRestrictedKernelCount.card_family_le
    π (KernelPredicate π e) hπ f hf
  have hk := card_kernelFamily_le π e hZ
  have hc : Nat.card π.ker=(Nat.card T)^(Nat.card J) :=
    (Nat.card_congr e.toEquiv).trans Nat.card_fun
  exact hb.trans (by simpa only [hc,←pow_mul] using Nat.mul_le_mul_right ((Nat.card π.ker)^d) hk)

end SymmetricSubgroupAsymptotics.SimplePowerRestrictedKernelExtensionCount
