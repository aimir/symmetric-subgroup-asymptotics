import SymmetricSubgroupAsymptotics.FiniteExtensionQuotientImageCount
import SymmetricSubgroupAsymptotics.FiniteExtensionSubgroupLiftCount

/-! At the SAME literal image and kernel intersection, all whole lift
subgroups cost at most |kerπ|^d. Image restriction is an actual preimage
extension; neither splitting nor normality of the fixed kernel is assumed. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteExtensionFixedImageKernelLiftCount
open FiniteExtensionSubgroupLiftCount

local instance subgroupFinite {G : Type} [Group G] [Finite G] : Finite (Subgroup G) :=
  Finite.of_injective (fun K : Subgroup G => (K : Set G)) SetLike.coe_injective

variable {E Q : Type} [Group E] [Group Q]

abbrev Fibre (π : E →* Q) (H : Subgroup Q) (K : Subgroup E) :=
  {L : Subgroup E // L.map π=H ∧ L⊓π.ker=K}

def toLiftFamily (π : E →* Q) (H : Subgroup Q) (K : Subgroup E) (L : Fibre π H K) :
    LiftFamily (π.subgroupComap H) (K.subgroupOf (H.comap π)) := by
  let A := FiniteExtensionQuotientImageCount.toFullImage π H ⟨L.val,L.property.1⟩
  refine ⟨A.val,A.property,?_⟩
  ext x
  constructor
  · intro hx
    have hp : π x.val=1 := congrArg (fun y : H => y.val) hx.2
    exact (show L.val⊓π.ker≤K from le_of_eq L.property.2) ⟨hx.1,hp⟩
  · intro hx
    have hm := (show K≤L.val⊓π.ker from le_of_eq L.property.2.symm) hx
    exact ⟨hm.1,Subtype.ext hm.2⟩

theorem toLiftFamily_injective (π : E →* Q) (H : Subgroup Q) (K : Subgroup E) :
    Function.Injective (toLiftFamily π H K) := by
  intro L M h
  have hv := congrArg (fun F : LiftFamily (π.subgroupComap H)
    (K.subgroupOf (H.comap π)) => F.val) h
  have hh : FiniteExtensionQuotientImageCount.toFullImage π H ⟨L.val,L.property.1⟩=
      FiniteExtensionQuotientImageCount.toFullImage π H ⟨M.val,M.property.1⟩ :=
    Subtype.ext hv
  have he := FiniteExtensionQuotientImageCount.toFullImage_injective π H hh
  exact Subtype.ext (congrArg (fun F : FiniteExtensionQuotientImageCount.ImageFibre π H => F.val) he)

def preimageKernelEquiv (π : E →* Q) (H : Subgroup Q) :
    (π.subgroupComap H).ker ≃ π.ker where
  toFun x := ⟨x.val.val,congrArg (fun y : H => y.val) x.property⟩
  invFun n := ⟨⟨n.val,by change π n.val∈H; rw [n.property]; exact H.one_mem⟩,
    Subtype.ext n.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_fibre_le [Finite E] (π : E →* Q) (hπ : Function.Surjective π)
    (H : Subgroup Q) (K : Subgroup E) {d : ℕ}
    (f : Fin d → H) (hf : Subgroup.closure (Set.range f)=⊤) :
    Nat.card (Fibre π H K)≤(Nat.card π.ker)^d := by
  have hi := Nat.card_le_card_of_injective (toLiftFamily π H K) (toLiftFamily_injective π H K)
  have hb := card_liftFamily_le (π.subgroupComap H)
    (π.subgroupComap_surjective_of_surjective H hπ) (K.subgroupOf (H.comap π)) f hf
  have he : Nat.card (π.subgroupComap H).ker=Nat.card π.ker :=
    Nat.card_congr (preimageKernelEquiv π H)
  exact hi.trans (by simpa only [he] using hb)

end SymmetricSubgroupAsymptotics.FiniteExtensionFixedImageKernelLiftCount
