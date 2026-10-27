import SymmetricSubgroupAsymptotics.FiniteExtensionSubgroupLiftCount
import SymmetricSubgroupAsymptotics.FiniteExtensionSelfNormalizingKernelLift
import SymmetricSubgroupAsymptotics.ActualComplementSubgroupCocycleCode

/-! ALL whole lifts at a fixed actual kernel K inject into genuine
complements in N_E(K)/K. Only K is normal in its normalizer; normality
of K in E, splitting, or a quotient-class capacity is never assumed.
The decoder recovers the entire original subgroup in E. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualFixedKernelNormalizerComplement
open FiniteExtensionSubgroupLiftCount

variable {E Q : Type} [Group E] [Group Q] (π : E →* Q) (K : Subgroup E)

abbrev Normalizer := Subgroup.normalizer (K : Set E)
abbrev Axis := K.subgroupOf (Normalizer K)
abbrev Quotient := Normalizer K ⧸ Axis K

def quotientProjection (hK : K≤π.ker) : Quotient K →* Q :=
  QuotientGroup.lift (Axis K) (π.comp (Normalizer K).subtype) (by
    intro g hg
    exact hK hg)

theorem quotientProjection_mk (hK : K≤π.ker) (g : Normalizer K) :
    quotientProjection π K hK (QuotientGroup.mk' (Axis K) g)=π g.val :=
  rfl

def image (L : LiftFamily π K) : Subgroup (Quotient K) :=
  (L.val.subgroupOf (Normalizer K)).map (QuotientGroup.mk' (Axis K))

def toComplement (hK : K≤π.ker) (L : LiftFamily π K) :
    ActualComplementSubgroupCocycleCode.Family (quotientProjection π K hK) := by
  have hLN : L.val≤Normalizer K :=
    FiniteExtensionSelfNormalizingKernelLift.le_normalizer_of_intersection_kernel π L.val K L.property.2
  refine ⟨image π K L,?_,?_⟩
  · apply eq_top_iff.mpr
    intro y _
    have hy : y∈L.val.map π := by rw [L.property.1]; trivial
    obtain ⟨g,hg,he⟩ := hy
    refine ⟨QuotientGroup.mk' (Axis K) ⟨g,hLN hg⟩,
      ⟨⟨g,hLN hg⟩,hg,rfl⟩,?_⟩
    exact (quotientProjection_mk π K hK _).trans he
  · apply le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨g,hg,he⟩ := hx.1
    have hπ : π g.val=1 := by
      have hh : quotientProjection π K hK x=1 := hx.2
      rw [←he,quotientProjection_mk] at hh
      exact hh
    have hgK : g.val∈K := by
      exact (show L.val⊓π.ker≤K from le_of_eq L.property.2) ⟨hg,hπ⟩
    have hq : QuotientGroup.mk' (Axis K) g=1 := (QuotientGroup.eq_one_iff _).mpr hgK
    change x∈(⊥ : Subgroup (Quotient K))
    rw [Subgroup.mem_bot]
    exact he.symm.trans hq

def decode (U : Subgroup (Quotient K)) : Subgroup E :=
  (U.comap (QuotientGroup.mk' (Axis K))).map (Normalizer K).subtype

theorem decode_image (L : LiftFamily π K) : decode K (image π K L)=L.val := by
  have hLN : L.val≤Normalizer K :=
    FiniteExtensionSelfNormalizingKernelLift.le_normalizer_of_intersection_kernel π L.val K L.property.2
  have hKL : K≤L.val := (le_of_eq L.property.2.symm).trans inf_le_left
  have hk : (QuotientGroup.mk' (Axis K)).ker≤L.val.subgroupOf (Normalizer K) := by
    rw [QuotientGroup.ker_mk']
    intro g hg
    exact hKL hg
  unfold decode image
  rw [Subgroup.comap_map_eq_self hk]
  exact Subgroup.map_subgroupOf_eq_of_le hLN

theorem toComplement_injective (hK : K≤π.ker) :
    Function.Injective (toComplement π K hK) := by
  intro L M h
  apply Subtype.ext
  have hh := congrArg (fun U : ActualComplementSubgroupCocycleCode.Family
    (quotientProjection π K hK) => decode K U.val) h
  exact (decode_image π K L).symm.trans (hh.trans (decode_image π K M))

theorem card_liftFamily_le_complementFamily [Finite E] (hK : K≤π.ker) :
    Nat.card (LiftFamily π K)≤
      Nat.card (ActualComplementSubgroupCocycleCode.Family (quotientProjection π K hK)) := by
  letI : Finite (Subgroup (Quotient K)) :=
    Finite.of_injective (fun U : Subgroup (Quotient K) => (U : Set (Quotient K))) SetLike.coe_injective
  exact Nat.card_le_card_of_injective (toComplement π K hK) (toComplement_injective π K hK)

end SymmetricSubgroupAsymptotics.ActualFixedKernelNormalizerComplement
