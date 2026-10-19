import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Original normal axes containing a fixed original normal subgroup
inject into the normal axes of its quotient. The corresponding quotient
maps have exactly equal epimorphism counts; no normal-axis multiplicity
is introduced by passing to the actual quotient. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalNormalQuotientAxisInjection
variable {G : Type} [Group G] (Z : Subgroup G) [Z.Normal]

abbrev Above := {N : {N : Subgroup G // N.Normal} // Z≤N.val}
instance axis_normal (N : Above Z) : N.val.val.Normal := N.val.property

def axis (N : Above Z) : {M : Subgroup (G ⧸ Z) // M.Normal} :=
  ⟨N.val.val.map (QuotientGroup.mk' Z),
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective Z)⟩

theorem axis_injective : Function.Injective (axis Z) := by
  intro N M h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg (fun L : {L : Subgroup (G ⧸ Z) // L.Normal} =>
    L.val.comap (QuotientGroup.mk' Z)) h
  change (N.val.val.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z)=
    (M.val.val.map (QuotientGroup.mk' Z)).comap (QuotientGroup.mk' Z) at he
  have hN : (QuotientGroup.mk' Z).ker≤N.val.val := by
    rw [QuotientGroup.ker_mk']
    exact N.property
  have hM : (QuotientGroup.mk' Z).ker≤M.val.val := by
    rw [QuotientGroup.ker_mk']
    exact M.property
  simpa only [Subgroup.comap_map_eq_self hN,Subgroup.comap_map_eq_self hM] using he

instance image_axis_normal (N : Above Z) : (axis Z N).val.Normal := (axis Z N).property

def quotientEquiv (N : Above Z) :
    (G ⧸ Z) ⧸ (axis Z N).val ≃* G ⧸ N.val.val :=
  QuotientGroup.quotientQuotientEquivQuotient Z N.val.val N.property

theorem epi_card {J : Type} [Group J] (N : Above Z) :
    Nat.card (GroupEpimorphism J (G ⧸ N.val.val))=
      Nat.card (GroupEpimorphism J ((G ⧸ Z) ⧸ (axis Z N).val)) :=
  (fusionGroupEpimorphism_card_congr (MulEquiv.refl J) (quotientEquiv Z N)).symm

end SymmetricSubgroupAsymptotics.OriginalNormalQuotientAxisInjection
