import SymmetricSubgroupAsymptotics.StandardThreeLinearChiefCertificates
import SymmetricSubgroupAsymptotics.ProjectiveThreeSimplicity
import Mathlib.GroupTheory.IndexNormal

/-! The actual index-two subgroup of GL3(3) is its determinant kernel.
The proof restricts the actual quotient map to the simple determinant
kernel. It does not identify a subgroup from its order in isolation. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups

local instance indexTwoPrimeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem subgroup_eq_determinantKernel_of_card5616
    (H : Subgroup (GeneralThree 3)) (hH : Nat.card H=5616) :
    H=determinantKernelThree := by
  have hi : H.index=2 := by
    have hm := H.card_mul_index
    rw [hH,card_GL_three] at hm
    omega
  letI : H.Normal := H.normal_of_index_eq_two hi
  letI : IsSimpleGroup determinantKernelThree :=
    simple_determinantKernelThree ProjectiveThreeSimplicity.proved
  let f : determinantKernelThree →* (GeneralThree 3⧸H) :=
    (QuotientGroup.mk' H).comp determinantKernelThree.subtype
  have hcardQ : Nat.card (GeneralThree 3⧸H)=2 := by
    rw [←H.index_eq_card,hi]
  have hle : determinantKernelThree≤H := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
    · have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hb
      have hc := Nat.card_le_card_of_injective f hf
      rw [card_determinantKernelThree,hcardQ] at hc
      omega
    · intro g hg
      have hm : (⟨g,hg⟩ : determinantKernelThree)∈f.ker := by
        rw [ht]
        trivial
      have hz : QuotientGroup.mk' H g=1 := hm
      exact (QuotientGroup.eq_one_iff g).mp hz
  exact (Subgroup.eq_of_le_of_card_ge hle (by
    rw [hH,card_determinantKernelThree])).symm

/-- Recognition through a given faithful map, retaining its actual image. -/
def equivSpecialThree_of_card5616
    {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f)
    (hL : Nat.card L=5616) : L ≃* SpecialThree 3 := by
  let e := MonoidHom.ofInjective hf
  have he : Nat.card f.range=5616 := (Nat.card_congr e.toEquiv).symm.trans hL
  exact e.trans ((MulEquiv.subgroupCongr
    (subgroup_eq_determinantKernel_of_card5616 f.range he)).trans
      (specialLinearKerEquiv 3).symm)

def equivGeneralThree_of_card11232
    {L : Type} [Group L] [Finite L]
    (f : L →* GeneralThree 3) (hf : Function.Injective f)
    (hL : Nat.card L=11232) : L ≃* GeneralThree 3 := by
  let e := MonoidHom.ofInjective hf
  have he : Nat.card f.range=11232 := (Nat.card_congr e.toEquiv).symm.trans hL
  have ht : f.range=⊤ := Subgroup.eq_of_le_of_card_ge le_top (by
    simpa only [Subgroup.card_top,card_GL_three] using he.ge)
  exact e.trans ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)

end SymmetricSubgroupAsymptotics.StandardThreeDimensionalLinearGroups
