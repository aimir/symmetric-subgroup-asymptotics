import SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSourceInvolution
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.GroupTheory.Commutator.Basic

/-! The literal normal radical inside the actual source. The source
involution is central modulo this radical because it commutes with the
actual complementary generators; no abstract Levi quotient is supplied. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSourceRadical
open CFSG.Models.Chevalley CFSGGTwoOriginalPositiveRootWords
open CFSGGTwoCharacteristicThreeMiddleCoordinateEquiv
open CFSGGTwoCharacteristicThreeMiddleSource CFSGGTwoCharacteristicThreeMiddleSourceInvolution
variable (K : Type) [Field K] [CharP K 3] [Finite K]

def radical : Subgroup (source K) := (Middle K).subgroupOf (source K)

theorem radical_normal : (radical K).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (middle_le_source K)).mpr
    (source_le_normalizer_middle K)

def radicalEquiv : radical K ≃* Middle K := Subgroup.subgroupOfEquivOfLe (middle_le_source K)

private theorem commutator_mul_right {G : Type*} [Group G] (t n h : G)
    (hc : t*h=h*t) : ⁅t,n*h⁆=⁅t,n⁆ := by
  have hi : h*t⁻¹=t⁻¹*h := (show Commute h t from hc.symm).inv_right.eq
  simp only [commutatorElement_def]
  calc
    t*(n*h)*t⁻¹*(n*h)⁻¹ = t*n*(h*t⁻¹)*h⁻¹*n⁻¹ := by group
    _ = t*n*(t⁻¹*h)*h⁻¹*n⁻¹ := by rw [hi]
    _ = t*n*t⁻¹*n⁻¹ := by group

theorem involution_commutator_mem (g : source K) : ⁅involution K,g⁆ ∈ radical K := by
  let L : Subgroup (Model CartanMatrix.G₂ K) :=
    Subgroup.closure {h | (∃ a : K, h=positiveModel K 0 a) ∨ h=shortWord K}
  have hLS : L ≤ source K := le_sup_right
  have hLN := hLS.trans (source_le_normalizer_middle K)
  have hset : (source K : Set (Model CartanMatrix.G₂ K)) =
      (Middle K : Set (Model CartanMatrix.G₂ K))*(L : Set (Model CartanMatrix.G₂ K)) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLN
  have hg : g.val ∈ (source K : Set (Model CartanMatrix.G₂ K)) := g.property
  rw [hset] at hg
  obtain ⟨n,hn,h,hh,hg⟩ := hg
  have hLC : L ≤ Subgroup.centralizer
      ({(involution K).val} : Set (Model CartanMatrix.G₂ K)) := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rcases hh with ⟨a,rfl⟩|rfl
    · exact (involution_positive_commute K a).symm
    · exact (involution_weyl_commute K).symm
  have hc : (involution K).val*h = h*(involution K).val :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hLC hh)).symm
  change ⁅(involution K).val,g.val⁆ ∈ Middle K
  rw [←hg,commutator_mul_right _ _ _ hc]
  have hnorm := source_le_normalizer_middle K (involution K).property
  have hn' : (involution K).val*n*((involution K).val)⁻¹ ∈ Middle K :=
    (Subgroup.mem_normalizer_iff.mp hnorm n).mp hn
  exact (Middle K).mul_mem hn' ((Middle K).inv_mem hn)

end SymmetricSubgroupAsymptotics.CFSGGTwoCharacteristicThreeMiddleSourceRadical
