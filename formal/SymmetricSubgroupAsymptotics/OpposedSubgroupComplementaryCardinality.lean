import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeeling
import Mathlib.Algebra.Group.Subgroup.Finite

/-! Complementary actual residual subgroups determine an inversion
cardinality. The word comparison is used only through a genuine positive
normalizer element; no whole-group order or Weyl recognition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OpposedSubgroupComplementaryCardinality
open CFSGOpposedSubgroupPeeling
variable {G : Type*} [Group G]

/-- A complementary word differs from o^-1*w by a positive normalizer.
Thus its actual positive residual lies in the inversion part of w. -/
theorem complementary_residual_le_inversion
    (U V R : Subgroup G) (o w c : G)
    (hopp : U.map (MulAut.conj o).toMonoidHom ≤ V)
    (hRU : R ≤ U)
    (hRc : R ≤ U.map (MulAut.conj c⁻¹).toMonoidHom)
    (hnormal : c*(o⁻¹*w)⁻¹ ∈ Subgroup.normalizer (U : Set G)) :
    R ≤ inversionPart U V w := by
  intro x hx
  refine ⟨hRU hx,?_⟩
  obtain ⟨u,hu,he⟩ := hRc hx
  change c⁻¹*u*(c⁻¹)⁻¹=x at he
  have hex : x=c⁻¹*u*c := by simpa only [inv_inv] using he.symm
  let d := c*(o⁻¹*w)⁻¹
  have hd : d ∈ Subgroup.normalizer (U : Set G) := hnormal
  have hc : c=d*o⁻¹*w := by dsimp only [d]; group
  have hu' : d⁻¹*u*d ∈ U :=
    (Subgroup.mem_normalizer_iff''.mp hd u).mp hu
  have hv : o*(d⁻¹*u*d)*o⁻¹ ∈ V :=
    hopp ⟨d⁻¹*u*d,hu',rfl⟩
  change w*x*w⁻¹ ∈ V
  have heq : w*x*w⁻¹=o*(d⁻¹*u*d)*o⁻¹ := by rw [hex,hc]; group
  rw [heq]
  exact hv

/-- A genuine one-peel product and complementary residual chart squeeze
both actual factors. The input cardinality concerns U and its two given
subgroups, not the order of the ambient group. -/
theorem inversion_card_eq_of_complementary_chart [Finite G]
    (U V R S : Subgroup G) (w : G)
    (hdis : Disjoint U V)
    (hfactor : ∀ x∈U, ∃ p∈U, ∃ b∈inversionPart U V w,
      x=p*b ∧ w*p*w⁻¹∈U)
    (hR : R ≤ remainderPart U U w)
    (hS : S ≤ inversionPart U V w)
    (hchart : Nat.card U=Nat.card R*Nat.card S) :
    Nat.card (inversionPart U V w)=Nat.card S := by
  have hpeel : Nat.card U=Nat.card (remainderPart U U w)*
      Nat.card (inversionPart U V w) :=
    card_eq_remainder_mul_inversion U V U w le_rfl inf_le_left hdis hfactor
  have hr : Nat.card R≤Nat.card (remainderPart U U w) := Subgroup.card_le_of_le hR
  have hs : Nat.card S≤Nat.card (inversionPart U V w) := Subgroup.card_le_of_le hS
  apply Nat.le_antisymm _ hs
  apply Nat.le_of_mul_le_mul_left _ (Nat.card_pos (α:=R))
  calc
    Nat.card R*Nat.card (inversionPart U V w) ≤
        Nat.card (remainderPart U U w)*Nat.card (inversionPart U V w) :=
      Nat.mul_le_mul_right _ hr
    _=Nat.card U := hpeel.symm
    _=Nat.card R*Nat.card S := hchart

end SymmetricSubgroupAsymptotics.OpposedSubgroupComplementaryCardinality
