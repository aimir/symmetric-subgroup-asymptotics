import SymmetricSubgroupAsymptotics.CFSGCentralTwistedProductCoordinates
import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.SetTheory.Cardinal.Finite

/-! Two actual disjoint cells give a subgroup-order lower bound. The
shifted cell retains its actual opposed inversion subgroup; no BN-pair
or group order formula is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTwoBruhatCellsCardinality
open CFSGCentralTwistedProductCoordinates
variable {G : Type*} [Group G]

def twoCellValue (B X : Subgroup G) (w : G) : B⊕(B×X) → G
  | Sum.inl b => b.val
  | Sum.inr p => p.1.val*w*p.2.val

private theorem word_mem_of_cells_meet (B X : Subgroup G) (w : G)
    (hXB : X≤B) (a b : B) (x : X) (he : a.val=b.val*w*x.val) : w∈B := by
  have hw : w=b.val⁻¹*a.val*x.val⁻¹ := by rw [he];group
  rw [hw]
  exact B.mul_mem (B.mul_mem (B.inv_mem b.property) a.property)
    (B.inv_mem (hXB x.property))

theorem twoCellValue_injective (B V X : Subgroup G) (w : G)
    (hXB : X≤B) (hBV : Disjoint B V) (hw : w∉B)
    (hX : ∀x : X,w*x.val*w⁻¹∈V) : Function.Injective (twoCellValue B X w) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subtype.ext he)
    | inr b => exact False.elim (hw (word_mem_of_cells_meet B X w hXB a b.1 b.2 he))
  | inr a =>
    cases b with
    | inl b => exact False.elim (hw (word_mem_of_cells_meet B X w hXB b a.1 a.2 he.symm))
    | inr b =>
      exact congrArg Sum.inr
        (shifted_product_factors_injective B V w X.subtype Subtype.val_injective hBV hX he)

theorem card_mul_one_add_le [Finite G] (B V X P : Subgroup G) (w : G)
    (hXB : X≤B) (hBP : B≤P) (hWP : w∈P) (hBV : Disjoint B V) (hw : w∉B)
    (hX : ∀x : X,w*x.val*w⁻¹∈V) :
    Nat.card B*(1+Nat.card X)≤Nat.card P := by
  let f : B⊕(B×X) → P := fun z=>⟨twoCellValue B X w z,by
    cases z with
    | inl b => exact hBP b.property
    | inr p => exact P.mul_mem (P.mul_mem (hBP p.1.property) hWP) (hBP (hXB p.2.property))⟩
  have hf : Function.Injective f := by
    intro a b he
    exact twoCellValue_injective B V X w hXB hBV hw hX
      (congrArg (fun z : P=>z.val) he)
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_sum,Nat.card_prod,mul_add,mul_one] using hc

theorem word_not_mem_of_nontrivial_inversion (B U V X : Subgroup G) (w : G)
    (hB : B≤Subgroup.normalizer (U : Set G)) (hXU : X≤U) (hUV : Disjoint U V)
    (hX : ∀x : X,w*x.val*w⁻¹∈V) (hne : Nat.card X≠1) : w∉B := by
  intro hw
  have hn := Subgroup.mem_normalizer_iff.mp (hB hw)
  have hbot : X=⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    change x=1
    have he : w*x*w⁻¹=1 := Subgroup.disjoint_def.mp hUV
      ((hn x).mp (hXU hx)) (hX ⟨x,hx⟩)
    apply (MulAut.conj w).injective
    exact he.trans (map_one (MulAut.conj w)).symm
  apply hne
  rw [hbot,Subgroup.card_bot]

end SymmetricSubgroupAsymptotics.CFSGTwoBruhatCellsCardinality
