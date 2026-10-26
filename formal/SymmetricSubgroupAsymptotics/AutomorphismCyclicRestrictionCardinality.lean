import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoSylowOuterNormalization
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! Restricting automorphisms to a cyclic subgroup reduces counting to
the ONE fixed-generator fibre. No accepted-image capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Pointwise
namespace SymmetricSubgroupAsymptotics.AutomorphismCyclicRestrictionCardinality
open OuterFixedElementEvaluationBound

variable {G : Type} [Group G] [Finite G]

private instance automorphismFinite : Finite (MulAut G) := Finite.of_injective
  (fun f : MulAut G => (f : G → G)) DFunLike.coe_injective

def restriction (S : Subgroup (MulAut G)) (P : Subgroup G)
    (hpreserve : ∀ f : S, ∀ p : P, f.val p.val ∈ P) : S →* MulAut P where
  toFun f := {
    toFun := fun p => ⟨f.val p.val,hpreserve f p⟩
    invFun := fun p => ⟨f.val.symm p.val,hpreserve f⁻¹ p⟩
    left_inv := fun p => Subtype.ext (f.val.symm_apply_apply p.val)
    right_inv := fun p => Subtype.ext (f.val.apply_symm_apply p.val)
    map_mul' := fun p q => Subtype.ext (f.val.map_mul p.val q.val) }
  map_one' := by ext p; rfl
  map_mul' := by intro f h; ext p; rfl

theorem card_le_fixed_mul_aut (S : Subgroup (MulAut G)) (P : Subgroup G) (x : G)
    (hP : P = Subgroup.zpowers x)
    (hpreserve : ∀ f : S, ∀ p : P, f.val p.val ∈ P)
    (hfullfixed : fixedAutomorphisms x ≤ S) :
    Nat.card S ≤ Nat.card (fixedAutomorphisms x) * Nat.card (MulAut P) := by
  let r := restriction S P hpreserve
  have hx : x ∈ P := by
    rw [hP]
    exact Subgroup.mem_zpowers x
  have hker (f : S) : f ∈ r.ker ↔ f.val x = x := by
    constructor
    · intro hf
      have he := congrArg (fun a : MulAut P => (a ⟨x,hx⟩).val) (MonoidHom.mem_ker.mp hf)
      exact he
    · intro hf
      apply MonoidHom.mem_ker.mpr
      apply MulEquiv.ext
      intro p
      apply Subtype.ext
      have hp : p.val ∈ Subgroup.zpowers x := by
        rw [←hP]
        exact p.property
      obtain ⟨k,hk⟩ := Subgroup.mem_zpowers_iff.mp hp
      change f.val p.val = p.val
      rw [←hk,map_zpow,hf]
  let j : fixedAutomorphisms x → r.ker := fun f =>
    ⟨⟨f.val,hfullfixed f.property⟩,(hker _).mpr f.property⟩
  have hj : Function.Bijective j := by
    constructor
    · intro f h he
      exact Subtype.ext (congrArg (fun k : r.ker => k.val.val) he)
    · intro k
      refine ⟨⟨k.val.val,(hker k.val).mp k.property⟩,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      rfl
  have hkcard : Nat.card r.ker = Nat.card (fixedAutomorphisms x) :=
    (Nat.card_congr (Equiv.ofBijective j hj)).symm
  have hprod : Nat.card r.ker * Nat.card r.range = Nat.card S := by
    rw [←Subgroup.index_ker,r.ker.card_mul_index]
  rw [←hprod,hkcard]
  exact Nat.mul_le_mul_left _ (Nat.card_le_card_of_injective r.range.subtype Subtype.val_injective)

end SymmetricSubgroupAsymptotics.AutomorphismCyclicRestrictionCardinality

namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoFixedFirstOuterReduction
open PrimitiveSocleRawStructure CFSGMathieuTwentyTwoElevenGeneration
open CFSGMathieuTwentyTwoSylowOuterNormalization OuterFixedElementEvaluationBound

private instance modelFinite : Finite CFSG.Models.Mathieu22 := Finite.of_injective
  (fun g : CFSG.Models.Mathieu22 => g.val) Subtype.val_injective

theorem preserving_card_le_ten_mul_fixed :
    Nat.card preservingAutomorphisms ≤ 10 * Nat.card (fixedAutomorphisms firstElement) := by
  have hpreserve : ∀ f : preservingAutomorphisms, ∀ p : selectedSylow,
      f.val p.val ∈ (selectedSylow : Subgroup CFSG.Models.Mathieu22) := by
    intro f p
    have hm := Subgroup.smul_mem_pointwise_smul p.val f.val
      (selectedSylow : Subgroup CFSG.Models.Mathieu22) p.property
    have he : f.val • (selectedSylow : Subgroup CFSG.Models.Mathieu22) =
        (selectedSylow : Subgroup CFSG.Models.Mathieu22) :=
      congrArg (fun Q : Sylow 11 CFSG.Models.Mathieu22 =>
        (Q : Subgroup CFSG.Models.Mathieu22)) f.property
    rwa [he] at hm
  have hfullfixed : fixedAutomorphisms firstElement ≤ preservingAutomorphisms := by
    intro f hf
    change f • selectedSylow = selectedSylow
    apply Sylow.ext
    change f • (selectedSylow : Subgroup CFSG.Models.Mathieu22) =
      (selectedSylow : Subgroup CFSG.Models.Mathieu22)
    rw [selectedSylow_eq_zpowers]
    change (Subgroup.zpowers firstElement).map f.toMonoidHom = Subgroup.zpowers firstElement
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (f firstElement) = Subgroup.zpowers firstElement
    rw [show f firstElement = firstElement from hf]
  have hh := AutomorphismCyclicRestrictionCardinality.card_le_fixed_mul_aut
    preservingAutomorphisms (selectedSylow : Subgroup CFSG.Models.Mathieu22) firstElement
    selectedSylow_eq_zpowers hpreserve hfullfixed
  letI : IsCyclic selectedSylow :=
    CFSGMathieuTwentyTwoElevenNormalizerSolvable.sylow_eleven_isCyclic selectedSylow
  have ha : Nat.card (MulAut (selectedSylow : Subgroup CFSG.Models.Mathieu22)) = 10 := by
    rw [IsCyclic.card_mulAut,CFSGMathieuTwentyTwoActualOrder.sylow_eleven_card]
    decide +kernel
  rw [ha] at hh
  simpa only [Nat.mul_comm] using hh

theorem outer_mul_eleven_le_twice_fixed [IsSimpleGroup CFSG.Models.Mathieu22] :
    Nat.card (Outer CFSG.Models.Mathieu22) * 11 ≤
      2 * Nat.card (fixedAutomorphisms firstElement) := by
  have hh := preserving_card_le_ten_mul_fixed
  rw [←outer_mul_fiftyFive_eq_preservingAutomorphisms] at hh
  have he : Nat.card (Outer CFSG.Models.Mathieu22) * 55 =
      (Nat.card (Outer CFSG.Models.Mathieu22) * 11) * 5 := by omega
  rw [he] at hh
  have hr : 10 * Nat.card (fixedAutomorphisms firstElement) =
      (2 * Nat.card (fixedAutomorphisms firstElement)) * 5 := by omega
  rw [hr] at hh
  exact Nat.le_of_mul_le_mul_right hh (by decide : 0 < 5)

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoFixedFirstOuterReduction
