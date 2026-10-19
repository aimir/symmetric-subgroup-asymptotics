import SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHot

/-! Cold maps with a small actual binary kernel, with the whole finite-top
sum explicitly retained. No splitting or elementary-kernel hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)

private theorem card_le_uniform_fibres {X Y : Type} [Finite X] [Fintype Y]
    (f : X → Y) (m : ℕ) (hm : ∀ y : Y, Nat.card {x : X // f x = y} ≤ m) :
    Nat.card X≤Nat.card Y*m := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  exact (Finset.sum_le_sum (fun y _ => hm y)).trans_eq (by simp [Nat.card_eq_fintype_card])

include htop

/-- Every top map and its actual source kernel is retained. -/
theorem cold_card_le (hK : IsPGroup 2 top.ker) (m : ℕ)
    (hcard : Nat.card top.ker≤2^m) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬ FiniteTopKernelRankHot T (51/200) J) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (GroupEpimorphism J T) *
        (Nat.card Q ^ Nat.card T * 2^(m*((51*b)/200))) := by
  let project : GroupEpimorphism J Q → GroupEpimorphism J T := fun phi =>
    ⟨top.comp phi.val,htop.comp phi.property⟩
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Finite (J →* T) := Finite.of_injective
    (fun f : J →* T => (f : J → T)) DFunLike.coe_injective
  letI : Fintype (GroupEpimorphism J T) := Fintype.ofFinite _
  have hf (theta : GroupEpimorphism J T) :
      Nat.card {phi // project phi=theta} ≤
        Nat.card Q ^ Nat.card T * 2^(m*((51*b)/200)) := by
    have hr : (binaryCharacterRank theta.val.ker : ℝ)≤(51/200)*b := by
      by_contra hh
      exact hJ ⟨theta.val,theta.property,lt_of_not_ge hh⟩
    have hr' : 200*binaryCharacterRank theta.val.ker≤51*b := by
      have hh : (200 : ℝ)*binaryCharacterRank theta.val.ker≤51*b := by linarith
      exact_mod_cast hh
    have hrn : binaryCharacterRank theta.val.ker≤(51*b)/200 := by omega
    let embed : {phi // project phi=theta} → Fibre top theta.val := fun phi =>
      ⟨phi.val,congrArg Subtype.val phi.property⟩
    have hi : Function.Injective embed := by
      intro phi chi h
      exact Subtype.ext (congrArg (fun z : Fibre top theta.val => z.val) h)
    exact (Nat.card_le_card_of_injective embed hi).trans
      ((fixed_top_binary_card_le top theta.val theta.property hK m hcard).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul_left m hrn))))
  exact card_le_uniform_fibres project _ hf
end SymmetricSubgroupAsymptotics.FiniteTopKernelHomLiftCount
