import SymmetricSubgroupAsymptotics.ScalarFourCentralFixedTopCount
import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHot

/-! Cold central-repeat maps, with the whole finite-top sum explicitly
retained. Every cubic kernel is a subgroup of the same original source. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralTopCoordinates Q T c d)

private theorem card_le_uniform_fibres {X Y : Type} [Finite X] [Fintype Y]
    (f : X → Y) (m : ℕ) (hm : ∀ y : Y, Nat.card {x : X // f x = y} ≤ m) :
    Nat.card X≤Nat.card Y*m := by
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  exact (Finset.sum_le_sum (fun y _ => hm y)).trans_eq (by simp [Nat.card_eq_fintype_card])

include D

/-- The top epimorphism factor is displayed, not absorbed into a fixed
coefficient. The actual rank bounds c,d≤3 are structural target bounds. -/
theorem cold_card_le (hc : c≤3) (hd : d≤3) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬ FiniteTopKernelRankHot T (51/200) J) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (GroupEpimorphism J T) *
        (Nat.card Q ^ Nat.card T * 2^(3*((51*b)/200))) := by
  let project : GroupEpimorphism J Q → GroupEpimorphism J T := fun phi =>
    ⟨D.top.comp phi.val,D.top_surjective.comp phi.property⟩
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Finite (J →* T) := Finite.of_injective
    (fun f : J →* T => (f : J → T)) DFunLike.coe_injective
  letI : Fintype (GroupEpimorphism J T) := Fintype.ofFinite _
  have hf (theta : GroupEpimorphism J T) :
      Nat.card {phi // project phi=theta} ≤
        Nat.card Q ^ Nat.card T * 2^(3*((51*b)/200)) := by
    have hr : (binaryCharacterRank theta.val.ker : ℝ)≤(51/200)*b := by
      by_contra hh
      exact hJ ⟨theta.val,theta.property,lt_of_not_ge hh⟩
    have hr' : 200*binaryCharacterRank theta.val.ker≤51*b := by
      have hh : (200 : ℝ)*binaryCharacterRank theta.val.ker≤51*b := by linarith
      exact_mod_cast hh
    have hrn : binaryCharacterRank theta.val.ker≤(51*b)/200 := by omega
    let embed : {phi // project phi=theta} → D.TopFibre theta.val := fun phi =>
      ⟨phi.val,congrArg Subtype.val phi.property⟩
    have hi : Function.Injective embed := by
      intro phi chi h
      exact Subtype.ext (congrArg (fun z : D.TopFibre theta.val => z.val) h)
    exact (Nat.card_le_card_of_injective embed hi).trans
      ((D.fixed_top_card_le theta.val theta.property).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
          (Nat.mul_le_mul (max_le hc hd) hrn))))
  exact card_le_uniform_fibres project _ hf
end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
