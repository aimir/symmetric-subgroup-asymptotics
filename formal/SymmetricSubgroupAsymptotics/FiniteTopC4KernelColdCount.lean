import SymmetricSubgroupAsymptotics.C4CoordinateHomCount
import SymmetricSubgroupAsymptotics.MarkedC4KernelHotCount

/-! Cold lift counts for actual C4-coordinate kernels. Every top map has
its own SAME source kernel; the tail is the full C4 Hom count on that
kernel and is never replaced by a binary character rank. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteTopC4KernelColdCount
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)

include htop in
 theorem cold_card_le {c : ℕ} (e : top.ker →* (Fin c → C4CoordinateHomCount.C4))
    (he : Function.Injective e) (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬MarkedC4KernelHotCount.KernelHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (GroupEpimorphism J T) : ℝ)*
        (Nat.card Q^Nat.card T : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*c)*b) := by
  let project : GroupEpimorphism J Q → GroupEpimorphism J T := fun phi =>
    ⟨top.comp phi.val,htop.comp phi.property⟩
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Finite (J →* T) := Finite.of_injective
    (fun f : J →* T => (f : J → T)) DFunLike.coe_injective
  letI : Fintype (GroupEpimorphism J T) := Fintype.ofFinite _
  have hf (theta : GroupEpimorphism J T) :
      (Nat.card {phi // project phi=theta} : ℝ) ≤
        (Nat.card Q^Nat.card T : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*c)*b) := by
    have hr : (Nat.card (theta.val.ker →* C4CoordinateHomCount.C4) : ℝ) ≤
        (2 : ℝ)^((51/200 : ℝ)*b) := by
      by_contra hh
      exact hJ ⟨theta.val,theta.property,lt_of_not_ge hh⟩
    let embed : {phi // project phi=theta} → FiniteTopKernelHomLiftCount.Fibre top theta.val :=
      fun phi => ⟨phi.val,congrArg Subtype.val phi.property⟩
    have hi : Function.Injective embed := by
      intro phi chi h
      exact Subtype.ext (congrArg (fun z : FiniteTopKernelHomLiftCount.Fibre top theta.val => z.val) h)
    have hn := (Nat.card_le_card_of_injective embed hi).trans
      ((FiniteTopKernelHomLiftCount.fixed_top_card_le top theta.val theta.property).trans
        (Nat.mul_le_mul_left _ (C4CoordinateHomCount.card_le (F := theta.val.ker) e he)))
    have hnR : (Nat.card {phi // project phi=theta} : ℝ) ≤
        (Nat.card Q^Nat.card T : ℕ)*
          (Nat.card (theta.val.ker →* C4CoordinateHomCount.C4) : ℝ)^c := by
      exact_mod_cast hn
    apply hnR.trans
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg _) hr c
    have hexp : ((2 : ℝ)^((51/200 : ℝ)*b))^c=
        (2 : ℝ)^(((51/200 : ℝ)*c)*b) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
      congr 1
      ring
    rw [hexp] at hp
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  calc
    _ = ∑ theta : GroupEpimorphism J T,(Nat.card {phi // project phi=theta} : ℝ) := by
      rw [←Nat.card_congr (Equiv.sigmaFiberEquiv project),Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _theta : GroupEpimorphism J T,
        (Nat.card Q^Nat.card T : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*c)*b) :=
      Finset.sum_le_sum (fun theta _ => hf theta)
    _ = _ := by simp [Nat.card_eq_fintype_card,mul_assoc]

end SymmetricSubgroupAsymptotics.FiniteTopC4KernelColdCount
