import SymmetricSubgroupAsymptotics.OriginalKernelDualFixedGeneratorCount
import SymmetricSubgroupAsymptotics.FiniteTopKernelRankHot
import SymmetricSubgroupAsymptotics.EpimorphismKernelLabels

/-! Every actual top map retains its own source kernel. Top-generator values and actual dual
module generation bound the binary-character cost of its lift fibre. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorColdCount
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T]
  (top : Q →* T) (htop : Function.Surjective top)
  (A : Rep.{0} (ZMod 2) T) (E : OriginalKernelModuleChart top A)

include htop E in
 theorem cold_card_le {c : ℕ} (hgen : RepresentationGeneratedBy A.ρ.dual c) (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      (Nat.card (GroupEpimorphism J T) : ℝ)*
        (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*c)*b) := by
  let project : GroupEpimorphism J Q → GroupEpimorphism J T := fun phi =>
    ⟨top.comp phi.val,htop.comp phi.property⟩
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Finite (J →* T) := Finite.of_injective
    (fun f : J →* T => (f : J → T)) DFunLike.coe_injective
  letI : Fintype (GroupEpimorphism J T) := Fintype.ofFinite _
  have hf (theta : GroupEpimorphism J T) :
      (Nat.card {phi // project phi=theta} : ℝ) ≤
        (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*c)*b) := by
    have hr : (binaryCharacterRank theta.val.ker : ℝ) ≤ (51/200 : ℝ)*b := by
      by_contra hh
      exact hJ ⟨theta.val,theta.property,lt_of_not_ge hh⟩
    let embed : {phi // project phi=theta} → OriginalKernelDualFixedTopCount.Lift top theta.val :=
      fun phi => ⟨phi.val.val,congrArg Subtype.val phi.property⟩
    have hi : Function.Injective embed := by
      intro phi chi h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : OriginalKernelDualFixedTopCount.Lift top theta.val => z.val) h
    have hn := (Nat.card_le_card_of_injective embed hi).trans
      (OriginalKernelDualFixedGeneratorCount.fixed_top_card_le_log top A E theta.val theta.property hgen)
    have hnR : (Nat.card {phi // project phi=theta} : ℝ) ≤
        (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*
          (2 : ℝ)^((c * binaryCharacterRank theta.val.ker : ℕ) : ℝ) := by
      exact_mod_cast hn
    apply hnR.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) c]
  calc
    _ = ∑ theta : GroupEpimorphism J T,(Nat.card {phi // project phi=theta} : ℝ) := by
      rw [←Nat.card_congr (Equiv.sigmaFiberEquiv project),Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _theta : GroupEpimorphism J T,
        (Nat.card Q^Nat.log 2 (Nat.card T) : ℕ)*(2 : ℝ)^(((51/200 : ℝ)*c)*b) :=
      Finset.sum_le_sum (fun theta _ => hf theta)
    _ = _ := by simp [Nat.card_eq_fintype_card,mul_assoc]

end SymmetricSubgroupAsymptotics.FiniteTopBinaryDualKernelGeneratorColdCount
