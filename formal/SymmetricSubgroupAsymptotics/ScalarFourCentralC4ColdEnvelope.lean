import SymmetricSubgroupAsymptotics.ScalarFourCentralC4FixedTopCount
import SymmetricSubgroupAsymptotics.MarkedC4KernelHotCount
import SymmetricSubgroupAsymptotics.SymmetricThreeEmbeddedTopEpiEnvelope

/-! Cold central-C4 targets retain the FULL C4-character kernel test.
No binary-character rank is substituted for the marked character count. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
open Non2UnipotentPrefixFiniteMenu
variable {Q T : Type} [Group Q] [Group T] [Finite Q] [Finite T] {c d : ℕ}
  (D : ScalarFourCentralC4TopCoordinates Q T c d)

def coldCoefficient (_D : ScalarFourCentralC4TopCoordinates Q T c d) : ℝ := (Nat.card (T ≃* T) : ℝ)*(Nat.card Q^Nat.card T : ℕ)
def coldSlope : ℝ := 153/200+Real.logb 2 5/3

include D

theorem cold_card_le (hc : c≤3) (hd : d≤3) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬MarkedC4KernelHotCount.KernelHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ)≤
      (Nat.card (GroupEpimorphism J T) : ℝ)*
        ((Nat.card Q^Nat.card T : ℕ)*(2 : ℝ)^((153/200 : ℝ)*(b : ℝ))) := by
  let project : GroupEpimorphism J Q → GroupEpimorphism J T := fun phi =>
    ⟨D.top.comp phi.val,D.top_surjective.comp phi.property⟩
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Finite (J →* T) := Finite.of_injective
    (fun f : J →* T => (f : J → T)) DFunLike.coe_injective
  letI : Fintype (GroupEpimorphism J T) := Fintype.ofFinite _
  have hf (theta : GroupEpimorphism J T) :
      (Nat.card {phi // project phi=theta} : ℝ)≤
        (Nat.card Q^Nat.card T : ℕ)*(2 : ℝ)^((153/200 : ℝ)*(b : ℝ)) := by
    have hr : (Nat.card (theta.val.ker →* InvariantC4Scalar) : ℝ)≤
        (2 : ℝ)^((51/200 : ℝ)*(b : ℝ)) := by
      by_contra hh
      exact hJ ⟨theta.val,theta.property,lt_of_not_ge hh⟩
    let embed : {phi // project phi=theta} → D.TopFibre theta.val := fun phi =>
      ⟨phi.val,congrArg Subtype.val phi.property⟩
    have hi : Function.Injective embed := by
      intro phi chi h
      exact Subtype.ext (congrArg (fun z : D.TopFibre theta.val => z.val) h)
    have hn : 1≤Nat.card (theta.val.ker →* InvariantC4Scalar) := by
      letI : Finite (theta.val.ker →* InvariantC4Scalar) := Finite.of_injective
        (fun f : theta.val.ker →* InvariantC4Scalar => (f : theta.val.ker → InvariantC4Scalar)) DFunLike.coe_injective
      exact Nat.card_pos
    have hp : (Nat.card (theta.val.ker →* InvariantC4Scalar) : ℝ)^(max c d)≤
        (2 : ℝ)^((153/200 : ℝ)*(b : ℝ)) := by
      calc
        _ ≤ (Nat.card (theta.val.ker →* InvariantC4Scalar) : ℝ)^3 :=
          pow_le_pow_right₀ (by exact_mod_cast hn) (max_le hc hd)
        _ ≤ ((2 : ℝ)^((51/200 : ℝ)*(b : ℝ)))^3 :=
          pow_le_pow_left₀ (by positivity) hr 3
        _ = _ := by
          rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ)≤2)]
          congr 1
          ring
    have hh := (Nat.card_le_card_of_injective embed hi).trans
      (D.fixed_top_card_le theta.val theta.property)
    have hh' : (Nat.card {phi // project phi=theta} : ℝ)≤
        (Nat.card Q^Nat.card T : ℕ)*(Nat.card (theta.val.ker →* InvariantC4Scalar) : ℝ)^(max c d) := by
      exact_mod_cast hh
    exact hh'.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  calc
    _ = ∑ theta : GroupEpimorphism J T, (Nat.card {phi // project phi=theta} : ℝ) := by
      rw [←Nat.card_congr (Equiv.sigmaFiberEquiv project),Nat.card_sigma,Nat.cast_sum]
    _ ≤ ∑ _theta : GroupEpimorphism J T,
        (Nat.card Q^Nat.card T : ℕ)*(2 : ℝ)^((153/200 : ℝ)*(b : ℝ)) :=
      Finset.sum_le_sum (fun theta _ => hf theta)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_eq_nat_card]

theorem cold_envelope (hc : c≤3) (hd : d≤3)
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬MarkedC4KernelHotCount.KernelHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ)≤
      D.coldCoefficient*(2 : ℝ)^(coldSlope*b) := by
  have hcold := D.cold_card_le hc hd b J hJ
  have htop := SymmetricThreeEmbeddedTopEpiEnvelope.epi_card_le f hf hZmud lit b J
  apply hcold.trans
  calc
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ)*(2 : ℝ)^((153/200 : ℝ)*(b : ℝ))) :=
      mul_le_mul_of_nonneg_right htop (by positivity)
    _ = _ := by
      unfold coldCoefficient coldSlope
      rw [add_mul,Real.rpow_add (by norm_num)]
      ring

end SymmetricSubgroupAsymptotics.ScalarFourCentralC4TopCoordinates
