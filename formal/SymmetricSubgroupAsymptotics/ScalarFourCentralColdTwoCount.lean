import SymmetricSubgroupAsymptotics.ScalarFourCentralColdEnvelope

/-! Width-twelve cold counting from ACTUAL central/active coordinate
ranks at most two. Both the complete finite top-map count and every
original kernel fibre are retained. This does not assert coordinate
existence for any group or representative. -/
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
coefficient. The actual rank bounds c,d≤2 are structural target bounds. -/
theorem cold_card_le_two (hc : c≤2) (hd : d≤2) (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬ FiniteTopKernelRankHot T (51/200) J) :
    Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (GroupEpimorphism J T) *
        (Nat.card Q ^ Nat.card T * 2^(2*((51*b)/200))) := by
  let project : GroupEpimorphism J Q → GroupEpimorphism J T := fun phi =>
    ⟨D.top.comp phi.val,D.top_surjective.comp phi.property⟩
  letI : Finite (J →* Q) := Finite.of_injective
    (fun f : J →* Q => (f : J → Q)) DFunLike.coe_injective
  letI : Finite (J →* T) := Finite.of_injective
    (fun f : J →* T => (f : J → T)) DFunLike.coe_injective
  letI : Fintype (GroupEpimorphism J T) := Fintype.ofFinite _
  have hf (theta : GroupEpimorphism J T) :
      Nat.card {phi // project phi=theta} ≤
        Nat.card Q ^ Nat.card T * 2^(2*((51*b)/200)) := by
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

def coldSlopeTwo : ℝ := 102/200+Real.logb 2 5/3

theorem cold_envelope_two (hc : c≤2) (hd : d≤2)
    (f : T →* Equiv.Perm (Fin 3)) (hf : Function.Injective f)
    (hZmud : ZmudFaithfulCharacterTupleInput) (lit : PreE7CharacterLiterature)
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b)))
    (hJ : ¬FiniteTopKernelRankHot T (51/200) J) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      D.coldCoefficient*(2 : ℝ)^(coldSlopeTwo*b) := by
  have hn := D.cold_card_le_two hc hd b J hJ
  have htop := SymmetricThreeEmbeddedTopEpiEnvelope.epi_card_le f hf hZmud lit b J
  have hexp : ((2*((51*b)/200) : ℕ) : ℝ)≤(102/200)*b := by
    have hh : 200*((51*b)/200)≤51*b := by omega
    have hh' : (200 : ℝ)*((51*b)/200 : ℕ)≤51*b := by exact_mod_cast hh
    push_cast
    nlinarith
  have hp : ((2^(2*((51*b)/200)) : ℕ) : ℝ)≤
      (2 : ℝ)^((102/200 : ℝ)*(b : ℝ)) := by
    rw [Nat.cast_pow,Nat.cast_ofNat,← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hexp
  have hn' : (Nat.card (GroupEpimorphism J Q) : ℝ)≤
      (Nat.card (GroupEpimorphism J T) : ℝ)*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*((2^(2*((51*b)/200)) : ℕ) : ℝ) := by
    have hnreal := (Nat.cast_le (α := ℝ)).mpr hn
    simpa only [Nat.cast_mul,mul_assoc] using hnreal
  calc
    _ ≤ _ := hn'
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*((2^(2*((51*b)/200)) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htop (by positivity)) (by positivity)
    _ ≤ ((Nat.card (T ≃* T) : ℝ)*(2 : ℝ)^((Real.logb 2 5/3)*b))*
        ((Nat.card Q^Nat.card T : ℕ) : ℝ)*(2 : ℝ)^((102/200 : ℝ)*(b : ℝ)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by
      unfold coldCoefficient coldSlopeTwo
      rw [Nat.cast_mul,add_mul,Real.rpow_add (by norm_num)]
      ring
end SymmetricSubgroupAsymptotics.ScalarFourCentralTopCoordinates
