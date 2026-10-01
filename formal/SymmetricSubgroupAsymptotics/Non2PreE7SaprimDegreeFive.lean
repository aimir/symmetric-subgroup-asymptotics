import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveInstances
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel

/-!
# The two degree-five SAPRIM actions

This file closes the regular `C5` and natural `D10` rows of the soluble
primitive affine owner.  The all-prime permutation-rank theorem gives the
sharp source exponent `log₂(5)/5`.  The cyclic action is paid directly;
the dihedral action sends every nonbottom literal normal quotient to the
regular `C2` comparator.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private theorem three_logFive_lt_seven :
    3 * Real.logb 2 5 < 7 := by
  have hp : ((5 : ℝ) ^ 3) < (2 : ℝ) ^ (7 : ℕ) := by norm_num
  have hl := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (pow_pos (by norm_num) 3) hp
  simp only [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one] at hl
  exact_mod_cast hl

private theorem logFiveFifth_le_window_five :
    Real.logb 2 5 / 5 ≤ preE7CharacterWindow 5 := by
  have hlog := three_logFive_lt_seven
  unfold preE7CharacterWindow preE7CharacterRho halfDegree
  norm_num at hlog ⊢
  linarith

private theorem cyclicFive_epi_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (Multiplicative (ZMod 5))) : ℝ) ≤
      (2 : ℝ) ^ ((Real.logb 2 5 / 5) * b) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Finite (J →* Multiplicative (ZMod 5)) := Finite.of_injective
    (fun f : J →* Multiplicative (ZMod 5) => (f : J → Multiplicative (ZMod 5)))
    DFunLike.coe_injective
  have hepi : Nat.card (GroupEpimorphism J (Multiplicative (ZMod 5))) ≤
      Nat.card (J →* Multiplicative (ZMod 5)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have hr : Module.finrank (ZMod 5) (PrimeCharacters 5 J) ≤ b / 5 := by
    simpa only [Nat.card_fin] using
      permutation_primeCharacterRank_le 5 J (Fin b)
  calc
    (Nat.card (GroupEpimorphism J (Multiplicative (ZMod 5))) : ℝ) ≤
        (Nat.card (J →* Multiplicative (ZMod 5)) : ℝ) := by exact_mod_cast hepi
    _ = (5 : ℝ) ^ Module.finrank (ZMod 5) (PrimeCharacters 5 J) := by
      rw [DerivedHead.card_hom_zmod_eq 5]
      push_cast
      rfl
    _ ≤ (5 : ℝ) ^ (b / 5) := pow_le_pow_right₀ (by norm_num) hr
    _ ≤ (2 : ℝ) ^ ((Real.logb 2 5 / 5) * b) :=
      DerivedHead.pow_floor_div_le_rpow 5 b (by norm_num)

private theorem dihedralFive_epi_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (DihedralGroup 5)) : ℝ) ≤
      (Nat.card (DihedralGroup 5 ≃* DihedralGroup 5) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 5 / 5) * b) := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := (dihedralDerivedCyclicDual (ℓ := 5) (by norm_num)).epi_card_le (J := J)
  rw [DerivedHead.card_hom_zmod_eq 5] at h
  have hr := primeRank_le_of_subgroup 5 J (commutator J)
  have hpow :
      (5 : ℝ) ^ Module.finrank (ZMod 5) (PrimeCharacters 5 (commutator J)) ≤
        (2 : ℝ) ^ ((Real.logb 2 5 / 5) * b) := by
    calc
      _ ≤ (5 : ℝ) ^ (b / 5) := pow_le_pow_right₀ (by norm_num) hr
      _ ≤ _ := DerivedHead.pow_floor_div_le_rpow 5 b (by norm_num)
  calc
    (Nat.card (GroupEpimorphism J (DihedralGroup 5)) : ℝ) ≤
        ((5 ^ Module.finrank (ZMod 5) (PrimeCharacters 5 (commutator J)) *
          Nat.card (DihedralGroup 5 ≃* DihedralGroup 5) : ℕ) : ℝ) := by
      exact_mod_cast h
    _ = (Nat.card (DihedralGroup 5 ≃* DihedralGroup 5) : ℝ) *
        (5 : ℝ) ^ Module.finrank (ZMod 5) (PrimeCharacters 5 (commutator J)) := by
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)

/-! ## Actual action predicates -/

structure PreE7SaprimC5Source (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  equiv : preE7NonPairAction w i ≃* Multiplicative (ZMod 5)
  degree : w = 5

structure PreE7SaprimD10Source (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  equiv : preE7NonPairAction w i ≃* DihedralGroup 5
  degree : w = 5

def c2PointEquiv : Multiplicative (ZMod 2) ≃ Fin 2 :=
  Multiplicative.toAdd.trans (ZMod.finEquiv 2).symm.toEquiv

def c2RegularAction : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 2) :=
  c2PointEquiv.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)))

theorem c2RegularAction_injective : Function.Injective c2RegularAction :=
  c2PointEquiv.permCongrHom.injective.comp MulAction.toPerm_injective

private theorem dihedralSign_surjective :
    Function.Surjective (dihedralSign (ℓ := 5)) := by
  intro x
  have hx : x = 1 ∨ x = Multiplicative.ofAdd (1 : ZMod 2) := by
    revert x
    decide
  rcases hx with rfl | rfl
  · exact ⟨DihedralGroup.r 0, rfl⟩
  · exact ⟨DihedralGroup.sr 0, rfl⟩

private theorem dihedralSign_ker_le_normal (N : Subgroup (DihedralGroup 5))
    (hN : N.Normal) (hne : N ≠ ⊥) :
    (dihedralSign (ℓ := 5)).ker ≤ N := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro x hx
  cases x with
  | r j => exact rotation_mem_of_normal_ne_bot (by norm_num) N hN hne j
  | sr j =>
      rw [MonoidHom.mem_ker] at hx
      change Multiplicative.ofAdd (1 : ZMod 2) = 1 at hx
      exact absurd hx (by decide)

namespace PreE7SaprimC5Source

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7SaprimC5Source w i)

def model : PreE7NormalComparatorModel w i where
  G := Multiplicative (ZMod 5)
  equiv := S.equiv
  index := Unit
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  proj := fun _ => 1
  proj_surjective := fun _ _ => ⟨1, Subsingleton.elim _ _⟩
  normal_cover := by
    intro N hN hne
    haveI : N.Normal := hN
    haveI : Fact (Nat.card (Multiplicative (ZMod 5))).Prime := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      exact ⟨by norm_num⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card N with h | h
    · exact absurd h hne
    · refine ⟨(), ?_⟩
      rw [h]
      exact le_top
  tailSlope := Real.logb 2 5 / 5
  tailConstant := 1
  tailConstant_nonneg := zero_le_one
  tail := fun b J => by simpa using cyclicFive_epi_le J
  comparator_window := by
    rw [S.degree]
    unfold preE7CharacterRho evenWidth halfDegree
    norm_num
  tail_window := by rw [S.degree]; exact logFiveFifth_le_window_five

noncomputable def numericalData : PreE7SmallAdditiveNumericalData .saprim w i := by
  let M := S.model
  apply M.numericalData .saprim
  · intro b
    calc
      (Nat.card {N : Subgroup (preE7NonPairAction w i) // N.Normal} : ℝ) ≤
          (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
      _ = (2 : ℝ) ^ (5 : ℝ) := by
        congr 1
        change (Nat.card (Multiplicative (ZMod 5)) : ℝ) = 5
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
        norm_num
      _ ≤ (2 : ℝ) ^ (16 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [S.degree]
        norm_num
      _ ≤ _ := two_rpow_sixteen_width_le_menuMass (S.degree ▸ by norm_num) b
  · intro b
    change (1 : ℝ) ≤ _
    exact Real.one_le_rpow (by norm_num) (by positivity)

end PreE7SaprimC5Source

namespace PreE7SaprimD10Source

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7SaprimD10Source w i)

def model : PreE7NormalComparatorModel w i where
  G := DihedralGroup 5
  equiv := S.equiv
  index := Unit
  R := Multiplicative (ZMod 2)
  degree := 2
  action := c2RegularAction
  action_injective := c2RegularAction_injective
  proj := fun _ => dihedralSign
  proj_surjective := fun _ => dihedralSign_surjective
  normal_cover := fun N hN hne => ⟨(), dihedralSign_ker_le_normal N hN hne⟩
  tailSlope := Real.logb 2 5 / 5
  tailConstant := Nat.card (DihedralGroup 5 ≃* DihedralGroup 5)
  tailConstant_nonneg := Nat.cast_nonneg _
  tail := fun b J => dihedralFive_epi_le J
  comparator_window := by
    rw [S.degree]
    unfold preE7CharacterRho evenWidth halfDegree
    norm_num
  tail_window := by rw [S.degree]; exact logFiveFifth_le_window_five

private theorem aut_card_le : Nat.card (DihedralGroup 5 ≃* DihedralGroup 5) ≤ 1000 := by
  have h := mulEquiv_card_le_card_pow_log (DihedralGroup 5)
  rw [DihedralGroup.nat_card] at h
  norm_num at h ⊢
  exact h

noncomputable def numericalData : PreE7SmallAdditiveNumericalData .saprim w i := by
  let M := S.model
  apply M.numericalData .saprim
  · intro b
    calc
      (Nat.card {N : Subgroup (preE7NonPairAction w i) // N.Normal} : ℝ) ≤
          (2 : ℝ) ^ (Nat.card M.G : ℝ) := M.normalAxis_card_cast_le_modelRpow
      _ = (2 : ℝ) ^ (10 : ℝ) := by
        congr 1
        change (Nat.card (DihedralGroup 5) : ℝ) = 10
        rw [DihedralGroup.nat_card]
        norm_num
      _ ≤ (2 : ℝ) ^ (16 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        rw [S.degree]
        norm_num
      _ ≤ _ := two_rpow_sixteen_width_le_menuMass (S.degree ▸ by norm_num) b
  · intro b
    change (Nat.card (DihedralGroup 5 ≃* DihedralGroup 5) : ℝ) ≤ _
    calc
      _ ≤ (1000 : ℝ) := by exact_mod_cast aut_card_le
      _ ≤ (2 : ℝ) ^ (16 * (w : ℝ)) := by
        rw [S.degree]
        norm_num
      _ ≤ _ := two_rpow_sixteen_width_le_menuMass (S.degree ▸ by norm_num) b

end PreE7SaprimD10Source

/-- The complete degree-five part of SAPRIM. -/
inductive PreE7SaprimDegreeFiveSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type
  | c5 (source : PreE7SaprimC5Source w i)
  | d10 (source : PreE7SaprimD10Source w i)

noncomputable def PreE7SaprimDegreeFiveSource.numericalData
    {w : ℕ} {i : PreE7NonPairActionClass w}
    (S : PreE7SaprimDegreeFiveSource w i) :
    PreE7SmallAdditiveNumericalData .saprim w i :=
  match S with
  | .c5 source => source.numericalData
  | .d10 source => source.numericalData

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
