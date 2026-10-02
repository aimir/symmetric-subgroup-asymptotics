import SymmetricSubgroupAsymptotics.PrimitiveAffineSolubleDerivedTarget
import SymmetricSubgroupAsymptotics.PrimitiveAffineLargeOrderNumerics
import SymmetricSubgroupAsymptotics.Non2PreE7RankTailSourceDichotomyClosure
import SymmetricSubgroupAsymptotics.Non2PreE7SaprimOddCyclicAffine

/-!
# A catalogue-free SAPRIM source for soluble primitive affine groups

For a faithful primitive affine action, the point stabilizer acts faithfully
on the nonidentity translations.  Every nontrivial normal subgroup contains
the regular translation subgroup, so every nonbottom normal quotient is a
quotient of that one comparator.  If the point stabilizer is nontrivial and
soluble, the bottom quotient is paid by the derived cyclic-target theorem.

The finite coefficient totals are bounded uniformly from the intrinsic order
bound on a primitive affine group.  Thus the construction uses no finite
affine catalogue and introduces no new mathematical assumption.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- The nonidentity translations. -/
abbrev NonidentityTranslation := {v : P.V // v ≠ 1}

/-- Removing the identity from a finite group leaves one fewer element. -/
def optionNonidentityEquiv : Option P.NonidentityTranslation ≃ P.V where
  toFun
    | none => 1
    | some v => v
  invFun v := if h : v = 1 then none else some ⟨v, h⟩
  left_inv := by
    intro v
    cases v with
    | none => simp
    | some v => simp [v.2]
  right_inv := by
    intro v
    by_cases h : v = 1 <;> simp [h]

theorem nonidentity_card_add_one [Finite L] :
    Nat.card P.NonidentityTranslation + 1 = Nat.card P.V := by
  rw [← Finite.card_option, Nat.card_congr P.optionNonidentityEquiv]

theorem nonidentity_card [Finite L] :
    Nat.card P.NonidentityTranslation = Nat.card P.V - 1 := by
  have h := P.nonidentity_card_add_one
  omega

/-- Conjugation by the point stabilizer preserves the nonidentity
translations. -/
def nonidentityAction (x : Ω) :
    P.complement x →* Equiv.Perm P.NonidentityTranslation where
  toFun h :=
    { toFun := fun v => ⟨P.complementAction x h v, by
          intro hz
          apply v.2
          exact (P.complementAction x h).injective (hz.trans (map_one _).symm)⟩
      invFun := fun v => ⟨(P.complementAction x h).symm v, by
          intro hz
          apply v.2
          exact (P.complementAction x h).symm.injective
            (hz.trans (map_one _).symm)⟩
      left_inv := fun v => Subtype.ext ((P.complementAction x h).symm_apply_apply v)
      right_inv := fun v => Subtype.ext ((P.complementAction x h).apply_symm_apply v) }
  map_one' := Equiv.ext fun v => Subtype.ext (by
    simp)
  map_mul' h k := Equiv.ext fun v => Subtype.ext (by
    change (P.complementAction x (h * k)) v =
      P.complementAction x h (P.complementAction x k v)
    rw [map_mul]
    rfl)

theorem nonidentityAction_injective [FaithfulSMul L Ω] (x : Ω) :
    Function.Injective (P.nonidentityAction x) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  apply P.complementAction_injective x
  apply MulEquiv.ext
  intro v
  by_cases hv : v = 1
  · simp [hv]
  · let z : P.NonidentityTranslation := ⟨v, hv⟩
    have hz := DFunLike.congr_fun hh z
    simpa [z] using congrArg Subtype.val hz

end PrimitiveAffineProfile

/-! ## Uniform numerical estimates below the large-order cutoff -/

/-- Below `1024`, the logarithmic-square order parameter and its normal-menu
square are bounded by the elementary menu exponent. -/
theorem primitiveAffine_small_logSquare_menu_exponent
    {w : ℕ} (hw5 : 5 ≤ w) (hw1024 : w < 1024) :
    let m := (Nat.log 2 w + 1) ^ 2
    m * m + m ≤ if w < 8 then 36 * w else 64 * w := by
  dsimp
  by_cases hw8 : w < 8
  · rw [if_pos hw8]
    interval_cases w <;> norm_num [Nat.log]
  · rw [if_neg hw8]
    have hwpos : w ≠ 0 := by omega
    let l := Nat.log 2 w
    have hl3 : 3 ≤ l := by
      dsimp [l]
      apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
      norm_num
      omega
    have hl10 : l < 10 := by
      dsimp [l]
      rw [Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) (by omega : w ≠ 0)]
      norm_num
      exact hw1024
    have hpow : 2 ^ l ≤ w := Nat.pow_log_le_self 2 hwpos
    change ((l + 1) ^ 2) * ((l + 1) ^ 2) + (l + 1) ^ 2 ≤ 64 * w
    interval_cases l <;> norm_num at hpow ⊢ <;> omega

/-- The logarithmic-square order bound pays both the normal axes and the
automorphism constant at every width from `5` through `1023`. -/
theorem primitiveAffine_small_menu_bound
    {L : Type} [Group L] [Finite L]
    {w b : ℕ} (hw5 : 5 ≤ w) (hw1024 : w < 1024)
    (horder : Nat.card L ≤ 2 ^ ((Nat.log 2 w + 1) ^ 2)) :
    (Nat.card {N : Subgroup L // N.Normal} : ℝ) + Nat.card (L ≃* L) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  let m := (Nat.log 2 w + 1) ^ 2
  have hnormal : Nat.card {N : Subgroup L // N.Normal} ≤ 2 ^ (m * m) := by
    exact normalSubgroup_card_le_two_pow_sq m (by simpa [m] using horder)
  have haut : Nat.card (L ≃* L) ≤ 2 ^ (m * m) := by
    calc
      Nat.card (L ≃* L) ≤ Nat.card L ^ Nat.log 2 (Nat.card L) :=
        Non2UnipotentPrefixFiniteMenu.mulEquiv_card_le_card_pow_log L
      _ ≤ (2 ^ m) ^ Nat.log 2 (Nat.card L) :=
        Nat.pow_le_pow_left horder _
      _ ≤ (2 ^ m) ^ m := by
        apply Nat.pow_le_pow_right (by positivity)
        exact (Nat.log_mono_right (b := 2) horder).trans_eq
          (Nat.log_pow (by norm_num) m)
      _ = 2 ^ (m * m) := by rw [pow_mul]
  have hsum :
      Nat.card {N : Subgroup L // N.Normal} + Nat.card (L ≃* L) ≤
        2 ^ (m * m + 1) := by
    calc
      _ ≤ 2 ^ (m * m) + 2 ^ (m * m) := Nat.add_le_add hnormal haut
      _ = 2 ^ (m * m + 1) := by rw [pow_succ]; omega
  have hmpos : 1 ≤ m := by
    calc
      1 = 1 ^ 2 := by norm_num
      _ ≤ (Nat.log 2 w + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = m := by rfl
  have hexp : m * m + 1 ≤ if w < 8 then 36 * w else 64 * w :=
    (Nat.add_le_add_left hmpos (m * m)).trans
      (primitiveAffine_small_logSquare_menu_exponent hw5 hw1024)
  by_cases hw8 : w < 8
  · have hexp' : m * m + 1 ≤ 36 * w := by simpa [hw8] using hexp
    calc
      _ ≤ ((2 ^ (m * m + 1) : ℕ) : ℝ) := by exact_mod_cast hsum
      _ = (2 : ℝ) ^ ((m * m + 1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
      _ ≤ (2 : ℝ) ^ (36 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact_mod_cast hexp'
      _ ≤ _ := Non2UnipotentPrefixFiniteMenu.two_rpow_thirtySix_width_le_menuMass
        (w := w) (by omega) b
  · have hexp' : m * m + 1 ≤ 64 * w := by simpa [hw8] using hexp
    calc
      _ ≤ ((2 ^ (m * m + 1) : ℕ) : ℝ) := by exact_mod_cast hsum
      _ = (2 : ℝ) ^ ((m * m + 1 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
      _ ≤ (2 : ℝ) ^ (64 * (w : ℝ)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        exact_mod_cast hexp'
      _ ≤ _ := Non2UnipotentPrefixFiniteMenu.two_rpow_sixtyFour_width_le_menuMass
        (w := w) (by omega) b

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineSolubleSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}

private def translationEquiv
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) : P.NonidentityTranslation ≃ Fin (w - 1) := by
  apply Equiv.trans (Finite.equivFin P.NonidentityTranslation)
  apply finCongr
  rw [P.nonidentity_card, P.card_eq x]
  simp

private def comparatorAction
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) :
    P.complement x →* Equiv.Perm (Fin (w - 1)) :=
  (translationEquiv P x).permCongrHom.toMonoidHom.comp (P.nonidentityAction x)

private theorem comparatorAction_injective
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) :
    Function.Injective (comparatorAction P x) :=
  (translationEquiv P x).permCongrHom.injective.comp
    (P.nonidentityAction_injective x)

private theorem comparator_window (hw6 : 6 ≤ w) (hw1024 : w < 1024)
    (hweven : Even w) :
    preE7CharacterRho * w ≤
      ((evenWidth w : ℝ) - ((max 2 (w - 1) : ℕ) : ℝ)) / 8 := by
  have hmax : max 2 (w - 1) = w - 1 := by omega
  have heven : evenWidth w = w := by
    rcases hweven with ⟨k, rfl⟩
    unfold evenWidth halfDegree
    omega
  have hsub : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ w)]
    norm_num
  have hdiff : (evenWidth w : ℝ) - ((w - 1 : ℕ) : ℝ) = 1 := by
    rw [heven, hsub]
    ring
  unfold preE7CharacterRho
  rw [hmax]
  have hwR : (w : ℝ) ≤ 1024 := by exact_mod_cast (Nat.le_of_lt hw1024)
  rw [hdiff]
  norm_num
  linarith

private theorem common_tail_window (hw6 : 6 ≤ w) :
    Real.logb 2 3 / 3 ≤ preE7CharacterWindow w :=
  logThreeThird_le_window hw6

theorem primitiveAffine_primeSlope_le_common
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w)) :
    Real.logb 2 P.p / P.p ≤ Real.logb 2 3 / 3 := by
  by_cases hp2 : P.p = 2
  · norm_num [hp2, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    exact half_le_logThreeThird
  · have hp3 : 3 ≤ P.p := by
      have := P.p_prime.two_le
      omega
    exact primeLogSlope_le_three hp3

private theorem bottom_epi_le
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (D : SolubleDerivedLength (P.complement x)) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (preE7NonPairAction w U)) : ℝ) ≤
      (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h := (P.derivedCyclicTarget hprimitive x D).epi_card_le_prime J
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_right (primitiveAffine_primeSlope_le_common P)
    (Nat.cast_nonneg b)

/-- The one-projection model for a nontrivial soluble primitive affine
action. -/
def model
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (h6 : 6 ≤ w) (h1024 : w < 1024) (heven : Even w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (D0 : SolubleDerivedLength (P.complement x)) :
    PreE7NormalComparatorModel w U := by
  letI : Nontrivial (Fin w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  exact
    { G := preE7NonPairAction w U
      equiv := MulEquiv.refl _
      index := Unit
      R := P.complement x
      degree := w - 1
      action := comparatorAction P x
      action_injective := comparatorAction_injective P x
      proj := fun _ => P.complementProjection x
      proj_surjective := fun _ => P.complementProjection_surjective x
      normal_cover := by
        intro N hN hNb
        letI : N.Normal := hN
        refine ⟨(), ?_⟩
        rw [P.complementProjection_ker x]
        exact le_of_minimal_selfCentralizing P.V (P.minimal hp)
          (P.selfCentralizing hp) N hNb
      tailSlope := Real.logb 2 3 / 3
      tailConstant := Nat.card
        (preE7NonPairAction w U ≃* preE7NonPairAction w U)
      tailConstant_nonneg := Nat.cast_nonneg _
      tail := fun _ J => bottom_epi_le P h6 hp x D0 J
      comparator_window := comparator_window h6 h1024 heven
      tail_window := common_tail_window h6 }

private theorem menu
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hw6 : 6 ≤ w) (hw1024 : w < 1024) (b : ℕ) :
    (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) +
        Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2) := by
  apply primitiveAffine_small_menu_bound (by omega) hw1024
  let x0 : Fin w := ⟨0, by omega⟩
  exact P.card_le_two_pow_logSquare x0

/-- Complete numerical SAPRIM data for the soluble primitive affine source. -/
noncomputable def numericalData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (h6 : 6 ≤ w) (h1024 : w < 1024)
    (heven : Even w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (D0 : SolubleDerivedLength (P.complement x)) :
    PreE7SmallAdditiveNumericalData .saprim w U :=
  (model P x h6 h1024 heven hp D0).numericalData .saprim
    (fun b => (show (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) ≤
        (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) +
          Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) by
            exact le_add_of_nonneg_right (Nat.cast_nonneg _)).trans
        (menu P h6 h1024 b))
    (fun b => (show (Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) : ℝ) ≤
        (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) +
          Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) by
            exact le_add_of_nonneg_left (Nat.cast_nonneg _)).trans
        (menu P h6 h1024 b))

/-- The soluble primitive affine action as a concrete owner source used by
the T1 classifier. -/
noncomputable def toRankTailOwnerSource
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (h6 : 6 ≤ w) (h1024 : w < 1024)
    (heven : Even w)
    (hp : MulAction.IsPreprimitive (preE7NonPairAction w U) (Fin w))
    (D0 : SolubleDerivedLength (P.complement x)) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .saprim (.small
    (numericalData P x h6 h1024 heven hp D0))

end PrimitiveAffineSolubleSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
