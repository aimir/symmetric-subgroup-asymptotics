import SymmetricSubgroupAsymptotics.Non2PreE7SaprimBinaryAffine
import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveInstances
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Odd primitive affine SAPRIM actions with cyclic complement

For `U = F_p^d ⋊ R`, every nontrivial normal axis is a quotient of `R`.
When `p` is odd and `R` is cyclic, all those quotients are cyclic and their
onto maps inject into the character group of the source abelianization.  The
bottom affine axis has slope `log₂(p)/p`, which is at most `log₂(3)/3` for
every odd prime.  Thus the whole literal normal menu is one pure cold row.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The elementary inequality `p³ ≤ 3ᵖ` for `p ≥ 3`. -/
theorem cube_le_three_pow {p : ℕ} (hp : 3 ≤ p) : p ^ 3 ≤ 3 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hlin : 3 * (p + 1) ≤ 4 * p := by omega
      have hc := Nat.pow_le_pow_left hlin 3
      simp only [mul_pow] at hc
      have hstep : (p + 1) ^ 3 ≤ 3 * p ^ 3 := by omega
      calc
        (p + 1) ^ 3 ≤ 3 * p ^ 3 := hstep
        _ ≤ 3 * 3 ^ p := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (p + 1) := by rw [pow_succ']

/-- Among primes at least three, `log₂(p)/p` is bounded by its value at
three.  The proof uses only `p³ ≤ 3ᵖ`. -/
theorem primeLogSlope_le_three {p : ℕ} (hp : 3 ≤ p) :
    Real.logb 2 p / p ≤ Real.logb 2 3 / 3 := by
  have hpowNat := cube_le_three_pow hp
  have hpow : ((p : ℝ) ^ (3 : ℕ)) ≤ (3 : ℝ) ^ p := by exact_mod_cast hpowNat
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (pow_pos (show (0 : ℝ) < (p : ℝ) by exact_mod_cast (show 0 < p by omega)) 3) hpow
  rw [Real.logb_pow, Real.logb_pow] at hlog
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  rw [div_le_div_iff₀ hpR (by norm_num : (0 : ℝ) < 3)]
  simpa [mul_comm] using hlog

/-- Onto maps to a finite cyclic group inject into the source character
group, and hence number at most the source abelianization. -/
theorem cyclicGroupEpimorphism_card_le_abelianization
    {J Q : Type*} [Group J] [Group Q] [Finite J] [Finite Q]
    (hQ : IsCyclic Q) :
    Nat.card (GroupEpimorphism J Q) ≤ Nat.card (Abelianization J) := by
  let e : Q ≃* Multiplicative (ZMod (Nat.card Q)) :=
    (zmodCyclicMulEquiv hQ).symm
  let label : GroupEpimorphism J Q →
      (J →* Multiplicative (ZMod (Nat.card Q))) :=
    fun f => e.toMonoidHom.comp f.1
  have hlabel : Function.Injective label := by
    intro f g h
    apply Subtype.ext
    apply MonoidHom.ext
    intro x
    exact e.injective (DFunLike.congr_fun h x)
  letI : NeZero (Nat.card Q) := ⟨Nat.card_pos.ne'⟩
  letI : Finite (J →* Multiplicative (ZMod (Nat.card Q))) :=
    Finite.of_injective
      (fun f : J →* Multiplicative (ZMod (Nat.card Q)) =>
        (f : J → Multiplicative (ZMod (Nat.card Q))))
      DFunLike.coe_injective
  exact (Nat.card_le_card_of_injective label hlabel).trans
    (cyclicCharacter_card_le_abelianization J (Nat.card Q))

namespace Non2UnipotentPrefixFiniteMenu

open AffineModel Equiv SemidirectProduct

/-- A fixed odd primitive affine action with cyclic nontrivial complement.
The last field is the finite coefficient check for this one action class. -/
structure PreE7SaprimOddCyclicAffineSource
    (w : ℕ) (i : PreE7NonPairActionClass w) : Type where
  p : ℕ
  [primeFact : Fact p.Prime]
  three_le : 3 ≤ p
  d : ℕ
  R : Subgroup (AffineModel.GLV p d)
  irreducible : AffineModel.Irreducible R
  length : AffineModel.DerivedLength R
  cyclic : IsCyclic R
  d_pos : 0 < d
  equiv : preE7NonPairAction w i ≃* AffineModel.Aff R
  width_lower : 7 ≤ w
  width_upper : w < 1024
  tail_menu : ∀ b,
    (Nat.card {N : Subgroup (preE7NonPairAction w i) // N.Normal} : ℝ) +
        Nat.card (AffineModel.Aff R ≃* AffineModel.Aff R) ≤
      (2 : ℝ) ^
        (16 * (w : ℝ) * Real.log ((w + b + 2 : ℕ) : ℝ) ^ 2)

attribute [instance] PreE7SaprimOddCyclicAffineSource.primeFact

namespace PreE7SaprimOddCyclicAffineSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}

private theorem bottom_epi_le (S : PreE7SaprimOddCyclicAffineSource w i) {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (AffineModel.Aff S.R)) : ℝ) ≤
      (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) *
        (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
  have h := (AffineModel.target S.irreducible S.length S.d_pos).epi_card_le_prime
    (J := J)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact mul_le_mul_of_nonneg_right (primeLogSlope_le_three S.three_le)
    (Nat.cast_nonneg b)

/-- Every literal normal axis is tail-paid at the common odd-prime slope. -/
def axis (S : PreE7SaprimOddCyclicAffineSource w i)
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w i) N PUnit
      (Real.logb 2 3 / 3) := by
  by_cases hN : N.1 = ⊥
  · refine .tail (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R))
      (Nat.cast_nonneg _) ?_
    intro b J
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* AffineModel.Aff S.R :=
      (QuotientGroup.quotientMulEquivOfEq hN).trans
        (QuotientGroup.quotientBot.trans S.equiv)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    exact S.bottom_epi_le J
  · refine .tail 1 zero_le_one ?_
    intro b J
    let N' : Subgroup (AffineModel.Aff S.R) := N.1.map S.equiv.toMonoidHom
    haveI hN' : N'.Normal := N.2.map _ S.equiv.surjective
    have hN'b : N' ≠ ⊥ := by
      intro hb
      apply hN
      rw [eq_bot_iff]
      intro x hx
      have hm : S.equiv x ∈ N' := ⟨x, hx, rfl⟩
      rw [hb] at hm
      exact (Subgroup.mem_bot).mpr
        (S.equiv.injective ((Subgroup.mem_bot).mp hm |>.trans (map_one _).symm))
    have hker : (SemidirectProduct.rightHom : AffineModel.Aff S.R →* S.R).ker ≤ N' := by
      rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
      exact AffineModel.Vsub_le_normal S.irreducible N' hN'b
    let M : Subgroup S.R := N'.map SemidirectProduct.rightHom
    haveI hM : M.Normal := hN'.map _ SemidirectProduct.rightHom_surjective
    let e : (preE7NonPairAction w i ⧸ N.1) ≃* (S.R ⧸ M) :=
      (QuotientGroup.congr N.1 N' S.equiv rfl).trans
        (quotientEquivOfKerLe SemidirectProduct.rightHom
          SemidirectProduct.rightHom_surjective N' hker)
    letI : IsCyclic S.R := S.cyclic
    letI : IsCyclic (S.R ⧸ M) :=
      isCyclic_of_surjective (QuotientGroup.mk' M)
        (QuotientGroup.mk'_surjective M)
    rw [fusionGroupEpimorphism_card_congr (MulEquiv.refl J) e]
    calc
      (Nat.card (GroupEpimorphism J (S.R ⧸ M)) : ℝ) ≤
          Nat.card (Abelianization J) := by
        exact_mod_cast cyclicGroupEpimorphism_card_le_abelianization
          (J := J) (Q := S.R ⧸ M) inferInstance
      _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := hKP b J
      _ = 1 * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
        rw [one_mul, three_rpow_third_eq]

private theorem axis_mainCoefficient (S : PreE7SaprimOddCyclicAffineSource w i)
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    (S.axis hKP N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le (S : PreE7SaprimOddCyclicAffineSource w i)
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w i) // N.Normal}) :
    (S.axis hKP N).tailCoefficient ≤
      1 + if N.1 = ⊥ then
        (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0 := by
  by_cases hN : N.1 = ⊥
  · simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]
  · simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

/-- The pure-tail additive data. -/
def toData (S : PreE7SaprimOddCyclicAffineSource w i)
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveData w i where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := Real.logb 2 3 / 3
  comparator_window := trivialSmallComparatorWindow (by
    have := S.width_lower
    omega : 6 ≤ w)
  tail_window := logThreeThird_le_window (by
    have := S.width_lower
    omega : 6 ≤ w)
  axis := S.axis hKP

/-- Complete numerical SAPRIM data for the odd cyclic-complement row. -/
noncomputable def numericalData (S : PreE7SaprimOddCyclicAffineSource w i)
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveNumericalData .saprim w i where
  data := S.toData hKP
  main_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    have hz :
        (∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
          ((S.toData hKP).certificate .saprim).C b N) = 0 := by
      apply Finset.sum_eq_zero
      intro N _
      exact S.axis_mainCoefficient hKP N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    unfold fusionAxisEnvelopeTotal
    let B : {N : Subgroup (preE7NonPairAction w i) // N.Normal} := ⟨⊥, inferInstance⟩
    calc
      (∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
          ((S.toData hKP).certificate .saprim).tailCoefficient b N) ≤
          ∑ N : {N : Subgroup (preE7NonPairAction w i) // N.Normal},
            ((1 : ℝ) + if N = B then
              (Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro N _
        have h := S.axis_tailCoefficient_le hKP N
        convert h using 1
        congr 2
        exact propext ⟨
          fun hn => by simpa [B] using congrArg Subtype.val hn,
          fun hn => Subtype.ext (by simpa [B] using hn)⟩
      _ = (Nat.card {N : Subgroup (preE7NonPairAction w i) // N.Normal} : ℝ) +
          Nat.card (AffineModel.Aff S.R ≃* AffineModel.Aff S.R) := by
        rw [Finset.sum_add_distrib]
        simp [B]
      _ ≤ _ := S.tail_menu b

end PreE7SaprimOddCyclicAffineSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
