import SymmetricSubgroupAsymptotics.Non2PreE7SmallAdditiveInstances
import SymmetricSubgroupAsymptotics.Non2PreE7SmallModelNumerics

/-!
# Numerical completion of the basic DIH and SAPRIM rows

The DIH and regular-prime SAPRIM certificates have no comparator term on
any literal normal axis.  Their tail coefficients are respectively bounded
by `|Aut(D_{2p})| + 1` and by one.  This file sums those coefficients and
places them inside the common subquadratic menu-mass envelope.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace Non2UnipotentPrefixFiniteMenu

private abbrev NormalAxis {w : ℕ} (i : PreE7NonPairActionClass w) :=
  {N : Subgroup (preE7NonPairAction w i) // N.Normal}

namespace PreE7DihSource

variable {w : ℕ} {i : PreE7NonPairActionClass w} (S : PreE7DihSource w i)

private def generators : Finset (DihedralGroup S.ℓ) :=
  {DihedralGroup.r 1, DihedralGroup.sr 0}

private theorem closure_generators :
    Subgroup.closure (S.generators : Set (DihedralGroup S.ℓ)) = ⊤ := by
  letI : NeZero S.ℓ := ⟨S.prime.ne_zero⟩
  apply top_unique
  rintro (x | x) _
  · have hr : DihedralGroup.r x = (DihedralGroup.r 1 : DihedralGroup S.ℓ) ^ x.val := by
      calc
        DihedralGroup.r x = DihedralGroup.r (x.val : ZMod S.ℓ) := by
          rw [ZMod.natCast_zmod_val]
        _ = (DihedralGroup.r 1 : DihedralGroup S.ℓ) ^ x.val :=
          (DihedralGroup.r_one_pow (n := S.ℓ) x.val).symm
    rw [hr]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [generators])) _
  · have hr : DihedralGroup.r x = (DihedralGroup.r 1 : DihedralGroup S.ℓ) ^ x.val := by
      calc
        DihedralGroup.r x = DihedralGroup.r (x.val : ZMod S.ℓ) := by
          rw [ZMod.natCast_zmod_val]
        _ = (DihedralGroup.r 1 : DihedralGroup S.ℓ) ^ x.val :=
          (DihedralGroup.r_one_pow (n := S.ℓ) x.val).symm
    rw [show DihedralGroup.sr x = DihedralGroup.sr 0 * DihedralGroup.r x by
      simp [DihedralGroup.sr_mul_r], hr]
    exact Subgroup.mul_mem _
      (Subgroup.subset_closure (by simp [generators]))
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp [generators])) _)

private theorem generators_card_le : S.generators.card ≤ 2 := by
  simp [generators]

private theorem aut_card_le_sq :
    Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) ≤ (2 * S.ℓ) ^ 2 := by
  letI : NeZero S.ℓ := ⟨S.prime.ne_zero⟩
  letI : Finite (DihedralGroup S.ℓ →* DihedralGroup S.ℓ) := Finite.of_injective
    (fun f : DihedralGroup S.ℓ →* DihedralGroup S.ℓ =>
      (f : DihedralGroup S.ℓ → DihedralGroup S.ℓ)) DFunLike.coe_injective
  have hautHom : Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) ≤
      Nat.card (DihedralGroup S.ℓ →* DihedralGroup S.ℓ) :=
    Nat.card_le_card_of_injective
      (fun e : DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ => e.toMonoidHom)
      (fun _ _ h => MulEquiv.ext (fun g => DFunLike.congr_fun h g))
  calc
    Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) ≤
        Nat.card (DihedralGroup S.ℓ →* DihedralGroup S.ℓ) := hautHom
    _ ≤ Nat.card (DihedralGroup S.ℓ) ^ S.generators.card :=
      monoidHom_card_le_pow_of_closure S.generators S.closure_generators
    _ ≤ Nat.card (DihedralGroup S.ℓ) ^ 2 :=
      Nat.pow_le_pow_right Nat.card_pos S.generators_card_le
    _ = (2 * S.ℓ) ^ 2 := by rw [DihedralGroup.nat_card]

private theorem axis_mainCoefficient (hKP : KovacsPraegerAbelianizationBound)
    (N : NormalAxis i) :
    (S.axis hKP N).mainCoefficient = 0 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient_le (hKP : KovacsPraegerAbelianizationBound)
    (N : NormalAxis i) :
    (S.axis hKP N).tailCoefficient ≤
      Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) + 1 := by
  by_cases hN : N.1 = ⊥ <;>
    simp [axis, hN, PreE7SmallAxisCertificate.tailCoefficient]

private theorem main_total_eq_zero (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
      (((S.toData hKP).certificate .dih).C b) = 0 := by
  unfold fusionAxisEnvelopeTotal
  apply Finset.sum_eq_zero
  intro N _
  change (S.axis hKP N).mainCoefficient = 0
  exact S.axis_mainCoefficient hKP N

private theorem tail_total_le (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
      (((S.toData hKP).certificate .dih).tailCoefficient b) ≤
      (2 : ℝ) ^ (6 * (w : ℝ)) := by
  unfold fusionAxisEnvelopeTotal
  have hℓw : S.ℓ ≤ w := by rcases S.degree with h | h <;> omega
  have haxisNat : Nat.card (NormalAxis i) ≤ 2 ^ (2 * w) := by
    calc
      Nat.card (NormalAxis i) ≤ 2 ^ Nat.card (preE7NonPairAction w i) :=
        normalAxis_card_le_two_pow_card _
      _ = 2 ^ (2 * S.ℓ) := by
        rw [Nat.card_congr S.equiv.toEquiv, DihedralGroup.nat_card]
      _ ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcoeffNat :
      Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) + 1 ≤ 2 ^ (4 * w) := by
    calc
      Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) + 1 ≤
          (2 * S.ℓ) ^ 2 + 1 := Nat.add_le_add_right S.aut_card_le_sq 1
      _ ≤ 2 * (2 * S.ℓ) ^ 2 + 1 := by omega
      _ ≤ 2 ^ (2 * (2 * S.ℓ)) := Nat.two_mul_sq_add_one_le_two_pow_two_mul _
      _ ≤ 2 ^ (4 * w) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc
    (∑ N : NormalAxis i,
        ((S.toData hKP).certificate .dih).tailCoefficient b N) ≤
        ∑ _N : NormalAxis i,
          (Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) + 1 : ℝ) := by
      apply Finset.sum_le_sum
      intro N _
      change (S.axis hKP N).tailCoefficient ≤ _
      exact S.axis_tailCoefficient_le hKP N
    _ = (Nat.card (NormalAxis i) : ℝ) *
        (Nat.card (DihedralGroup S.ℓ ≃* DihedralGroup S.ℓ) + 1 : ℝ) := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ ((2 ^ (2 * w) : ℕ) : ℝ) * ((2 ^ (4 * w) : ℕ) : ℝ) := by
      apply mul_le_mul <;> try positivity
      · exact_mod_cast haxisNat
      · exact_mod_cast hcoeffNat
    _ = ((2 ^ (6 * w) : ℕ) : ℝ) := by
      rw [← Nat.cast_mul, ← pow_add]
      congr 2
      omega
    _ = (2 : ℝ) ^ (6 * (w : ℝ)) := by
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [← Real.rpow_natCast]
      congr 1
      norm_num

/-- The full DIH numerical owner consumed by the ordinary T1 package. -/
noncomputable def numericalData (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveNumericalData .dih w i where
  data := S.toData hKP
  main_total_bound := fun b => by
    rw [S.main_total_eq_zero hKP b]
    positivity
  tail_total_bound := fun b =>
    (S.tail_total_le hKP b).trans
      (two_rpow_sixteen_width_le_menuMass (w := w)
        ((by norm_num : 4 ≤ 6).trans S.not_natural_small) b |>.trans' <| by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hw0 : (0 : ℝ) ≤ w := by positivity
        nlinarith)

end PreE7DihSource

namespace PreE7SaprimRegularPrimeSource

variable {w : ℕ} {i : PreE7NonPairActionClass w}
  (S : PreE7SaprimRegularPrimeSource w i)

private theorem axis_mainCoefficient (hKP : KovacsPraegerAbelianizationBound)
    (N : NormalAxis i) :
    (S.axis hKP N).mainCoefficient = 0 := by
  simp [axis, PreE7SmallAxisCertificate.mainCoefficient]

private theorem axis_tailCoefficient (hKP : KovacsPraegerAbelianizationBound)
    (N : NormalAxis i) :
    (S.axis hKP N).tailCoefficient = 1 := by
  simp [axis, PreE7SmallAxisCertificate.tailCoefficient]

private theorem main_total_eq_zero (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
      (((S.toData hKP).certificate .saprim).C b) = 0 := by
  unfold fusionAxisEnvelopeTotal
  apply Finset.sum_eq_zero
  intro N _
  change (S.axis hKP N).mainCoefficient = 0
  exact S.axis_mainCoefficient hKP N

private theorem tail_total_le (hKP : KovacsPraegerAbelianizationBound)
    (b : ℕ) :
    fusionAxisEnvelopeTotal (preE7NonPairAction w i)
      (((S.toData hKP).certificate .saprim).tailCoefficient b) ≤
      (2 : ℝ) ^ (w : ℝ) := by
  unfold fusionAxisEnvelopeTotal
  calc
    (∑ N : NormalAxis i,
        ((S.toData hKP).certificate .saprim).tailCoefficient b N) =
        Nat.card (NormalAxis i) := by
      simp_rw [show ∀ N : NormalAxis i,
          ((S.toData hKP).certificate .saprim).tailCoefficient b N = 1 from
        fun N => S.axis_tailCoefficient hKP N]
      simp
    _ ≤ (2 : ℝ) ^ (Nat.card (preE7NonPairAction w i) : ℝ) := by
      calc
        (Nat.card (NormalAxis i) : ℝ) ≤
            ((2 ^ Nat.card (preE7NonPairAction w i) : ℕ) : ℝ) := by
          exact_mod_cast normalAxis_card_le_two_pow_card (preE7NonPairAction w i)
        _ = _ := by rw [Real.rpow_natCast]; norm_num
    _ = (2 : ℝ) ^ (w : ℝ) := by
      have hcard : Nat.card (preE7NonPairAction w i) = w := by
        calc
          Nat.card (preE7NonPairAction w i) = S.p := by
            rw [Nat.card_congr S.equiv.toEquiv, Nat.card_congr Multiplicative.toAdd,
              Nat.card_zmod]
          _ = w := S.degree.symm
      congr 1
      exact_mod_cast hcard

/-- The regular-prime SAPRIM row with both finite totals required by T1. -/
noncomputable def numericalData (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveNumericalData .saprim w i where
  data := S.toData hKP
  main_total_bound := fun b => by
    rw [S.main_total_eq_zero hKP b]
    positivity
  tail_total_bound := fun b =>
    (S.tail_total_le hKP b).trans
      (two_rpow_sixteen_width_le_menuMass (w := w)
        ((by norm_num : 4 ≤ 6).trans S.width_ge_six) b |>.trans' <| by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        have hw0 : (0 : ℝ) ≤ w := by positivity
        nlinarith)

end PreE7SaprimRegularPrimeSource

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
