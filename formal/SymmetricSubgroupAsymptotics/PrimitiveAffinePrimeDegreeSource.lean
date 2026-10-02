import SymmetricSubgroupAsymptotics.PrimitiveAffineOrderTailSource
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Prime-degree affine profiles have cyclic complements

If an affine profile has prime degree, its regular subgroup has that prime
order.  Its automorphism group is the unit group of the corresponding prime
field and is cyclic.  Faithfulness of the point-stabilizer conjugation action
therefore makes the literal complement cyclic, so the profile-native cyclic
SAPRIM source applies without a catalogue witness.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

namespace PrimitiveAffineProfile

variable {L : Type} [Group L] {w : ℕ} [MulAction L (Fin w)]
  [Finite L]
  (P : PrimitiveAffineProfile L (Fin w))

/-- A prime affine degree equals the profile prime, so the translation space
has dimension one. -/
theorem profilePrime_eq_of_degree_prime (x : Fin w) (hw : w.Prime) :
    P.p = w := by
  obtain ⟨d, hd⟩ := P.degree_eq_prime_power x
  exact (hw.pow_eq_iff.mp hd.symm).1

/-- The regular translation subgroup at prime degree is cyclic. -/
theorem translation_isCyclic_of_degree_prime
    (x : Fin w) (hw : w.Prime) : IsCyclic P.V := by
  have hpw : P.p = w := P.profilePrime_eq_of_degree_prime x hw
  have hVcard : Nat.card P.V = P.p := by
    calc
      Nat.card P.V = Nat.card (Fin w) := P.card_eq x
      _ = w := by simp
      _ = P.p := hpw.symm
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  exact isCyclic_of_prime_card hVcard

/-- The stabilizer in a prime-degree affine profile is cyclic. -/
theorem complement_isCyclic_of_degree_prime
    [FaithfulSMul L (Fin w)]
    (x : Fin w) (hw : w.Prime) : IsCyclic (P.complement x) := by
  have hpw : P.p = w := P.profilePrime_eq_of_degree_prime x hw
  have hVcard : Nat.card P.V = P.p := by
    calc
      Nat.card P.V = Nat.card (Fin w) := P.card_eq x
      _ = w := by simp
      _ = P.p := hpw.symm
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : IsCyclic P.V := P.translation_isCyclic_of_degree_prime x hw
  have hUnits : IsCyclic (ZMod (Nat.card P.V))ˣ := by
    rw [hVcard]
    exact ZMod.isCyclic_units_prime P.p_prime
  letI : IsCyclic (ZMod (Nat.card P.V))ˣ := hUnits
  letI : IsCyclic (MulAut P.V) :=
    isCyclic_of_injective (IsCyclic.mulAutMulEquiv P.V).toMonoidHom
      (IsCyclic.mulAutMulEquiv P.V).injective
  exact isCyclic_of_injective (P.complementAction x)
    (P.complementAction_injective x)

end PrimitiveAffineProfile

namespace Non2UnipotentPrefixFiniteMenu

namespace PrimitiveAffinePrimeDegreeSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}

private def cyclicAxis
    (hcyclic : IsCyclic (preE7NonPairAction w U))
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    PreE7SmallAxisCertificate (preE7NonPairAction w U) N PUnit
      (Real.logb 2 3 / 3) := by
  haveI : N.1.Normal := N.2
  letI : IsCyclic (preE7NonPairAction w U) := hcyclic
  letI : IsCyclic (preE7NonPairAction w U ⧸ N.1) :=
    isCyclic_of_surjective (QuotientGroup.mk' N.1)
      (QuotientGroup.mk'_surjective N.1)
  refine .tail 1 zero_le_one ?_
  intro b J
  calc
    (Nat.card (GroupEpimorphism J
        (preE7NonPairAction w U ⧸ N.1)) : ℝ) ≤
        Nat.card (Abelianization J) := by
      exact_mod_cast cyclicGroupEpimorphism_card_le_abelianization
        (J := J) (Q := preE7NonPairAction w U ⧸ N.1) inferInstance
    _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := hKP b J
    _ = 1 * (2 : ℝ) ^ ((Real.logb 2 3 / 3) * b) := by
      rw [one_mul, three_rpow_third_eq]

private theorem cyclicAxis_mainCoefficient
    (hcyclic : IsCyclic (preE7NonPairAction w U))
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (cyclicAxis hcyclic hKP N).mainCoefficient = 0 := by
  simp [cyclicAxis, PreE7SmallAxisCertificate.mainCoefficient]

private theorem cyclicAxis_tailCoefficient
    (hcyclic : IsCyclic (preE7NonPairAction w U))
    (hKP : KovacsPraegerAbelianizationBound)
    (N : {N : Subgroup (preE7NonPairAction w U) // N.Normal}) :
    (cyclicAxis hcyclic hKP N).tailCoefficient = 1 := by
  simp [cyclicAxis, PreE7SmallAxisCertificate.tailCoefficient]

private def cyclicData
    (hw7 : 7 ≤ w)
    (hcyclic : IsCyclic (preE7NonPairAction w U))
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveData w U where
  R := PUnit
  degree := 0
  action := 1
  action_injective := fun _ _ _ => Subsingleton.elim _ _
  tailSlope := Real.logb 2 3 / 3
  comparator_window := trivialSmallComparatorWindow (by omega)
  tail_window := logThreeThird_le_window (by omega)
  axis := cyclicAxis hcyclic hKP

private noncomputable def cyclicNumericalData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (hw7 : 7 ≤ w) (hw1024 : w < 1024)
    (hcyclic : IsCyclic (preE7NonPairAction w U))
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7SmallAdditiveNumericalData .saprim w U where
  data := cyclicData hw7 hcyclic hKP
  main_total_bound := by
    intro b
    have hz : fusionAxisEnvelopeTotal (preE7NonPairAction w U)
        (fun N => ((cyclicData hw7 hcyclic hKP).certificate .saprim).C b N) = 0 := by
      unfold fusionAxisEnvelopeTotal
      apply Finset.sum_eq_zero
      intro N _
      exact cyclicAxis_mainCoefficient hcyclic hKP N
    rw [hz]
    exact Real.rpow_nonneg (by norm_num) _
  tail_total_bound := by
    intro b
    have heq : fusionAxisEnvelopeTotal (preE7NonPairAction w U)
        (fun N => ((cyclicData hw7 hcyclic hKP).certificate
          .saprim).tailCoefficient b N) =
        (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) := by
      calc
        fusionAxisEnvelopeTotal (preE7NonPairAction w U)
            (fun N => ((cyclicData hw7 hcyclic hKP).certificate
              .saprim).tailCoefficient b N) =
            fusionAxisEnvelopeTotal (preE7NonPairAction w U) (fun _ => 1) := by
          unfold fusionAxisEnvelopeTotal
          apply Finset.sum_congr rfl
          intro N _
          change (cyclicAxis hcyclic hKP N).tailCoefficient = 1
          exact cyclicAxis_tailCoefficient hcyclic hKP N
        _ = _ := by
          unfold fusionAxisEnvelopeTotal
          simp
          exact @Fintype.card_congr
            {N : Subgroup (preE7NonPairAction w U) // N.Normal}
            {N : Subgroup (preE7NonPairAction w U) // N.Normal}
            (Subtype.fintype Subgroup.Normal) originalNormalFintype (Equiv.refl _)
    rw [heq]
    apply (show (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) ≤
        (Nat.card {N : Subgroup (preE7NonPairAction w U) // N.Normal} : ℝ) +
          Nat.card (preE7NonPairAction w U ≃* preE7NonPairAction w U) by
      exact le_add_of_nonneg_right (Nat.cast_nonneg _)).trans
    apply primitiveAffine_small_menu_bound (by omega) hw1024
    exact P.card_le_two_pow_logSquare x

private noncomputable def cyclicOwner
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (x : Fin w) (hw7 : 7 ≤ w) (hw1024 : w < 1024)
    (hcyclic : IsCyclic (preE7NonPairAction w U))
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7RankTailOwnerSourceData w U :=
  .ordinary .saprim (.small
    (cyclicNumericalData P x hw7 hw1024 hcyclic hKP))

end PrimitiveAffinePrimeDegreeSource

/-- Every retained prime-degree primitive affine action between degrees seven
and `1023` supplies the concrete cyclic-complement SAPRIM source. -/
noncomputable def primitiveAffinePrimeDegree_rankTailOwnerSourceData
    {w : ℕ} (U : PreE7NonPairActionClass w)
    (hwprime : w.Prime) (hw7 : 7 ≤ w) (hw1024 : w < 1024)
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hKP : KovacsPraegerAbelianizationBound) :
    PreE7RankTailOwnerSourceData w U := by
  let x : Fin w := ⟨0, by omega⟩
  let hcyclic : IsCyclic (P.complement x) :=
    P.complement_isCyclic_of_degree_prime x hwprime
  by_cases hnontrivial : Nontrivial (P.complement x)
  · letI : Nontrivial (P.complement x) := hnontrivial
    letI : IsCyclic (P.complement x) := hcyclic
    letI : CommGroup (P.complement x) := IsCyclic.commGroup
    letI : IsSolvable (P.complement x) :=
      isSolvable_of_comm (fun a b => mul_comm a b)
    let D : SolubleDerivedLength (P.complement x) :=
      Classical.choice (SolubleDerivedLength.nonempty _ inferInstance)
    exact PrimitiveAffineCyclicSource.toRankTailOwnerSource
      P (by omega) hw1024 hprimitive x D hcyclic hKP
  · have hsub : Subsingleton (P.complement x) :=
      not_nontrivial_iff_subsingleton.mp hnontrivial
    letI : Subsingleton (P.complement x) := hsub
    letI : IsCyclic P.V := P.translation_isCyclic_of_degree_prime x hwprime
    have hcomp : Nat.card (P.complement x) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have hfactor := (P.isComplement'_complement x).card_mul
    have hcard : Nat.card P.V = Nat.card (preE7NonPairAction w U) := by
      rw [hcomp, mul_one] at hfactor
      exact hfactor
    have hsurj : Function.Surjective P.V.subtype :=
      (Nat.bijective_iff_injective_and_card P.V.subtype).2
        ⟨Subtype.val_injective, hcard⟩ |>.2
    have hcyclicU : IsCyclic (preE7NonPairAction w U) :=
      isCyclic_of_surjective P.V.subtype hsurj
    exact PrimitiveAffinePrimeDegreeSource.cyclicOwner
      P x hw7 hw1024 hcyclicU hKP

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
