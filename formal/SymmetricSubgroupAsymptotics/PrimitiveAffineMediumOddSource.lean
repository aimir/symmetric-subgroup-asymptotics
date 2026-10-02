import SymmetricSubgroupAsymptotics.PrimitiveAffineDimensionOrderTailSource

/-!
# Catalogue-free medium odd affine owners

The dimension-sensitive order theorem closes the five composite odd
prime-power degrees below `343` at which the full affine group is already
small enough for the ordinary generator tail: `121`, `125`, `169`, `243`
and `289`.  Prime-power uniqueness recovers the translation dimension from
the action degree, so no affine-group census is used.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Uniqueness of a positive prime-power presentation, in the exact form
needed to read the affine translation dimension from the action degree. -/
theorem prime_pow_positive_injective
    {p q d e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : 0 < d) (he : 0 < e) (h : p ^ d = q ^ e) :
    p = q ∧ d = e := by
  have hpdiv : p ∣ q := hp.dvd_of_dvd_pow (by
    rw [← h]
    exact dvd_pow_self p hd.ne')
  have hqdiv : q ∣ p := hq.dvd_of_dvd_pow (by
    rw [h]
    exact dvd_pow_self q he.ne')
  have hpq : p = q := Nat.dvd_antisymm hpdiv hqdiv
  subst q
  exact ⟨rfl, Nat.pow_right_injective hp.two_le h⟩

namespace PrimitiveAffineProfile

variable {L : Type} [Group L] {w : ℕ} [MulAction L (Fin w)] [Finite L]
  (P : PrimitiveAffineProfile L (Fin w))

/-- A displayed prime-power degree fixes the dimension of the chosen
elementary translation chart. -/
theorem ElementaryChart.dimension_eq_of_degree_eq_prime_pow
    [FaithfulSMul L (Fin w)] [Nontrivial (Fin w)]
    {hprimitive : MulAction.IsPreprimitive L (Fin w)}
    (C : P.ElementaryChart hprimitive) (x : Fin w)
    {q e : ℕ} (hq : q.Prime) (he : 0 < e) (hw : w = q ^ e) :
    C.d = e := by
  letI : Finite C.V := Finite.of_injective
    (fun v : C.V => C.equiv.symm (Multiplicative.ofAdd v))
    C.equiv.symm.injective
  have hdegree : w = P.p ^ C.d := by
    simpa [PrimitiveAffineProfile.ElementaryChart.d] using
      P.degree_eq_prime_pow_finrank C.equiv x
  exact (prime_pow_positive_injective P.p_prime hq C.d_pos he
    (hdegree.symm.trans hw)).2

end PrimitiveAffineProfile

namespace Non2UnipotentPrefixFiniteMenu
namespace PrimitiveAffineMediumOddSource

open PrimitiveAffineDimensionOrderTailSource

variable {w : ℕ} {U : PreE7NonPairActionClass w}

private noncomputable def source121 {U : PreE7NonPairActionClass 121}
    (P : PrimitiveAffineProfile (preE7NonPairAction 121 U) (Fin 121))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 121 U) (Fin 121))
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData 121 U := by
  let x : Fin 121 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  have hd : C.d = 2 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 11) (by norm_num) (by norm_num)
  let D : CeilingData P := ceilingDataOfDimension P hprimitive x 21
    (by norm_num) (by
      change 121 ^ (C.d + 1) ≤ 2 ^ 21
      norm_num [hd])
    (by norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree])
    (by norm_num)
  exact toRankTailOwnerSource P D hprimitive x hgen

private noncomputable def source125 {U : PreE7NonPairActionClass 125}
    (P : PrimitiveAffineProfile (preE7NonPairAction 125 U) (Fin 125))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 125 U) (Fin 125))
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData 125 U := by
  let x : Fin 125 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  have hd : C.d = 3 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 5) (by norm_num) (by norm_num)
  let D : CeilingData P := ceilingDataOfDimension P hprimitive x 28
    (by norm_num) (by
      change 125 ^ (C.d + 1) ≤ 2 ^ 28
      norm_num [hd])
    (by norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree])
    (by norm_num)
  exact toRankTailOwnerSource P D hprimitive x hgen

private noncomputable def source169 {U : PreE7NonPairActionClass 169}
    (P : PrimitiveAffineProfile (preE7NonPairAction 169 U) (Fin 169))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 169 U) (Fin 169))
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData 169 U := by
  let x : Fin 169 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  have hd : C.d = 2 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 13) (by norm_num) (by norm_num)
  let D : CeilingData P := ceilingDataOfDimension P hprimitive x 23
    (by norm_num) (by
      change 169 ^ (C.d + 1) ≤ 2 ^ 23
      norm_num [hd])
    (by norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree])
    (by norm_num)
  exact toRankTailOwnerSource P D hprimitive x hgen

private noncomputable def source243 {U : PreE7NonPairActionClass 243}
    (P : PrimitiveAffineProfile (preE7NonPairAction 243 U) (Fin 243))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 243 U) (Fin 243))
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData 243 U := by
  let x : Fin 243 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  have hd : C.d = 5 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 3) (by norm_num) (by norm_num)
  let D : CeilingData P := ceilingDataOfDimension P hprimitive x 48
    (by norm_num) (by
      change 243 ^ (C.d + 1) ≤ 2 ^ 48
      norm_num [hd])
    (by norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree])
    (by norm_num)
  exact toRankTailOwnerSource P D hprimitive x hgen

private noncomputable def source289 {U : PreE7NonPairActionClass 289}
    (P : PrimitiveAffineProfile (preE7NonPairAction 289 U) (Fin 289))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction 289 U) (Fin 289))
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData 289 U := by
  let x : Fin 289 := ⟨0, by norm_num⟩
  let C := P.elementaryChart hprimitive
  have hd : C.d = 2 := C.dimension_eq_of_degree_eq_prime_pow P x
    (by norm_num : Nat.Prime 17) (by norm_num) (by norm_num)
  let D : CeilingData P := ceilingDataOfDimension P hprimitive x 25
    (by norm_num) (by
      change 289 ^ (C.d + 1) ≤ 2 ^ 25
      norm_num [hd])
    (by norm_num [preE7CharacterWindow, preE7CharacterRho, halfDegree])
    (by norm_num)
  exact toRankTailOwnerSource P D hprimitive x hgen

/-- Every primitive affine profile in one of the five medium composite odd
degrees supplies a concrete SAPRIM owner, without a finite catalogue. -/
noncomputable def primitiveAffineMediumOdd_rankTailOwnerSourceData
    (P : PrimitiveAffineProfile (preE7NonPairAction w U) (Fin w))
    (hprimitive : MulAction.IsPreprimitive
      (preE7NonPairAction w U) (Fin w))
    (hdegree : w = 121 ∨ w = 125 ∨ w = 169 ∨ w = 243 ∨ w = 289)
    (hgen : PermutationSubgroupGeneratorBound) :
    PreE7RankTailOwnerSourceData w U := by
  by_cases h : w = 121
  · subst w
    exact source121 P hprimitive hgen
  by_cases h' : w = 125
  · subst w
    exact source125 P hprimitive hgen
  by_cases h'' : w = 169
  · subst w
    exact source169 P hprimitive hgen
  by_cases h''' : w = 243
  · subst w
    exact source243 P hprimitive hgen
  · have h289 : w = 289 := by
      rcases hdegree with h121 | h125 | h169 | h243 | h289
      · exact False.elim (h h121)
      · exact False.elim (h' h125)
      · exact False.elim (h'' h169)
      · exact False.elim (h''' h243)
      · exact h289
    subst w
    exact source289 P hprimitive hgen

end PrimitiveAffineMediumOddSource
end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics

end
