import SymmetricSubgroupAsymptotics.SimpleModelMinimumIndexDegreeTransport
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryPointIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticBinaryRankTwoSharpIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticPrimeFieldRankTwoIndex
import SymmetricSubgroupAsymptotics.CFSGSymplecticOddHigherRankIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBOriginalMatrixBounds
import SymmetricSubgroupAsymptotics.CFSGOrthogonalBPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDPointRadicalIndex
import SymmetricSubgroupAsymptotics.CFSGSuzukiQuadraticTorusIndex

/-! Actual proper-index bounds exclude the paired B/C/D/Suzuki models
below degree twelve. The binary C/B case retains its literal projective
matrix quotient and original simplicity. This is a uniform action
argument, with no minimum-index catalogue or generator assumption. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGPairedNonTypeAMinimumTwelve
open PrimitiveSocleRawStructure CFSGReduction

private theorem map_ne_top {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (H : Subgroup A) (hH : H ≠ ⊤) : H.map e.toMonoidHom ≠ ⊤ := by
  intro ht
  apply hH
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  exact ht.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm

private theorem two_ne_zero (q : CFSG.PrimePower) (hp : q.prime ≠ 2) :
    (2 : q.Field) ≠ 0 := by
  intro h
  have hd := (CharP.cast_eq_zero_iff q.Field q.prime 2).mp h
  exact hp ((Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_two).mp hd)

private theorem prime_le_order (q : CFSG.PrimePower) : q.prime ≤ q.order := by
  simpa only [pow_one] using
    (Nat.pow_le_pow_right q.prime_isPrime.pos (show 1 ≤ q.exponent from q.exponent_pos))

private theorem binary_projective (q : CFSG.PrimePower) (hq : q.prime = 2)
    (r : ℕ) (hr : 3 ≤ r)
    [IsSimpleGroup (CFSGSymplecticSerreMatrices.elementaryProjective q.Field r)]
    (H : Subgroup (CFSGSymplecticSerreMatrices.elementaryProjective q.Field r))
    (hH : H ≠ ⊤) : 12 ≤ H.index := by
  letI : CharP q.Field 2 := by rw [← hq]; infer_instance
  by_cases hb : q.order = 2
  · have hc : Nat.card q.Field = 2 := q.card_field.trans hb
    have hpow : 4 ≤ 2^(r-1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ r-1)
    have hprod : 12 ≤ 2^(r-1)*(2^(r-1)-1) := by
      calc
        12 = 4*(4-1) := by decide
        _ ≤ _ := Nat.mul_le_mul hpow (by omega)
    exact hprod.trans
      (CFSGSymplecticBinaryPointIndex.binary_point_radical_proper_index q.Field hc r hr H hH)
  · have he : 2 ≤ q.exponent := by
      have hpos := q.exponent_pos
      by_contra hh
      have h1 : q.exponent = 1 := by omega
      exact hb (by simp only [CFSG.PrimePower.order,hq,h1,pow_one])
    have hq4 : 4 ≤ q.order := by
      change 4 ≤ q.prime^q.exponent
      rw [hq]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) he
    have hp : 16 ≤ q.order^(r-1) := (Nat.pow_le_pow_left hq4 2).trans
      (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 2 ≤ r-1))
    have hi := CFSGSymplecticIndexStarLower.projective_field_power_le_proper_index q.Field r
      (by omega) H hH
    rw [q.card_field] at hi
    omega

theorem typeC (r : ℕ) (hr : 2 ≤ r) (q : CFSG.PrimePower)
    (hs : r = 2 → q.order ≠ 2) [IsSimpleGroup (CFSG.Models.C r q)]
    (H : Subgroup (CFSG.Models.C r q)) (hH : H ≠ ⊤) : 12 ≤ H.index := by
  have hq2 : 2 ≤ q.order := q.prime_isPrime.two_le.trans (prime_le_order q)
  by_cases htwo : r = 2
  · subst r
    have hq3 : 3 ≤ q.order := by have hh := hs rfl; omega
    by_cases hchar : q.prime = 2
    · have hq4 : 4 ≤ q.order := by
        by_contra hh
        have h3 : q.order = 3 := by omega
        have hd : 2 ∣ 3 := by
          have hp : q.prime ∣ q.order := dvd_pow_self _ q.exponent_pos.ne'
          simpa only [hchar,h3] using hp
        norm_num at hd
      have hpow : 16 ≤ q.order^2 := Nat.pow_le_pow_left hq4 2
      have hi := typeC_rankTwo_binary_field_square_le_proper_index_of_four_le q hchar hq4 H hH
      omega
    · by_cases hq4 : 4 ≤ q.order
      · have hpow : 16 ≤ q.order^2 := Nat.pow_le_pow_left hq4 2
        have hi := typeC_rankTwo_field_square_le_proper_index q (two_ne_zero q hchar) H hH
        omega
      · have h3 : q.order = 3 := by omega
        have hd : q.prime ∣ 3 := by
          have hdiv : q.prime ∣ q.order := dvd_pow_self _ q.exponent_pos.ne'
          rwa [h3] at hdiv
        have hp : q.prime = 3 :=
          (Nat.prime_dvd_prime_iff_eq q.prime_isPrime Nat.prime_three).mp hd
        have hi := typeC_rankTwo_prime_cube_le_proper_index q (h3.trans hp.symm)
          (two_ne_zero q hchar) H hH
        norm_num only [h3] at hi
        omega
  · have hr3 : 3 ≤ r := by omega
    by_cases hchar : q.prime = 2
    · obtain ⟨s,rfl⟩ : ∃ s : ℕ, r = s+1 := ⟨r-1,by omega⟩
      let e := CFSGSymplecticSerreMatrices.serreProjectiveEquivElementaryProjective q.Field s
      letI : IsSimpleGroup
          (CFSGSymplecticSerreMatrices.elementaryProjective q.Field (s+1)) :=
        e.symm.isSimpleGroup
      have hi := binary_projective q hchar (s+1) hr3 (H.map e.toMonoidHom) (map_ne_top e H hH)
      exact hi.trans_eq (H.index_map_equiv e)
    · have hp : 3 ≤ q.prime := by have hh := q.prime_isPrime.two_le; omega
      have hq3 : 3 ≤ q.order := hp.trans (prime_le_order q)
      have hpow : 81 ≤ q.order^(2*r-2) := (Nat.pow_le_pow_left hq3 4).trans
        (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 4 ≤ 2*r-2))
      have hprod : 243 ≤ q.prime*q.order^(2*r-2) := Nat.mul_le_mul hp hpow
      exact (by decide : 12 ≤ 243).trans (hprod.trans
        (typeC_odd_prime_mul_field_power_le_proper_index r hr3 q (two_ne_zero q hchar) H hH))

theorem typeB (r : ℕ) (hr : 3 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.B r q)]
    (H : Subgroup (CFSG.Models.B r q)) (hH : H ≠ ⊤) : 12 ≤ H.index := by
  by_cases hchar : q.prime = 2
  · letI : CharP q.Field 2 := by rw [← hchar]; infer_instance
    obtain ⟨s,rfl⟩ : ∃ s : ℕ, r = s+3 := ⟨r-3,by omega⟩
    let e := CFSGOrthogonalBSerreMatrices.serreProjectiveEquivSymplecticProjective_charTwo
      q.Field (s+2) (by omega)
    letI : IsSimpleGroup
        (CFSGSymplecticSerreMatrices.elementaryProjective q.Field (s+3)) := e.symm.isSimpleGroup
    have hi := binary_projective q hchar (s+3) hr (H.map e.toMonoidHom) (map_ne_top e H hH)
    exact hi.trans_eq (H.index_map_equiv e)
  · have hp : 3 ≤ q.prime := by have hh := q.prime_isPrime.two_le; omega
    have hq3 : 3 ≤ q.order := hp.trans (prime_le_order q)
    have hpow : 9 ≤ q.order^(r-1) := (Nat.pow_le_pow_left hq3 2).trans
      (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 2 ≤ r-1))
    have hprod : 72 ≤ (q.order^(r-1)-1)*q.order^(r-1) := by
      calc
        72 = (9-1)*9 := by decide
        _ ≤ _ := Nat.mul_le_mul (by omega) hpow
    exact (by decide : 12 ≤ 72).trans
      (hprod.trans (typeB_point_radical_le_proper_index r hr q hchar H hH))

theorem typeD (r : ℕ) (hr : 4 ≤ r) (q : CFSG.PrimePower)
    [IsSimpleGroup (CFSG.Models.D r q)]
    (H : Subgroup (CFSG.Models.D r q)) (hH : H ≠ ⊤) : 12 ≤ H.index := by
  have hq : 2 ≤ q.order := q.prime_isPrime.two_le.trans (prime_le_order q)
  have ha : 8 ≤ q.order^(r-1) := (Nat.pow_le_pow_left hq 3).trans
    (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 3 ≤ r-1))
  have hb : 4 ≤ q.order^(r-2) := (Nat.pow_le_pow_left hq 2).trans
    (Nat.pow_le_pow_right (by omega : 0 < q.order) (by omega : 2 ≤ r-2))
  have hp : 28 ≤ (q.order^(r-1)-1)*q.order^(r-2) := by
    calc
      28 = (8-1)*4 := by decide
      _ ≤ _ := Nat.mul_le_mul (by omega) hb
  exact (by decide : 12 ≤ 28).trans (hp.trans (typeD_point_radical_le_proper_index r hr q H hH))

theorem suzuki (m : ℕ) (hm : 1 ≤ m) [IsSimpleGroup (CFSG.Models.Suzuki m)]
    (H : Subgroup (CFSG.Models.Suzuki m)) (hH : H ≠ ⊤) : 12 ≤ H.index := by
  have ha : 8 ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ 2*m+1)
  have hb : 4 ≤ 2^(m+1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ m+1)
  have hp : 28 ≤ (2^(2*m+1)-1)*2^(m+1) := by
    calc
      28 = (8-1)*4 := by decide
      _ ≤ _ := Nat.mul_le_mul (by omega) hb
  exact (by decide : 12 ≤ 28).trans (hp.trans
    (CFSGSuzukiQuadraticTorusIndex.suzuki_quadratic_torus_le_proper_index m hm H hH))

end SymmetricSubgroupAsymptotics.CFSGPairedNonTypeAMinimumTwelve
