import SymmetricSubgroupAsymptotics.MarkedC4HallSpliceCount

/-!
# Literal Case-I Hall encoding

The Case-I row in the bounded-word argument is a finite injection into an
abelian Hall fibre.  This file proves the marked estimate for that fibre from
the actual groups.  In particular the two occurrences of the auxiliary rank
`r` are consequences of adjoining the literal group `C₄^r`; they are not an
`r`-dependent counting hypothesis.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics
namespace MarkedC4

universe u

/-- Exponent two implies exponent four. -/
theorem hasExp2_two_of_hasExp2_one
    {A : Type u} [Group A] (hA : HasExp2 A 1) : HasExp2 A 2 := by
  intro x
  calc
    x ^ (2 ^ 2) = (x ^ (2 ^ 1)) ^ 2 := by
      simpa using (pow_mul x 2 2)
    _ = 1 := by rw [hA x, one_pow]

/-- An elementary abelian `2`-group has no second binary column. -/
theorem col_one_eq_zero_of_hasExp2_one
    (A : Type u) [CommGroup A] [Finite A] (hA : HasExp2 A 1) :
    col A 1 = 0 := by
  rw [show 1 = 0 + 1 by omega, col_succ]
  letI : Subsingleton (sqs A) :=
    subsingleton_of_hasExp2_zero (hasExp2_sqs hA)
  exact col_eq_zero_of_subsingleton (sqs A) 0

/-- The complete Hall fibre used in Case I, with the two marked columns
derived from the literal product with `C₄^r`.

`a/2` is only an upper bound for the first physical target column; the two
source columns are the actual first columns of the source abelianization.
-/
theorem elementaryCyclicFourFullSecond_le
    (r : ℕ)
    (A : Type u) [CommGroup A] [Finite A]
    [Fintype (Subgroup (A × Multiplicative (Fin r → ZMod 4)))]
    (hA : HasExp2 A 1)
    (E : Type u) [Group E] [Finite E]
    (a sourceFirst sourceSecond : ℝ)
    (ha : (col A 0 : ℝ) ≤ a / 2)
    (hfirst : (col (Abelianization E) 0 : ℝ) = sourceFirst)
    (hsecond : (col (Abelianization E) 1 : ℝ) = sourceSecond) :
    (Nat.card (AbelianProductGraphClassification.FullSecond
      (A × Multiplicative (Fin r → ZMod 4)) E) : ℝ)
      ≤ 16 * (a / 2 + r + 1) * (r + 1) *
        (2 : ℝ) ^ (psi (a / 2 + r) sourceFirst + psi r sourceSecond) := by
  have hraw := cyclicFourFullSecond_le 2 r A
    (hasExp2_two_of_hasExp2_one hA) (by norm_num) E
  have hcol1 : col A 1 = 0 := col_one_eq_zero_of_hasExp2_one A hA
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have htarget0 :
      (col (A × Multiplicative (Fin r → ZMod 4)) 0 : ℝ) ≤ a / 2 + r := by
    rw [col_prod_cyclicFourCoordinates]
    norm_num
    exact_mod_cast ha
  have htarget1 :
      (col (A × Multiplicative (Fin r → ZMod 4)) 1 : ℝ) = r := by
    rw [col_prod_cyclicFourCoordinates, hcol1]
    norm_num
  have hfirst0 : 0 ≤ sourceFirst := by
    rw [← hfirst]
    positivity
  have hsecond0 : 0 ≤ sourceSecond := by
    rw [← hsecond]
    positivity
  have hpsi0 :
      psi (col (A × Multiplicative (Fin r → ZMod 4)) 0)
          (col (Abelianization E) 0) ≤
        psi (a / 2 + r) sourceFirst := by
    rw [hfirst]
    exact psi_mono_left (by positivity) htarget0 hfirst0
  have hpsi1 :
      psi (col (A × Multiplicative (Fin r → ZMod 4)) 1)
          (col (Abelianization E) 1) =
        psi r sourceSecond := by
    rw [hsecond, htarget1]
  have hfactor0 :
      ((col (A × Multiplicative (Fin r → ZMod 4)) 0 : ℝ) + 1) ≤
        a / 2 + r + 1 := by linarith
  have hfactor1 :
      ((col (A × Multiplicative (Fin r → ZMod 4)) 1 : ℝ) + 1) = r + 1 := by
    rw [htarget1]
  have htargetNonneg : 0 ≤ a / 2 + r + 1 := by
    have hcol0 : (0 : ℝ) ≤ col A 0 := by positivity
    linarith
  have hprod :
      (∏ k ∈ Finset.range 2,
          (((col (A × Multiplicative (Fin r → ZMod 4)) k : ℕ) : ℝ) + 1)) ≤
        (a / 2 + r + 1) * (r + 1) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [hfactor1]
    exact mul_le_mul_of_nonneg_right hfactor0 (by positivity)
  have hexp :
      (∑ k ∈ Finset.range 2,
          psi (col (A × Multiplicative (Fin r → ZMod 4)) k)
            (col (Abelianization E) k)) ≤
        psi (a / 2 + r) sourceFirst + psi r sourceSecond := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [hpsi1]
    linarith
  have hpow :
      (2 : ℝ) ^ (∑ k ∈ Finset.range 2,
          psi (col (A × Multiplicative (Fin r → ZMod 4)) k)
            (col (Abelianization E) k)) ≤
        (2 : ℝ) ^ (psi (a / 2 + r) sourceFirst + psi r sourceSecond) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
  calc
    (Nat.card (AbelianProductGraphClassification.FullSecond
        (A × Multiplicative (Fin r → ZMod 4)) E) : ℝ)
        ≤ (∏ k ∈ Finset.range 2,
              (((col (A × Multiplicative (Fin r → ZMod 4)) k : ℕ) : ℝ) + 1)) *
            4 ^ 2 *
            (2 : ℝ) ^ (∑ k ∈ Finset.range 2,
              psi (col (A × Multiplicative (Fin r → ZMod 4)) k)
                (col (Abelianization E) k)) := hraw
    _ = (∏ k ∈ Finset.range 2,
              (((col (A × Multiplicative (Fin r → ZMod 4)) k : ℕ) : ℝ) + 1)) *
            16 *
            (2 : ℝ) ^ (∑ k ∈ Finset.range 2,
              psi (col (A × Multiplicative (Fin r → ZMod 4)) k)
                (col (Abelianization E) k)) := by norm_num
    _ ≤ ((a / 2 + r + 1) * (r + 1)) * 16 *
          (2 : ℝ) ^ (psi (a / 2 + r) sourceFirst + psi r sourceSecond) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_right hprod (by norm_num)) hpow
        (Real.rpow_nonneg (by norm_num) _)
        (mul_nonneg (mul_nonneg htargetNonneg (by positivity)) (by norm_num))
    _ = 16 * (a / 2 + r + 1) * (r + 1) *
          (2 : ℝ) ^ (psi (a / 2 + r) sourceFirst + psi r sourceSecond) := by
      ring

/-! ## Finite structural encodings -/

/-- One actual elementary Hall target occurring in a Case-I tableau. -/
structure ElementaryHallTarget (a : ℝ) where
  Carrier : Type u
  [commGroup : CommGroup Carrier]
  [finite : Finite Carrier]
  exponent_two : HasExp2 Carrier 1
  first_column : (col Carrier 0 : ℝ) ≤ a / 2

attribute [instance] ElementaryHallTarget.commGroup ElementaryHallTarget.finite

/-- One actual source group occurring in a Case-I Hall fibre. -/
structure TwoColumnHallSource (sourceFirst sourceSecond : ℝ) where
  Carrier : Type u
  [group : Group Carrier]
  [finite : Finite Carrier]
  first_column : (col (Abelianization Carrier) 0 : ℝ) = sourceFirst
  second_column : (col (Abelianization Carrier) 1 : ℝ) = sourceSecond

attribute [instance] TwoColumnHallSource.group TwoColumnHallSource.finite

/-- A literal, `r`-independent Case-I encoding.  The finite code type and its
physical/source groups do not depend on the auxiliary mark count.  For each
`r`, every counted object injects into a code together with an exact
second-full subgroup of `A × C₄^r` over the retained source.
-/
structure PublishedCaseIHallEncoding
    (caseI : ℕ → ℝ) (a sourceFirst sourceSecond entropy A₀ : ℝ) (b : ℕ) where
  Code : Type u
  codeFintype : Fintype Code
  target : Code → ElementaryHallTarget a
  source : Code → TwoColumnHallSource sourceFirst sourceSecond
  Object : ℕ → Type u
  objectFintype : ∀ r, Fintype (Object r)
  encode : ∀ r, Object r →
    Σ q : Code, AbelianProductGraphClassification.FullSecond
      ((target q).Carrier × Multiplicative (Fin r → ZMod 4))
      (source q).Carrier
  encode_injective : ∀ r, Function.Injective (encode r)
  count_identity : ∀ r, caseI r = (Nat.card (Object r) : ℝ)
  code_bound : (Fintype.card Code : ℝ) ≤
    (2 : ℝ) ^ entropy * (((b : ℝ) + 2) ^ A₀)

namespace PublishedCaseIHallEncoding

variable {caseI : ℕ → ℝ} {a sourceFirst sourceSecond entropy A₀ : ℝ} {b : ℕ}

/-- The literal injection and the exact Hall theorem imply the full marked
Case-I enumeration.  The six extra polynomial powers pay the two Hall-profile
factors and the fixed `4²` constant.
-/
theorem bound
    (D : PublishedCaseIHallEncoding caseI a sourceFirst sourceSecond entropy A₀ b)
    (ha : 0 ≤ a) (hab : a ≤ b) (hA₀ : 0 ≤ A₀) (r : ℕ) :
    caseI r ≤
      (2 : ℝ) ^ (entropy +
        psi (a / 2 + r) sourceFirst + psi r sourceSecond) *
        (((b : ℝ) + r + 2) ^ (A₀ + 6)) := by
  letI : Fintype D.Code := D.codeFintype
  letI : Fintype (D.Object r) := D.objectFintype r
  let Hall (q : D.Code) :=
    AbelianProductGraphClassification.FullSecond
      ((D.target q).Carrier × Multiplicative (Fin r → ZMod 4))
      (D.source q).Carrier
  letI (q : D.Code) : Finite (Hall q) := by
    dsimp only [Hall]
    infer_instance
  letI (q : D.Code) : Fintype (Hall q) := Fintype.ofFinite _
  letI : Finite (Σ q : D.Code, Hall q) := inferInstance
  have hinj : Nat.card (D.Object r) ≤ Nat.card (Σ q : D.Code, Hall q) :=
    Nat.card_le_card_of_injective (D.encode r) (D.encode_injective r)
  have hsigma : (Nat.card (Σ q : D.Code, Hall q) : ℝ) =
      ∑ q : D.Code, (Nat.card (Hall q) : ℝ) := by
    rw [Nat.card_sigma]
    push_cast
    rfl
  let H : ℝ :=
    (2 : ℝ) ^ (psi (a / 2 + r) sourceFirst + psi r sourceSecond)
  have hHall (q : D.Code) :
      (Nat.card (Hall q) : ℝ) ≤
        16 * (a / 2 + r + 1) * (r + 1) * H := by
    letI : Fintype (Subgroup
        ((D.target q).Carrier × Multiplicative (Fin r → ZMod 4))) :=
      Fintype.ofFinite _
    exact elementaryCyclicFourFullSecond_le r (D.target q).Carrier
      (D.target q).exponent_two (D.source q).Carrier
      a sourceFirst sourceSecond (D.target q).first_column
      (D.source q).first_column (D.source q).second_column
  have hobjects : (Nat.card (D.Object r) : ℝ) ≤
      (Fintype.card D.Code : ℝ) *
        (16 * (a / 2 + r + 1) * (r + 1) * H) := by
    calc
      (Nat.card (D.Object r) : ℝ) ≤
          (Nat.card (Σ q : D.Code, Hall q) : ℕ) := by exact_mod_cast hinj
      _ = ∑ q : D.Code, (Nat.card (Hall q) : ℝ) := hsigma
      _ ≤ ∑ _q : D.Code,
          (16 * (a / 2 + r + 1) * (r + 1) * H) :=
        Finset.sum_le_sum (fun q _ ↦ hHall q)
      _ = (Fintype.card D.Code : ℝ) *
          (16 * (a / 2 + r + 1) * (r + 1) * H) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  let x : ℝ := (b : ℝ) + r + 2
  have hx2 : 2 ≤ x := by
    dsimp only [x]
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx2
  have htarget : a / 2 + r + 1 ≤ x := by
    dsimp only [x]
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    nlinarith
  have hrx : (r : ℝ) + 1 ≤ x := by
    dsimp only [x]
    have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
    linarith
  have hprofile :
      16 * (a / 2 + r + 1) * (r + 1) ≤ x ^ (6 : ℕ) := by
    have h4 : (16 : ℝ) ≤ x ^ (4 : ℕ) := by
      calc
        (16 : ℝ) = 2 ^ (4 : ℕ) := by norm_num
        _ ≤ x ^ (4 : ℕ) := pow_le_pow_left₀ (by norm_num) hx2 4
    have htwo :
        (a / 2 + r + 1) * (r + 1) ≤ x ^ (2 : ℕ) := by
      calc
        (a / 2 + r + 1) * (r + 1) ≤ x * x :=
          mul_le_mul htarget hrx (by positivity) (by linarith)
        _ = x ^ (2 : ℕ) := by ring
    calc
      16 * (a / 2 + r + 1) * (r + 1) =
          16 * ((a / 2 + r + 1) * (r + 1)) := by ring
      _ ≤ x ^ (4 : ℕ) * x ^ (2 : ℕ) :=
        mul_le_mul h4 htwo (by positivity) (by positivity)
      _ = x ^ (6 : ℕ) := by rw [← pow_add]
  have hbase : (b : ℝ) + 2 ≤ x := by
    dsimp only [x]
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hpoly : (((b : ℝ) + 2) ^ A₀) ≤ x ^ A₀ := by
    exact Real.rpow_le_rpow (by positivity) hbase hA₀
  have hH : 0 ≤ H := Real.rpow_nonneg (by norm_num) _
  have htwoexp :
      (2 : ℝ) ^ entropy * H =
        (2 : ℝ) ^ (entropy +
          psi (a / 2 + r) sourceFirst + psi r sourceSecond) := by
    dsimp only [H]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hpolyeq : x ^ A₀ * x ^ (6 : ℕ) = x ^ (A₀ + 6) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hxpos]
    norm_num
  rw [D.count_identity]
  calc
    (Nat.card (D.Object r) : ℝ) ≤
        (Fintype.card D.Code : ℝ) *
          (16 * (a / 2 + r + 1) * (r + 1) * H) := hobjects
    _ ≤ ((2 : ℝ) ^ entropy * (((b : ℝ) + 2) ^ A₀)) *
          (16 * (a / 2 + r + 1) * (r + 1) * H) := by
      gcongr
      exact D.code_bound
    _ ≤ ((2 : ℝ) ^ entropy * (x ^ A₀)) *
          ((x ^ (6 : ℕ)) * H) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (by norm_num) _))
        (mul_le_mul_of_nonneg_right hprofile hH)
        (mul_nonneg (by positivity) (by positivity))
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (by positivity))
    _ = (2 : ℝ) ^ (entropy +
          psi (a / 2 + r) sourceFirst + psi r sourceSecond) *
          (((b : ℝ) + r + 2) ^ (A₀ + 6)) := by
      change ((2 : ℝ) ^ entropy * x ^ A₀) * (x ^ (6 : ℕ) * H) =
        (2 : ℝ) ^ (entropy +
          psi (a / 2 + r) sourceFirst + psi r sourceSecond) *
          x ^ (A₀ + 6)
      calc
        ((2 : ℝ) ^ entropy * x ^ A₀) * (x ^ (6 : ℕ) * H) =
            ((2 : ℝ) ^ entropy * H) * (x ^ A₀ * x ^ (6 : ℕ)) := by ring
        _ = _ := by rw [htwoexp, hpolyeq]

end PublishedCaseIHallEncoding

end MarkedC4
end SymmetricSubgroupAsymptotics

end
