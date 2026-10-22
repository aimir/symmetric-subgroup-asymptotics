import SymmetricSubgroupAsymptotics.SemisimpleOuterFactorPublished
import SymmetricSubgroupAsymptotics.CFSGSimpleAutomorphismOrderBound

/-! The SAME semisimple outer factor from actual AutSquare, without a
 generating-tuple theorem. A displayed nontrivial factor forces w>=2,
 so log2(w+b+2)>=2 pays its square automorphism bound with coefficient3. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace SymmetricSubgroupAsymptotics
namespace SemisimpleNormalChart
variable {w : ℕ} {U : Subgroup (Equiv.Perm (Fin w))} {E : Subgroup U}
  (C : SemisimpleNormalChart E)

theorem factorPermutation_degree_two_le (i : C.ι) : 2 ≤ w := by
  letI : IsSimpleGroup (C.factor i) := C.simple i
  have hc : Nat.card (C.factor i) ≤ Nat.factorial w := by
    calc
      _ ≤ Nat.card (Equiv.Perm (Fin w)) :=
        Nat.card_le_card_of_injective (C.factorPermutationHom i) (C.factorPermutationHom_injective i)
      _ = Nat.factorial w := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  by_contra hn
  have hw : w ≤ 1 := by omega
  have hfac : Nat.factorial w ≤ 1 := by simpa only [Nat.factorial_one] using Nat.factorial_le hw
  have hpos := Finite.one_lt_card (α := C.factor i)
  omega

end SemisimpleNormalChart
namespace Non2UnipotentPrefixFiniteMenu
private theorem logb_two_prod_nat
    {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 0 < f i) :
    Real.logb 2 ((∏ i ∈ s, f i : ℕ) : ℝ) =
      ∑ i ∈ s, Real.logb 2 (f i : ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : (f a : ℝ) ≠ 0 := by exact_mod_cast (hf a (Finset.mem_insert_self _ _)).ne'
      have hfs : (((∏ i ∈ s, f i : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast
          (Finset.prod_pos fun i hi => hf i (Finset.mem_insert_of_mem hi)).ne'
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Nat.cast_mul,
        Real.logb_mul hfa hfs]
      rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private theorem factorial_le_two_pow_sq (n : ℕ) :
    n.factorial ≤ 2 ^ (n * n) := by
  calc
    n.factorial ≤ n ^ n := n.factorial_le_pow
    _ ≤ (2 ^ n) ^ n :=
      Nat.pow_le_pow_left (Nat.le_of_lt n.lt_two_pow_self) n
    _ = 2 ^ (n * n) := by rw [pow_mul]

private theorem factorial_logb_le_sq (n : ℕ) :
    Real.logb 2 (Nat.factorial n : ℝ) ≤ (n : ℝ) ^ 2 := by
  have hcast : (Nat.factorial n : ℝ) ≤ (((2 ^ (n * n) : ℕ) : ℝ)) := by
    exact_mod_cast factorial_le_two_pow_sq n
  have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (by positivity : (0 : ℝ) < Nat.factorial n)
    hcast
  calc
    Real.logb 2 (Nat.factorial n : ℝ) ≤
        Real.logb 2 (((2 ^ (n * n) : ℕ) : ℝ)) := h
    _ = (n : ℝ) ^ 2 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow,
        Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2), mul_one,
        Nat.cast_mul]
      norm_num [pow_two]

private theorem factorial_logb_add_one_le_rpow
    (w b : ℕ) :
    Real.logb 2 (Nat.factorial b : ℝ) + 1 ≤
      (2 : ℝ) ^
        (2 * Real.logb 2 ((w + b + 2 : ℕ) : ℝ)) := by
  let X : ℝ := Real.logb 2 ((w + b + 2 : ℕ) : ℝ)
  have hL := factorial_logb_le_sq b
  have hb : (b : ℝ) + 1 ≤ (w + b + 2 : ℕ) := by
    exact_mod_cast (show b + 1 ≤ w + b + 2 by omega)
  have hsq : (b : ℝ) ^ 2 + 1 ≤ ((w + b + 2 : ℕ) : ℝ) ^ 2 := by
    nlinarith
  have hN : (0 : ℝ) < (w + b + 2 : ℕ) := by positivity
  have hrepr : (2 : ℝ) ^ X = ((w + b + 2 : ℕ) : ℝ) := by
    dsimp [X]
    exact Real.rpow_logb (by norm_num) (by norm_num) hN
  calc
    Real.logb 2 (Nat.factorial b : ℝ) + 1 ≤ (b : ℝ) ^ 2 + 1 :=
      by linarith
    _ ≤ ((w + b + 2 : ℕ) : ℝ) ^ 2 := hsq
    _ = ((2 : ℝ) ^ X) ^ (2 : ℕ) := by rw [hrepr]
    _ = ((2 : ℝ) ^ X) ^ (2 : ℝ) := (Real.rpow_two _).symm
    _ = (2 : ℝ) ^ (X * 2) := by rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    _ = (2 : ℝ) ^ (2 * X) := by ring_nf

/-- The same coefficient-three factor bound follows from AutSquare. -/
theorem semisimpleOuterFactorPermutationBound_of_autSquare
    (hAut : FiniteSimpleAutomorphismSquareBound) :
    SemisimpleOuterFactorPermutationBound := by
  intro w U E _ C b
  let L : ℝ := Real.logb 2 (Nat.factorial b : ℝ)
  let X : ℝ := Real.logb 2 ((w + b + 2 : ℕ) : ℝ)
  have hL : 0 ≤ L := Real.logb_nonneg (by norm_num)
    (by exact_mod_cast Nat.factorial_pos b)
  have hX : 1 ≤ X := by
    dsimp [X]
    calc
      (1 : ℝ) = Real.logb 2 2 := by
        rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      _ ≤ Real.logb 2 ((w + b + 2 : ℕ) : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num)
          (by norm_num) (by exact_mod_cast (show 2 ≤ w + b + 2 by omega))
  have hLone : L + 1 ≤ (2 : ℝ) ^ (2 * X) := by
    exact factorial_logb_add_one_le_rpow w b
  have hfactor : ∀ i : C.ι,
      1 + C.factorWeight L i ≤
        (2 : ℝ) ^
          (3 * Real.logb 2 (Nat.card (C.factor i) : ℝ) * X) := by
    intro i
    let a : ℝ := Real.logb 2 (Nat.card (C.factor i) : ℝ)
    have ha : 1 ≤ a := by
      letI : IsSimpleGroup (C.factor i) := C.simple i
      dsimp [a]
      rw [Real.le_logb_iff_rpow_le (by norm_num)
        (by exact_mod_cast (Nat.card_pos (α := C.factor i)))]
      norm_num
      exact_mod_cast Finite.one_lt_card (α := C.factor i)
    have ha0 : 0 ≤ a := le_trans (by norm_num) ha
    have hw2 := C.factorPermutation_degree_two_le i
    have hX2 : (2 : ℝ) ≤ X := by
      have he : Real.logb 2 (4 : ℝ) = 2 := by
        calc
          _ = Real.logb 2 ((2 : ℝ) ^ (2 : ℕ)) := by norm_num
          _ = 2 * Real.logb 2 2 := Real.logb_pow 2 2 2
          _ = 2 := by rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]; norm_num
      calc
        (2 : ℝ) = Real.logb 2 4 := he.symm
        _ ≤ X := Real.logb_le_logb_of_le (by norm_num) (by norm_num)
          (by exact_mod_cast (show 4 ≤ w + b + 2 by omega))
    have hautNat := hAut (C.factor i) (C.simple i) (C.centerless i)
    have haut : (Nat.card (C.factor i ≃* C.factor i) : ℝ) ≤
        (Nat.card (C.factor i) : ℝ) ^ (2 : ℕ) := by
      exact_mod_cast hautNat
    have hden : L / a ≤ L := div_le_self hL ha
    have hweight : C.factorWeight L i ≤
        (Nat.card (C.factor i ≃* C.factor i) : ℝ) * L := by
      unfold SemisimpleNormalChart.factorWeight
      exact mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg _)
    have hautone : (1 : ℝ) ≤ Nat.card (C.factor i ≃* C.factor i) := by
      exact_mod_cast Nat.card_pos
    have hcardpos : (0 : ℝ) < Nat.card (C.factor i) := by
      exact_mod_cast Nat.card_pos (α := C.factor i)
    have hcardrepr : (2 : ℝ) ^ a = (Nat.card (C.factor i) : ℝ) := by
      dsimp [a]
      exact Real.rpow_logb (by norm_num) (by norm_num) hcardpos
    have hautExp : (Nat.card (C.factor i ≃* C.factor i) : ℝ) ≤
        (2 : ℝ) ^ (a * X) := by
      calc
        (Nat.card (C.factor i ≃* C.factor i) : ℝ) ≤
            (Nat.card (C.factor i) : ℝ) ^ (2 : ℕ) := haut
        _ = ((2 : ℝ) ^ a) ^ (2 : ℕ) := by rw [hcardrepr]
        _ = ((2 : ℝ) ^ a) ^ (2 : ℝ) := (Real.rpow_two _).symm
        _ = (2 : ℝ) ^ (a * 2) := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        _ ≤ (2 : ℝ) ^ (a * X) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (mul_le_mul_of_nonneg_left hX2 ha0)
    calc
      1 + C.factorWeight L i ≤
          1 + (Nat.card (C.factor i ≃* C.factor i) : ℝ) * L :=
        by simpa [add_comm] using add_le_add_right hweight 1
      _ ≤ (Nat.card (C.factor i ≃* C.factor i) : ℝ) * (L + 1) := by
        nlinarith
      _ ≤ (2 : ℝ) ^ (a * X) * (2 : ℝ) ^ (2 * X) :=
        mul_le_mul hautExp hLone (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (a * X + 2 * X) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (3 * a * X) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        nlinarith
      _ = (2 : ℝ) ^
          (3 * Real.logb 2 (Nat.card (C.factor i) : ℝ) * X) := rfl
  have hcardE : Nat.card E = ∏ i : C.ι, Nat.card (C.factor i) := by
    calc
      Nat.card E = Nat.card ((i : C.ι) → C.factor i) :=
        Nat.card_congr C.equiv.toEquiv
      _ = ∏ i : C.ι, Nat.card (C.factor i) := Nat.card_pi
  have hsumEq :
      (∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i) : ℝ)) =
        Real.logb 2 (Nat.card E : ℝ) := by
    symm
    rw [hcardE]
    exact logb_two_prod_nat Finset.univ (fun i => Nat.card (C.factor i))
      (fun i _ => Nat.card_pos)
  have hcardEfac : Nat.card E ≤ Nat.factorial w := by
    calc
      Nat.card E ≤ Nat.card U := Subgroup.card_le_card_group E
      _ ≤ Nat.card (Equiv.Perm (Fin w)) := Subgroup.card_le_card_group U
      _ = Nat.factorial w := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  have hsum :
      (∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i) : ℝ)) ≤
        (w : ℝ) * X := by
    rw [hsumEq]
    have h1 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (by exact_mod_cast (Nat.card_pos (α := E)) : (0 : ℝ) < Nat.card E)
      (by
        have hcast : (Nat.card E : ℝ) ≤ (Nat.factorial w : ℝ) := by
          exact_mod_cast hcardEfac
        exact hcast)
    by_cases hw : w = 0
    · subst w
      norm_num at hcardEfac
      have hEpos : 0 < Fintype.card E := Fintype.card_pos
      have hE : Fintype.card E = 1 := by omega
      rw [Nat.card_eq_fintype_card, hE]
      simp
    · have hfac : Nat.factorial w ≤ w ^ w := w.factorial_le_pow
      have hfacCast : (Nat.factorial w : ℝ) ≤ (((w ^ w : ℕ) : ℝ)) := by
        exact_mod_cast hfac
      have h2 := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
        (by positivity : (0 : ℝ) < Nat.factorial w)
        hfacCast
      calc
        Real.logb 2 (Nat.card E : ℝ) ≤
            Real.logb 2 (Nat.factorial w : ℝ) := h1
        _ ≤ Real.logb 2 (((w ^ w : ℕ) : ℝ)) := h2
        _ = (w : ℝ) * Real.logb 2 (w : ℝ) := by
          rw [Nat.cast_pow, Real.logb_pow]
        _ ≤ (w : ℝ) * X := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
            (by exact_mod_cast (Nat.pos_of_ne_zero hw))
          exact_mod_cast (show w ≤ w + b + 2 by omega)
  unfold SemisimpleNormalChart.outerFactor
  calc
    (∏ i : C.ι, (1 + C.factorWeight L i)) ≤
        ∏ i : C.ι,
          (2 : ℝ) ^
            (3 * Real.logb 2 (Nat.card (C.factor i) : ℝ) * X) :=
      Finset.prod_le_prod
        (fun i _ => add_nonneg zero_le_one (C.factorWeight_nonneg hL i))
        (fun i _ => hfactor i)
    _ = (2 : ℝ) ^
        (∑ i : C.ι,
          (3 * Real.logb 2 (Nat.card (C.factor i) : ℝ) * X)) := by
      exact (Real.rpow_sum_of_pos (by norm_num) _ Finset.univ).symm
    _ = (2 : ℝ) ^
        (3 * X *
          (∑ i : C.ι, Real.logb 2 (Nat.card (C.factor i) : ℝ))) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ (2 : ℝ) ^ (3 * X * ((w : ℝ) * X)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      exact mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (by norm_num) (le_trans (by norm_num) hX))
    _ = (2 : ℝ) ^
        (3 * (w : ℝ) *
          (Real.logb 2 ((w + b + 2 : ℕ) : ℝ)) ^ 2) := by
      dsimp [X]
      ring

end Non2UnipotentPrefixFiniteMenu
end SymmetricSubgroupAsymptotics
