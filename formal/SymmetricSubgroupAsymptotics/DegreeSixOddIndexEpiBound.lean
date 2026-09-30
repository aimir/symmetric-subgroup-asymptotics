import SymmetricSubgroupAsymptotics.DegreeSixOddIndexStructure
import SymmetricSubgroupAsymptotics.KovacsPraegerAbelianization
import SymmetricSubgroupAsymptotics.FusionEpimorphismTransport
import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseMass

/-!
# Every quotient of a degree-six odd-index-two owner

For every original normal subgroup `N` of the owner `U`, the onto maps from
an arbitrary permutation source of degree `b` to the literal quotient `U/N`
number at most a fixed constant times `2^(8b/15)`.

Write `A` for the image of the ternary base.  If `N` is trivial and the base
has order nine, the stabilizer character labels the maps to `U` itself.
Otherwise `A` has order at most three.  When conjugation by the outside
coset acts nontrivially on `A`, one injective character labels the maps;
when it acts trivially, the quotient is abelian with a sixfold embedding and
the Kovács--Praeger input applies.  No quotient is classified.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

/-- The ternary label count in the degree-six exponent. -/
theorem ternaryLabel_real_bound {Q : Type*} [Group Q] (b : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (h : Nat.card (GroupEpimorphism J Q) ≤
      Nat.card (PrimeCharacters 3 (commPowSubgroup J 2)) * Nat.card (Q ≃* Q)) :
    (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
      Nat.card (Q ≃* Q) * (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hc : Nat.card (PrimeCharacters 3 (commPowSubgroup J 2)) ≤ 3 ^ (b / 3) :=
    primeCharacters_commPow_card_le (p := 3) (q := 2) b J 3
      (fun G X _ _ _ _ _ => permutation_ternaryCharacterRank_le_third G X)
  have hpow : (3 : ℝ) ^ (b / 3) ≤ (2 : ℝ) ^ ((8 / 15 : ℝ) * b) :=
    ternaryPower_le_primeBase_eight_fifteenths b (b / 3) (Nat.mul_div_le b 3)
  calc (Nat.card (GroupEpimorphism J Q) : ℝ) ≤
        (Nat.card (PrimeCharacters 3 (commPowSubgroup J 2)) : ℝ) * Nat.card (Q ≃* Q) := by
        exact_mod_cast h
    _ ≤ (3 : ℝ) ^ (b / 3) * Nat.card (Q ≃* Q) := by
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        exact_mod_cast hc
    _ ≤ (2 : ℝ) ^ ((8 / 15 : ℝ) * b) * Nat.card (Q ≃* Q) :=
        mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

/-- The Kovács--Praeger bound in the degree-six exponent. -/
theorem kovacsPraeger_real_bound (b : ℕ) :
    (3 : ℝ) ^ ((b : ℝ) / 3) ≤ (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  have h := c1_ternary_rpow_envelope (x := (b : ℝ) / 3) (by positivity)
  convert h using 2
  ring

/-- A finite group of order at most `p` in which every element has order
dividing `p` embeds in the cyclic group of order `p`. -/
theorem exists_injective_zmod_of_card_le {B : Type*} [Group B] [Finite B] (p : ℕ)
    [Fact p.Prime] (hB : IsPGroup p B) (hcard : Nat.card B ≤ p) :
    ∃ ι : B →* Multiplicative (ZMod p), Function.Injective ι := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  have hp := (Fact.out : p.Prime)
  rcases k with _ | k
  · refine ⟨1, fun x y _ => ?_⟩
    have : Subsingleton B := by
      rw [pow_zero] at hk
      exact (Nat.card_eq_one_iff_unique.mp hk).1
    exact Subsingleton.elim x y
  · have hk1 : k = 0 := by
      by_contra h
      have : p ^ 2 ≤ p ^ (k + 1) := Nat.pow_le_pow_right hp.pos (by omega)
      have hp2 : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
    subst hk1
    rw [zero_add, pow_one] at hk
    have hZ : Nat.card (Multiplicative (ZMod p)) = p :=
      (Nat.card_congr Multiplicative.toAdd).trans (Nat.card_zmod p)
    exact ⟨(mulEquivOfPrimeCardEq hk hZ).toMonoidHom, (mulEquivOfPrimeCardEq hk hZ).injective⟩

namespace C1OddIndexTwoOwnerWitness

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    [MulAction.IsPretransitive U X]

/-- A nontrivial original normal subgroup meets a ternary base of order
nine nontrivially: otherwise it would be central and conjugation outside the
base would be trivial on the base. -/
theorem ternary_meets_normal (W : C1OddIndexTwoOwnerWitness U) (hX : Nat.card X = 6)
    (hT9 : Nat.card W.ternary = 9) (N : Subgroup U) [hNn : N.Normal] (hN : N ≠ ⊥) :
    ∃ t : W.ternary, t ≠ 1 ∧ (t : U) ∈ N := by
  letI := W.normal
  by_contra hno
  push_neg at hno
  have hkbot : ∀ u : U, u ∈ W.ternary → u ∈ N → u = 1 := by
    intro u hu huN
    by_contra h1
    exact hno ⟨u, hu⟩ (fun h => h1 (congrArg Subtype.val h)) huN
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hN
  have hz1' : (z : U) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzT : (z : U) ∉ W.ternary := fun hzT => hz1' (hkbot _ hzT z.2)
  have hzcent : ∀ g : U, g * (z : U) * g⁻¹ = z := by
    intro g
    have hmem : g * (z : U) * g⁻¹ ∈ N := hNn.conj_mem _ z.2 g
    rcases W.mem_or_inv_mul_mem hzT (g * (z : U) * g⁻¹) with hT | hT
    · exfalso
      apply hz1'
      have h := hkbot _ hT hmem
      calc (z : U) = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    · have h := hkbot _ hT (N.mul_mem (N.inv_mem z.2) hmem)
      calc g * (z : U) * g⁻¹ = (z : U) * ((z : U)⁻¹ * (g * z * g⁻¹)) := by group
        _ = z := by rw [h, mul_one]
  obtain ⟨s0, hs0⟩ := W.exists_not_mem
  obtain ⟨v, hv⟩ := W.conj_not_trivial hX hT9 s0 hs0
  apply hv
  apply Subtype.ext
  simp only [MulAut.conjNormal_apply]
  have hw : s0⁻¹ * (z : U) ∈ W.ternary := (W.mem_or_inv_mul_mem hs0 z).resolve_left hzT
  have hc : (s0⁻¹ * (z : U)) * (v : U) = (v : U) * (s0⁻¹ * z) :=
    congrArg Subtype.val (W.ternary_comm hX ⟨_, hw⟩ v)
  have hwv : (s0⁻¹ * (z : U))⁻¹ * (v : U) * (s0⁻¹ * z) = v := by
    rw [mul_assoc, ← hc, inv_mul_cancel_left]
  have hzv : (z : U) * v * (z : U)⁻¹ = v := by
    calc (z : U) * v * (z : U)⁻¹ = ((v : U) * z * (v : U)⁻¹) * v * (z : U)⁻¹ := by
          rw [hzcent (v : U)]
      _ = v := by group
  calc s0 * (v : U) * s0⁻¹ = (z : U) * ((s0⁻¹ * (z : U))⁻¹ * (v : U) * (s0⁻¹ * z)) *
        (z : U)⁻¹ := by group
    _ = (z : U) * v * (z : U)⁻¹ := by rw [hwv]
    _ = v := hzv

/-- Outside the case of the trivial axis over a base of order nine, the
base has image of order at most three. -/
theorem image_card_le_three (W : C1OddIndexTwoOwnerWitness U) (hX : Nat.card X = 6)
    (N : Subgroup U) [N.Normal] (hbig : ¬ (N = ⊥ ∧ Nat.card W.ternary = 9)) :
    Nat.card (W.ternary.map (QuotientGroup.mk' N)) ≤ 3 := by
  let ψ : W.ternary →* U ⧸ N := (QuotientGroup.mk' N).comp W.ternary.subtype
  have hrange : ψ.range = W.ternary.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hsplit : Nat.card W.ternary = Nat.card ψ.range * Nat.card ψ.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [← hrange]
  have hk : 0 < Nat.card ψ.ker := Nat.card_pos
  rcases W.ternary_card hX with hT3 | hT9
  · have := Nat.le_mul_of_pos_right (Nat.card ψ.range) hk
    omega
  · have hN : N ≠ ⊥ := fun h => hbig ⟨h, hT9⟩
    obtain ⟨t, ht1, htN⟩ := W.ternary_meets_normal hX hT9 N hN
    have htk : t ∈ ψ.ker := by
      change QuotientGroup.mk' N (t : U) = 1
      exact (QuotientGroup.eq_one_iff _).mpr htN
    have hne1 : Nat.card ψ.ker ≠ 1 := by
      intro h1
      rw [Subgroup.card_eq_one] at h1
      rw [h1] at htk
      exact ht1 (Subgroup.mem_bot.mp htk)
    have hdvd : Nat.card ψ.ker ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hT9]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨i, hi, hki⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    have h3k : 3 ≤ Nat.card ψ.ker := by
      rcases Nat.lt_or_ge i 1 with hi0 | hi1
      · have : i = 0 := by omega
        subst this
        rw [pow_zero] at hki
        exact absurd hki hne1
      · rw [hki]
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ i := Nat.pow_le_pow_right (by norm_num) hi1
    by_contra h
    push_neg at h
    have h12 := Nat.mul_le_mul h h3k
    rw [← hsplit, hT9] at h12
    omega

/-- The uniform quotient-epimorphism bound for one original normal axis. -/
theorem quotientEpimorphism_bound (W : C1OddIndexTwoOwnerWitness U)
    (hKP : KovacsPraegerAbelianizationBound)
    (hX : Nat.card X = 6) (N : Subgroup U) [N.Normal]
    (b : ℕ) (J : Subgroup (Equiv.Perm (Fin b))) :
    (Nat.card (GroupEpimorphism J (U ⧸ N)) : ℝ) ≤
      ((Nat.card (U ≃* U) : ℝ) + Nat.card ((U ⧸ N) ≃* (U ⧸ N)) + 1) *
        (2 : ℝ) ^ ((8 / 15 : ℝ) * b) := by
  letI := W.normal
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨s0, hs0⟩ := W.exists_not_mem
  set E : ℝ := (2 : ℝ) ^ ((8 / 15 : ℝ) * b) with hE
  have hEnn : 0 ≤ E := by positivity
  have haut1 : (0 : ℝ) ≤ Nat.card (U ≃* U) := Nat.cast_nonneg _
  have haut2 : (0 : ℝ) ≤ Nat.card ((U ⧸ N) ≃* (U ⧸ N)) := Nat.cast_nonneg _
  by_cases hbig : N = ⊥ ∧ Nat.card W.ternary = 9
  · obtain ⟨hN, hT9⟩ := hbig
    have hcongr : Nat.card (GroupEpimorphism J (U ⧸ N)) =
        Nat.card (GroupEpimorphism J U) :=
      fusionGroupEpimorphism_card_congr (MulEquiv.refl J)
        ((QuotientGroup.quotientMulEquivOfEq hN).trans QuotientGroup.quotientBot)
    have hne : Nonempty X := (Nat.card_pos_iff.mp (by rw [hX]; norm_num)).1
    obtain ⟨x0⟩ := hne
    letI : Fintype (U ⧸ W.ternary) := Fintype.ofFinite _
    have hlab := groupEpimorphism_card_le_ternarySign (J := J) W.ternary
      (W.ternary_comm hX) (W.ternary_pow_three hX) W.sq_mem s0 hs0 W.quotient_card
      (W.stabilizerCharacter hX hT9 x0)
      (fun t h1 h2 => W.stabilizerCharacter_pair hX hT9 x0 s0 hs0 t h1 h2)
      (W.conj_not_trivial hX hT9 s0 hs0)
    have hreal := ternaryLabel_real_bound b J hlab
    rw [hcongr]
    calc _ ≤ (Nat.card (U ≃* U) : ℝ) * E := hreal
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hEnn
  -- Otherwise the image of the base has order at most three.
  let φ : U →* U ⧸ N := QuotientGroup.mk' N
  let A : Subgroup (U ⧸ N) := W.ternary.map φ
  haveI hAn : A.Normal := Subgroup.Normal.map W.normal φ (QuotientGroup.mk'_surjective N)
  let s : U ⧸ N := φ s0
  have hmemA (t : U) (ht : t ∈ W.ternary) : φ t ∈ A := Subgroup.mem_map_of_mem φ ht
  have hA : ∀ a c : A, a * c = c * a := by
    intro a c
    obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨t', ht', htc⟩ := Subgroup.mem_map.mp c.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hta, ← htc, ← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (W.ternary_comm hX ⟨t, ht⟩ ⟨t', ht'⟩)
  have h3 : ∀ a : A, a ^ 3 = 1 := by
    intro a
    obtain ⟨t, ht, hta⟩ := Subgroup.mem_map.mp a.2
    apply Subtype.ext
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hta, ← map_pow]
    have := congrArg Subtype.val (W.ternary_pow_three hX ⟨t, ht⟩)
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this
    rw [this, map_one]
  have hsq : ∀ x : U ⧸ N, x ^ 2 ∈ A := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_pow]
    exact hmemA _ (W.sq_mem u)
  have hQA : ∀ x : U ⧸ N, x ∈ A ∨ s⁻¹ * x ∈ A := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective N x
    rcases W.mem_or_inv_mul_mem hs0 u with hu | hu
    · exact Or.inl (hmemA u hu)
    · right
      have := hmemA _ hu
      rwa [map_mul, map_inv] at this
  -- The image has order at most three.
  have hApg : IsPGroup 3 A := W.ternaryPGroup.map φ
  have hsmall : Nat.card A ≤ 3 := W.image_card_le_three hX N hbig
  obtain ⟨ιA, hιA⟩ := exists_injective_zmod_of_card_le 3 hApg hsmall
  letI : Fintype ((U ⧸ N) ⧸ A) := Fintype.ofFinite _
  have hcardQA : Nat.card ((U ⧸ N) ⧸ A) ≤ 2 := by
    have hsub : (Finset.univ : Finset ((U ⧸ N) ⧸ A)) ⊆ {1, QuotientGroup.mk s} := by
      intro c _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rcases hQA x with hx | hx
      · exact Or.inl ((QuotientGroup.eq_one_iff x).mpr hx)
      · exact Or.inr (QuotientGroup.eq.mpr hx).symm
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    exact this.trans (Finset.card_le_two)
  by_cases hσ : ∃ v : A, MulAut.conjNormal s v ≠ v
  · have hs : s ∉ A := by
      intro hsA
      obtain ⟨v, hv⟩ := hσ
      exact hv (conjNormal_self_of_mem A hA hsA v)
    have hindex : Nat.card ((U ⧸ N) ⧸ A) = 2 := by
      have hne : (1 : (U ⧸ N) ⧸ A) ≠ QuotientGroup.mk s := by
        intro h
        exact hs ((QuotientGroup.eq_one_iff s).mp h.symm)
      have := Finset.card_le_univ ({1, QuotientGroup.mk s} : Finset ((U ⧸ N) ⧸ A))
      rw [Finset.card_pair hne, ← Nat.card_eq_fintype_card] at this
      omega
    have hlab := groupEpimorphism_card_le_ternarySign (J := J) A hA h3 hsq s hs hindex ιA
      (fun v h1 _ => hιA (h1.trans ιA.map_one.symm)) hσ
    have hreal := ternaryLabel_real_bound b J hlab
    calc _ ≤ (Nat.card ((U ⧸ N) ≃* (U ⧸ N)) : ℝ) * E := hreal
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hEnn
  · push_neg at hσ
    have hsA (a : U ⧸ N) (ha : a ∈ A) : Commute s a := by
      have h := congrArg Subtype.val (hσ ⟨a, ha⟩)
      simp only [MulAut.conjNormal_apply] at h
      exact (mul_inv_eq_iff_eq_mul.mp h)
    have hAA (a c : U ⧸ N) (ha : a ∈ A) (hc : c ∈ A) : Commute a c :=
      congrArg Subtype.val (hA ⟨a, ha⟩ ⟨c, hc⟩)
    have hform (x : U ⧸ N) : ∃ a ∈ A, x = a ∨ x = s * a := by
      rcases hQA x with hx | hx
      · exact ⟨x, hx, Or.inl rfl⟩
      · exact ⟨s⁻¹ * x, hx, Or.inr (by group)⟩
    have hQcomm (x y : U ⧸ N) : Commute x y := by
      obtain ⟨a, ha, hx⟩ := hform x
      obtain ⟨c, hc, hy⟩ := hform y
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
      · exact hAA a c ha hc
      · exact ((hsA a ha).symm).mul_right (hAA a c ha hc)
      · exact ((hsA c hc).mul_left (hAA a c ha hc))
      · exact ((Commute.refl s).mul_right (hsA c hc)).mul_left
          ((hsA a ha).symm.mul_right (hAA a c ha hc))
    obtain ⟨ι2, hι2⟩ : ∃ ι2 : (U ⧸ N) →* Multiplicative (ZMod 2),
        ∀ x, ι2 x = 1 → x ∈ A := by
      have hpg : IsPGroup 2 ((U ⧸ N) ⧸ A) := by
        intro c
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
        refine ⟨1, ?_⟩
        rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
        exact hsq x
      obtain ⟨e, he⟩ := exists_injective_zmod_of_card_le 2 hpg hcardQA
      refine ⟨e.comp (QuotientGroup.mk' A), fun x hx => ?_⟩
      have : QuotientGroup.mk' A x = 1 := he (hx.trans e.map_one.symm)
      exact (QuotientGroup.eq_one_iff x).mp this
    let fourth : (U ⧸ N) →* A :=
      { toFun := fun x => ⟨x ^ 4, by
          rw [show x ^ 4 = (x ^ 2) ^ 2 by group]
          exact A.pow_mem (hsq x) 2⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := fun x y => by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          exact (hQcomm x y).mul_pow 4 }
    let ι3 : (U ⧸ N) →* Multiplicative (ZMod 3) := ιA.comp fourth
    have hjoint : ∀ x : U ⧸ N, ι2 x = 1 → ι3 x = 1 → x = 1 := by
      intro x hx2 hx3
      have hxA := hι2 x hx2
      have h4 : fourth x = 1 := hιA (hx3.trans ιA.map_one.symm)
      have h4' : x ^ 4 = 1 := congrArg Subtype.val h4
      have hx3' : x ^ 3 = 1 := congrArg Subtype.val (h3 ⟨x, hxA⟩)
      calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
        _ = 1 := by rw [h4', hx3', inv_one, one_mul]
    have hkp := groupEpimorphism_card_le_of_kovacsPraeger hKP ι2 ι3 hjoint b J
    calc _ ≤ (3 : ℝ) ^ ((b : ℝ) / 3) := hkp
      _ ≤ E := kovacsPraeger_real_bound b
      _ ≤ _ := by
          have : (1 : ℝ) ≤ (Nat.card (U ≃* U) : ℝ) + Nat.card ((U ⧸ N) ≃* (U ⧸ N)) + 1 := by
            linarith
          nlinarith

end C1OddIndexTwoOwnerWitness
end SymmetricSubgroupAsymptotics

end
