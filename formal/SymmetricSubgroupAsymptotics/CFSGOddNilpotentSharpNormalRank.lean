import SymmetricSubgroupAsymptotics.CFSGOddNilpotentMixedNormalRank

/-! The sharp-enough odd nilpotent normal-rank profile on the SAME action.
Mixed sectors improve to n/9; pure primes use the proved central-frame
recurrence. Only an active three-point diagonal is exceptional. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOddNilpotentSharpNormalRank
open MarkedC4

/-- Outside degree3 every ambient normal subgroup costs at most2n/9. -/
theorem normalGen_real_le_two_ninths
    {G X : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    [Finite X] [Nonempty X] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X] (hodd : ¬2 ∣ Nat.card G)
    (hdegree : Nat.card X≠3) (N : Subgroup G) [N.Normal] :
    (normalGen N : ℝ) ≤ (2/9 : ℝ)*Nat.card X := by
  by_cases hG1 : Nat.card G=1
  · letI : Subsingleton G := (Nat.card_eq_one_iff_unique.mp hG1).1
    have hN : N=⊥ := Subsingleton.elim _ _
    rw [hN,normalGen_bot,Nat.cast_zero]
    positivity
  obtain ⟨p,hp,hpdvd⟩ := Nat.exists_prime_and_dvd hG1
  letI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by
    have hp2 : p≠2 := by intro h;exact hodd (h ▸ hpdvd)
    have := hp.two_le
    omega
  let P := CFSGNilpotentPrimeFactors.PrimePart p G
  let O := CFSGNilpotentPrimeFactors.RestPart p G
  let e : G ≃* P × O := CFSGNilpotentPrimeFactors.equiv p G
  have hecard : Nat.card G=Nat.card P*Nat.card O := by
    rw [Nat.card_congr e.toEquiv,Nat.card_prod]
  have hcop : Nat.Coprime (Nat.card P) (Nat.card O) :=
    CFSGNilpotentPrimeFactors.factors_coprime p G
  have hPp : IsPGroup p P := CFSGNilpotentPrimeFactors.prime_isPGroup p G
  have hOcop : Nat.Coprime (Nat.card O) p := CFSGNilpotentPrimeFactors.rest_card_coprime p G
  have hP1 : Nat.card P≠1 := by
    intro h1
    have hd : p ∣ Nat.card O := by simpa only [hecard,h1,one_mul] using hpdvd
    exact (hp.coprime_iff_not_dvd.mp hOcop.symm) hd
  by_cases hO1 : Nat.card O=1
  · obtain ⟨k,hk⟩ := hPp.exists_card_eq
    have hGp : IsPGroup p G := IsPGroup.of_card (n := k)
      (by rw [hecard,hO1,mul_one,hk])
    by_cases hpEq3 : p=3
    · have hG3 : IsPGroup 3 G := hpEq3 ▸ hGp
      exact CFSGPrimeOrdinaryActionProfile.ternary_normalGen_real_le_of_degree_ne_three
        (X := X) hG3 hdegree N
    · have hp5 : 5 ≤ p := by
        have hp4 : p≠4 := by intro h;rw [h] at hp;norm_num at hp
        omega
      have hr := CFSGPrimeOrdinaryActionProfile.normalGen_real_le_div (X := X) hGp N
      apply hr.trans
      apply (div_le_iff₀ (show (0 : ℝ) < p by exact_mod_cast hp.pos)).mpr
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have hnR : (0 : ℝ) ≤ Nat.card X := Nat.cast_nonneg _
      nlinarith
  · letI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp
      (by have := Nat.card_pos (α := P);omega)
    letI : Nontrivial O := Finite.one_lt_card_iff_nontrivial.mp
      (by have := Nat.card_pos (α := O);omega)
    letI : Group.IsNilpotent P := hPp.isNilpotent
    have hOodd : ¬2 ∣ Nat.card O := by
      intro hd
      apply hodd
      rw [hecard]
      exact dvd_mul_of_dvd_right hd _
    have hPodd : ¬2 ∣ Nat.card P := by
      intro hd
      apply hodd
      rw [hecard]
      exact dvd_mul_of_dvd_left hd _
    letI : MulAction (P × O) X := MulAction.compHom X e.symm.toMonoidHom
    letI : FaithfulSMul (P × O) X := ⟨fun {a b} hab => e.symm.injective
      (eq_of_smul_eq_smul (α := X) hab)⟩
    letI : MulAction.IsPretransitive (P × O) X := by
      constructor
      intro x y
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G x y
      refine ⟨e g,?_⟩
      change e.symm (e g) • x=y
      simpa only [e.symm_apply_apply] using hg
    let M := N.map e.toMonoidHom
    letI : M.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
    have heq := ActualMarkZeroNormalRank.normalGen_map_eq e.toMonoidHom e.surjective N
      (fun a _ ha => e.injective (ha.trans (map_one e).symm))
    have hm := CFSGOddNilpotentMixedNormalRank.normalGen_real_le_ninth
      (X := X) hcop hPodd hOodd M
    rw [heq] at hm
    nlinarith [show (0 : ℝ) ≤ (Nat.card X : ℝ) from Nat.cast_nonneg _]

/-- A final actual-diagonal profile for the exceptional-density theorem.
The exceptional predicate keeps both the original degree and nontriviality. -/
theorem normalGen_real_le_with_exception
    {G X : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    [Finite X] [Nonempty X] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X] (hodd : ¬2 ∣ Nat.card G)
    (N : Subgroup G) [N.Normal] :
    (normalGen N : ℝ) ≤ (2/9 : ℝ)*Nat.card X+
      (if Nat.card X=3 ∧ N≠⊥ then (1/9 : ℝ)*Nat.card X else 0) := by
  by_cases hN : N=⊥
  · subst N
    simp only [normalGen_bot,Nat.cast_zero,ne_eq,not_true_eq_false,and_false,if_false,add_zero]
    positivity
  by_cases hd : Nat.card X=3
  · rw [if_pos ⟨hd,hN⟩]
    have hh := CFSGOddNilpotentCoarseNormalRank.normalGen_real_le_third (X := X) hodd N
    nlinarith
  · rw [if_neg (by tauto),add_zero]
    exact normalGen_real_le_two_ninths (X := X) hodd hd N

end SymmetricSubgroupAsymptotics.CFSGOddNilpotentSharpNormalRank
