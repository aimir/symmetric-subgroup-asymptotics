import SymmetricSubgroupAsymptotics.CFSGCoprimeTransitiveFactorActions
import SymmetricSubgroupAsymptotics.CFSGCoprimeProductNormalGenerators
import SymmetricSubgroupAsymptotics.CFSGNilpotentPrimeFactors
import SymmetricSubgroupAsymptotics.CFSGPrimeOrdinaryActionProfile

/-! Coarse ambient normal rank for actual odd nilpotent transitive actions.
Induction uses their actual coprime Sylow fibres and keeps the SAME normal
subgroup through the original product equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOddNilpotentCoarseNormalRank
open MarkedC4

/-- An odd nontrivial group acting faithfully on its coset fibre needs at
least three points. Both oddness and faithfulness refer to this fibre. -/
theorem coset_degree_ge_three {G : Type} [Group G] [Finite G] [Nontrivial G]
    (K : Subgroup G) [FaithfulSMul G (G ⧸ K)] (hodd : ¬2 ∣ Nat.card G) :
    3 ≤ Nat.card (G ⧸ K) := by
  have hlarge : 1 < Nat.card (G ⧸ K) := by
    by_contra hn
    letI : Subsingleton (G ⧸ K) := Finite.card_le_one_iff_subsingleton.mp (by omega)
    have hs : Subsingleton G := ⟨fun a b =>
      eq_of_smul_eq_smul (α := G ⧸ K) (fun x => Subsingleton.elim _ _)⟩
    exact (not_subsingleton G) hs
  have hne2 : Nat.card (G ⧸ K)≠2 := by
    intro htwo
    apply hodd
    have hd : Nat.card (G ⧸ K) ∣ Nat.card G := K.index_dvd_card
    rw [htwo] at hd
    exact hd
  omega

/-- Every original ambient-normal subgroup satisfies n/3. This is not an
assumption about an independently substituted permutation model. -/
theorem normalGen_real_le_third
    {G X : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    [Finite X] [Nonempty X] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X] (hodd : ¬2 ∣ Nat.card G)
    (N : Subgroup G) [N.Normal] : (normalGen N : ℝ) ≤ (Nat.card X : ℝ)/3 := by
  suffices hh : ∀ n : ℕ,∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G],
      Nat.card G=n → ∀ (X : Type) [Finite X] [Nonempty X] [MulAction G X]
        [FaithfulSMul G X] [MulAction.IsPretransitive G X],
      (¬2 ∣ Nat.card G) → ∀ (N : Subgroup G) [N.Normal],
        (normalGen N : ℝ) ≤ (Nat.card X : ℝ)/3 by
    exact hh (Nat.card G) G rfl X hodd N
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ _ hcard X _ _ _ _ _ hodd N _
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
      have hr := CFSGPrimeOrdinaryActionProfile.normalGen_real_le_div (X := X) hGp N
      apply hr.trans
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) < 3)
      exact_mod_cast hp3
    · letI : Nontrivial P := Finite.one_lt_card_iff_nontrivial.mp
        (by have := Nat.card_pos (α := P);omega)
      letI : Nontrivial O := Finite.one_lt_card_iff_nontrivial.mp
        (by have := Nat.card_pos (α := O);omega)
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
      have hOlt : Nat.card O < n := by
        rw [←hcard,hecard]
        have hPgt : 1 < Nat.card P := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
        have := Nat.card_pos (α := O)
        nlinarith
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
      let x : X := Classical.arbitrary X
      let A := CFSGCoprimeTransitiveFactorActions.LeftFiber (P := P) (O := O) x
      let B := CFSGCoprimeTransitiveFactorActions.RightFiber (P := P) (O := O) x
      letI : FaithfulSMul P A := CFSGCoprimeTransitiveFactorActions.left_faithful hcop x
      letI : FaithfulSMul O B := CFSGCoprimeTransitiveFactorActions.right_faithful hcop x
      have hA3 : 3 ≤ Nat.card A := coset_degree_ge_three _ hPodd
      have hB3 : 3 ≤ Nat.card B := coset_degree_ge_three _ hOodd
      have hprod : Nat.card A*Nat.card B=Nat.card X :=
        CFSGCoprimeTransitiveFactorActions.degree_product hcop x
      let M := N.map e.toMonoidHom
      letI : M.Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
      have hMeq := ActualMarkZeroNormalRank.normalGen_map_eq e.toMonoidHom e.surjective N
        (fun a _ ha => e.injective (ha.trans (map_one e).symm))
      let f : P × O →* P := MonoidHom.fst P O
      let g : P × O →* O := MonoidHom.snd P O
      letI : (M.map f).Normal := Subgroup.Normal.map inferInstance f (fun a => ⟨(a,1),rfl⟩)
      letI : (M.map g).Normal := Subgroup.Normal.map inferInstance g (fun b => ⟨(1,b),rfl⟩)
      have hleft := CFSGPrimeOrdinaryActionProfile.normalGen_real_le_div (X := A) hPp (M.map f)
      have hleft3 : (normalGen (M.map f) : ℝ) ≤ (Nat.card A : ℝ)/3 := by
        apply hleft.trans
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) < 3)
        exact_mod_cast hp3
      have hright := ih (Nat.card O) hOlt O rfl B hOodd (M.map g)
      have hm := CFSGCoprimeProductNormalGenerators.normalGen_le_max hcop M
      have hmR : (normalGen N : ℝ) ≤ max (normalGen (M.map f) : ℝ) (normalGen (M.map g) : ℝ) := by
        rw [←hMeq]
        exact_mod_cast hm
      apply hmR.trans (max_le _ _)
      · apply hleft3.trans
        have hpr : (Nat.card A : ℝ)*(Nat.card B : ℝ)=Nat.card X := by exact_mod_cast hprod
        have hbR : (3 : ℝ) ≤ Nat.card B := by exact_mod_cast hB3
        have haR : (0 : ℝ) ≤ Nat.card A := Nat.cast_nonneg _
        nlinarith
      · apply hright.trans
        have hpr : (Nat.card A : ℝ)*(Nat.card B : ℝ)=Nat.card X := by exact_mod_cast hprod
        have haR : (3 : ℝ) ≤ Nat.card A := by exact_mod_cast hA3
        have hbR : (0 : ℝ) ≤ Nat.card B := Nat.cast_nonneg _
        nlinarith

end SymmetricSubgroupAsymptotics.CFSGOddNilpotentCoarseNormalRank
