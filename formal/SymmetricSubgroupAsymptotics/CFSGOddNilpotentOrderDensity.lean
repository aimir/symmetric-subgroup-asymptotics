import SymmetricSubgroupAsymptotics.CFSGOddNilpotentCoarseNormalRank
import SymmetricSubgroupAsymptotics.CFSGOddPermutationDensity

/-! The order density of an original odd nilpotent transitive action.
Its actual coprime factor degrees multiply to the original degree, so the
prime bound sqrt(3)^degree survives without a supplied product model. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGOddNilpotentOrderDensity
open MarkedC4 CFSGOddNilpotentCoarseNormalRank

theorem log_order_le
    {G X : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    [Finite X] [Nonempty X] [MulAction G X] [FaithfulSMul G X]
    [MulAction.IsPretransitive G X] (hodd : ¬2 ∣ Nat.card G) :
    Real.logb 2 (Nat.card G) ≤ (Real.logb 2 3/2)*(Nat.card X : ℝ) := by
  suffices hh : ∀ n : ℕ,∀ (G : Type) [Group G] [Finite G] [Group.IsNilpotent G],
      Nat.card G=n → ∀ (X : Type) [Finite X] [Nonempty X] [MulAction G X]
        [FaithfulSMul G X] [MulAction.IsPretransitive G X],
      (¬2 ∣ Nat.card G) →
        Real.logb 2 (Nat.card G) ≤ (Real.logb 2 3/2)*(Nat.card X : ℝ) by
    exact hh (Nat.card G) G rfl X hodd
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro G _ _ _ hcard X _ _ _ _ _ hodd
    have hC : 0 ≤ Real.logb 2 3/2 :=
      div_nonneg (Real.logb_nonneg (by norm_num) (by norm_num)) (by norm_num)
    by_cases hG1 : Nat.card G=1
    · rw [hG1,Nat.cast_one,Real.logb_one]
      exact mul_nonneg hC (Nat.cast_nonneg _)
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
      exact CFSGOddPermutationDensity.pGroup_log_order_le hp3 (X := X) hGp
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
      have hleft := CFSGOddPermutationDensity.pGroup_log_order_le hp3 (X := A) hPp
      have hright := ih (Nat.card O) hOlt O rfl B hOodd
      have hpr : (Nat.card A : ℝ)*(Nat.card B : ℝ)=Nat.card X := by exact_mod_cast hprod
      have haR : (2 : ℝ) ≤ Nat.card A := by exact_mod_cast (show 2 ≤ Nat.card A by omega)
      have hbR : (2 : ℝ) ≤ Nat.card B := by exact_mod_cast (show 2 ≤ Nat.card B by omega)
      have hsum : (Nat.card A : ℝ)+(Nat.card B : ℝ) ≤ Nat.card X := by
        nlinarith [mul_nonneg (sub_nonneg.mpr haR) (sub_nonneg.mpr hbR)]
      rw [hecard,Nat.cast_mul,Real.logb_mul
        (show (Nat.card P : ℝ)≠0 by exact_mod_cast (Nat.card_pos (α := P)).ne')
        (show (Nat.card O : ℝ)≠0 by exact_mod_cast (Nat.card_pos (α := O)).ne')]
      calc
        _ ≤ (Real.logb 2 3/2)*(Nat.card A : ℝ)+(Real.logb 2 3/2)*(Nat.card B : ℝ) :=
          add_le_add hleft hright
        _ = (Real.logb 2 3/2)*((Nat.card A : ℝ)+(Nat.card B : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC

end SymmetricSubgroupAsymptotics.CFSGOddNilpotentOrderDensity
