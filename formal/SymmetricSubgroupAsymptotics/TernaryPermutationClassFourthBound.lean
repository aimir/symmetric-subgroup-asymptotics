import SymmetricSubgroupAsymptotics.PrimeCyclePointBlocks
import SymmetricSubgroupAsymptotics.LargePrimePermutationClassFourthBound

/-! The actual ternary permutation class bound by a prime-index original
block quotient and its commuting-pair estimate. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.TernaryPermutationClassFourthBound
open PermutationCharacterRankSplit PrimeCyclePointBlocks
local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

private theorem sylow_order_bound
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 3 G) :
    Nat.card G ≤ 3 ^ ((Nat.factorial (Nat.card X)).factorization 3) := by
  let f : G →* Equiv.Perm X := MulAction.toPermHom G X
  let e : G ≃* f.range := MonoidHom.ofInjective
    (show Function.Injective f from MulAction.toPerm_injective)
  obtain ⟨P,hP⟩ := (hG.of_equiv e).exists_le_sylow
  calc
    Nat.card G = Nat.card f.range := Nat.card_congr e.toEquiv
    _ ≤ Nat.card P := Nat.card_le_card_of_injective (Subgroup.inclusion hP)
      (Subgroup.inclusion_injective hP)
    _ = _ := by rw [P.card_eq_multiplicity,Nat.card_perm]

private theorem small_bound
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 3 G)
    (hsmall : Nat.card X ≤ 3) :
    Nat.card (ConjClasses G)^4 ≤ 5^Nat.card X := by
  have hc := Nat.card_le_card_of_surjective (@ConjClasses.mk G _) ConjClasses.mk_surjective
  have h := hc.trans (sylow_order_bound G X hG)
  generalize hn : Nat.card X = n at *
  apply (Nat.pow_le_pow_left h 4).trans
  interval_cases n <;> norm_num <;> decide +kernel

private theorem ternary_factorial_valuation (r : ℕ) :
    2 * (Nat.factorial (3^r)).factorization 3 + 1 = 3^r := by
  induction r with
  | zero => norm_num
  | succ r ih =>
    rw [pow_succ',Nat.factorization_factorial_mul Nat.prime_three]
    nlinarith

private theorem transitive_step
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] [MulAction.IsPretransitive G X]
    (hG : IsPGroup 3 G) (hlarge : 3 < Nat.card X)
    (ih : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
      [MulAction H Y] [FaithfulSMul H Y], IsPGroup 3 H → Nat.card Y < Nat.card X →
        Nat.card (ConjClasses H)^4 ≤ 5^Nat.card Y) :
    Nat.card (ConjClasses G)^4 ≤ 5^Nat.card X := by
  letI : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card X)).1
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨s⟩ := pGroup_primeIndexSubgroupChain_exists hG
    (MulAction.stabilizer G x₀) ⊤ le_top
  have hdegree : Nat.card X = 3^s.length := by
    simpa only [Subgroup.relIndex_top_right,
      MulAction.index_stabilizer_of_transitive G x₀] using s.relIndex
  have hk : 1 < s.length := by
    by_contra h
    have hp := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : s.length ≤ 1)
    rw [← hdegree] at hp
    norm_num at hp
    omega
  let r := s.length - 1
  let m := 3^r
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hdegree' : Nat.card X = 3^(r+1) := by
    simpa only [show r+1=s.length by dsimp [r]; omega] using hdegree
  have hdeg : Nat.card X = 3*m := by rw [hdegree',pow_succ]; dsimp [m]; ring
  have hm : 3 ≤ m := by
    dsimp [m]
    exact Nat.pow_le_pow_right (by decide : 0 < 3) hr
  obtain ⟨D⟩ := primePowerPointBlock_nonempty x₀ 3 r hG (by
    rw [hdegree']
    exact Nat.pow_lt_pow_right (by decide : 1 < 3) (by omega))
  let K := D.subgroup
  letI : K.Normal := normal_of_prime_index D hG (subgroup_index D hdegree')
  let S := selected D
  have hS : Nat.card S=m := selected_card D
  have hC : Nat.card ↥(Sᶜ)=2*m := by
    simpa only [show 3-1=2 by decide] using complement_card D hdegree'
  let N := Kernel S
  let H := Image S
  letI : FaithfulSMul N ↥(Sᶜ) := kernel_complement_faithful S
  have hN : Nat.card (ConjClasses N)^4 ≤ 5^(2*m) := by
    simpa only [hC] using ih N ↥(Sᶜ) (kernel_isPGroup S 3 (hG.to_subgroup K))
      (by rw [hC,hdeg]; omega)
  have hH : Nat.card (ConjClasses H)^4 ≤ 5^m := by
    simpa only [hS] using ih H S (image_isPGroup S 3 (hG.to_subgroup K))
      (by rw [hS,hdeg]; omega)
  let A := Nat.card (ConjClasses N) * Nat.card (ConjClasses H)
  have hA : A^4 ≤ 5^Nat.card X := by
    calc
      A^4 = Nat.card (ConjClasses N)^4 * Nat.card (ConjClasses H)^4 := mul_pow _ _ _
      _ ≤ 5^(2*m) * 5^m := Nat.mul_le_mul hN hH
      _ = _ := by rw [←pow_add,hdeg]; congr 1; omega
  let v := (Nat.factorial m).factorization 3
  have hv : 2*v+1=m := ternary_factorial_valuation r
  have hvpos : 1 ≤ v := by omega
  have horder : Nat.card H ≤ 3^v := by
    simpa only [hS] using sylow_order_bound H S (image_isPGroup S 3 (hG.to_subgroup K))
  have hfour : 4 ≤ 3^(v+1) := by
    have he := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 2 ≤ v+1)
    norm_num at he
    omega
  have hcost : (4 * Nat.card H)^4 ≤ 5^Nat.card X := by
    have hfirst : 4*Nat.card H ≤ 3^m := by
      calc
        _ ≤ 4*3^v := Nat.mul_le_mul_left _ horder
        _ ≤ 3^(v+1)*3^v := Nat.mul_le_mul_right _ hfour
        _ = 3^m := by rw [←pow_add]; congr 1; omega
    calc
      _ ≤ (3^m)^4 := Nat.pow_le_pow_left hfirst 4
      _ = (3^4)^m := by simp only [←pow_mul,Nat.mul_comm]
      _ ≤ (5^3)^m := Nat.pow_le_pow_left (by decide : (3 : ℕ)^4 ≤ 5^3) m
      _ = _ := by rw [←pow_mul,hdeg]
  have hcount := CyclicBlockCentralizerProjection.index_mul_class_card_le
    K S (reach D (subgroup_index D hdegree'))
  have hi : K.index=3 := subgroup_index D hdegree'
  rw [hi] at hcount
  change 3*Nat.card (ConjClasses G)+Nat.card H ≤ A+3^2*Nat.card H at hcount
  by_cases ha : A ≤ 4*Nat.card H
  · exact (Nat.pow_le_pow_left (by omega : Nat.card (ConjClasses G) ≤ 4*Nat.card H) 4).trans hcost
  · exact (Nat.pow_le_pow_left (by omega : Nat.card (ConjClasses G) ≤ A) 4).trans hA

/-- All original finite faithful ternary actions, with no literature input. -/
theorem class_card_pow_four_le
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 3 G) :
    Nat.card (ConjClasses G)^4 ≤ 5^Nat.card X := by
  classical
  suffices hh : ∀ n (G X : Type) [Group G] [Finite G] [Finite X]
      [MulAction G X] [FaithfulSMul G X], IsPGroup 3 G → Nat.card X=n →
      Nat.card (ConjClasses G)^4 ≤ 5^Nat.card X from hh _ G X hG rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G X _ _ _ _ _ hG hn
    have hsmaller : ∀ (H Y : Type) [Group H] [Finite H] [Finite Y]
        [MulAction H Y] [FaithfulSMul H Y], IsPGroup 3 H → Nat.card Y < Nat.card X →
        Nat.card (ConjClasses H)^4 ≤ 5^Nat.card Y := by
      intro H Y _ _ _ _ _ hH hlt
      exact ih (Nat.card Y) (by omega) H Y hH rfl
    by_cases hsmall : Nat.card X ≤ 3
    · exact small_bound G X hG hsmall
    by_cases ht : MulAction.IsPretransitive G X
    · letI := ht
      exact transitive_step G X hG (by omega) hsmaller
    · obtain ⟨S,hS,hC⟩ := exists_nonempty_proper_invariant ht
      letI : FaithfulSMul (Kernel S) ↥(Sᶜ) := kernel_complement_faithful S
      have hlt := degrees_lt S hS hC
      have hI := hsmaller (Image S) S (image_isPGroup S 3 hG) hlt.1
      have hK := hsmaller (Kernel S) ↥(Sᶜ) (kernel_isPGroup S 3 hG) hlt.2
      have hsplit := conjugacyClass_card_le_normal_mul_quotient (Kernel S)
      have hquot := conjugacyClass_card_congr
        (QuotientGroup.quotientKerEquivOfSurjective (projection S) (projection_surjective S))
      rw [hquot] at hsplit
      calc
        _ ≤ (Nat.card (ConjClasses (Kernel S))*Nat.card (ConjClasses (Image S)))^4 :=
          Nat.pow_le_pow_left hsplit 4
        _ = Nat.card (ConjClasses (Kernel S))^4*Nat.card (ConjClasses (Image S))^4 := mul_pow _ _ _
        _ ≤ 5^Nat.card ↥(Sᶜ)*5^Nat.card S := Nat.mul_le_mul hK hI
        _ = _ := by rw [←pow_add]; congr 1; have h := card_split S; omega

end SymmetricSubgroupAsymptotics.TernaryPermutationClassFourthBound
