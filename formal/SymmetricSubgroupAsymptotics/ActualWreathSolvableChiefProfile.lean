import SymmetricSubgroupAsymptotics.ActualWreathChiefOrderDivisibility
import SymmetricSubgroupAsymptotics.MinimalNormalSimpleQuotients
import Mathlib.GroupTheory.Solvable

/-! A solvable ACTUAL local component has no nonabelian charge on the
same finite chief trace. The constructed divisible profile retains each
literal elementary prime, dimension and induced capacity. Solvability
is transported to each genuine quotient; no order-compatible numerical
profile is substituted for the trace. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathSolvableChiefProfile
open PermutationalWreathProduct ActualWreathCharacteristicChiefProfile
open ActualWreathChiefOrderDivisibility

private theorem minimalNormal_abelian {A : Type} [Group A] [Finite A] [IsSolvable A]
    (N : Subgroup A) (hN : IsMinimalNormalSubgroup N) : IsMulCommutative N := by
  letI : N.Normal := hN.1
  letI : Nontrivial N := N.nontrivial_iff_ne_bot.mpr hN.2.1
  by_contra hc
  letI : Group.IsPerfect N := nonabelian_minimal_normal_perfect N
    (fun K hK hKN => by
      by_cases hbot : K = ⊥
      · exact Or.inl hbot
      · exact Or.inr (hN.2.2 K hK hbot hKN)) hc
  exact (ne_of_lt (IsSolvable.commutator_lt_top_of_nontrivial N))
    Group.IsPerfect.commutator_eq_top

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem divisible_profile_of_chiefCost
    {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) : IsSolvable S.D →
    ∃ P : DivisibleProfile (Fintype.card I) n (Nat.card S.D), P.simpleRank = 0 := by
  induction h with
  | terminal S hD =>
      intro _
      refine ⟨{
        charges := []
        simpleRank := 0
        total := by simp
        order_bound := ?_
        elementary_order_dvd := by simp },rfl⟩
      simpa only [List.map_nil,List.prod_nil,pow_zero,one_mul] using
        (Nat.card_pos (α := S.D))
  | vanishing S D' phi hphi hmin hz n next ih =>
      intro hsolv
      letI : IsSolvable S.D := hsolv
      letI : IsSolvable D' := solvable_of_surjective (f := phi) hphi
      have hnext : IsSolvable (S.quotient D' phi hphi).D := by
        change IsSolvable D'
        infer_instance
      obtain ⟨P,hzero⟩ := ih hnext
      exact ⟨{
        charges := P.charges
        simpleRank := P.simpleRank
        total := P.total
        order_bound := P.order_bound.trans (Nat.card_le_card_of_surjective phi hphi)
        elementary_order_dvd :=
          P.elementary_order_dvd.trans (Subgroup.card_dvd_of_surjective phi hphi) },hzero⟩
  | elementary S D' phi hphi hmin C n next ih =>
      intro hsolv
      letI : IsSolvable S.D := hsolv
      letI : IsSolvable D' := solvable_of_surjective (f := phi) hphi
      have hnext : IsSolvable (S.quotient D' phi hphi).D := by
        change IsSolvable D'
        infer_instance
      obtain ⟨P,hzero⟩ := ih hnext
      refine ⟨{
        charges := actualCharge S phi C i hI :: P.charges
        simpleRank := P.simpleRank
        total := ?_
        order_bound := ?_
        elementary_order_dvd := ?_ },hzero⟩
      · change ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i + n =
          (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i +
            (P.charges.map (·.capacity)).sum) + P.simpleRank
        exact (congrArg
          (Nat.add (ActualWreathElementaryOrdinaryStep.layerCapacity S phi C i))
          P.total).trans (Nat.add_assoc _ _ _).symm
      · change (C.p ^ Module.finrank (ZMod C.p) C.V *
            (P.charges.map (fun c => c.p ^ c.dimension)).prod) *
          2 ^ P.simpleRank ≤ Nat.card S.D
        calc
          _ = C.p ^ Module.finrank (ZMod C.p) C.V *
              ((P.charges.map (fun c => c.p ^ c.dimension)).prod * 2 ^ P.simpleRank) :=
            Nat.mul_assoc _ _ _
          _ ≤ C.p ^ Module.finrank (ZMod C.p) C.V * Nat.card D' :=
            Nat.mul_le_mul_left _ P.order_bound
          _ = Nat.card phi.ker * Nat.card D' := by
            rw [ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C]
          _ = Nat.card S.D :=
            ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi
      · change C.p ^ Module.finrank (ZMod C.p) C.V *
          (P.charges.map (fun c => c.p ^ c.dimension)).prod ∣ Nat.card S.D
        have hd := Nat.mul_dvd_mul (dvd_refl (Nat.card phi.ker)) P.elementary_order_dvd
        change Nat.card phi.ker * (P.charges.map (fun c => c.p ^ c.dimension)).prod ∣
          Nat.card phi.ker * Nat.card D' at hd
        rw [ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi,
          ActualWreathChiefHalfOrderBudget.elementary_kernel_card phi C] at hd
        exact hd
  | nonabelian S D' phi hphi hmin hnc hne C j n next ih =>
      intro hsolv
      letI : IsSolvable S.D := hsolv
      exact False.elim (hnc (minimalNormal_abelian phi.ker hmin))

theorem exists_divisible_profile (S : ActualWreathCompressionState Q I)
    [IsSolvable S.D] (i : I) (hI : 2 ≤ Fintype.card I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      ∃ P : DivisibleProfile (Fintype.card I) n (Nat.card S.D), P.simpleRank = 0 := by
  obtain ⟨n,hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n,hn,divisible_profile_of_chiefCost hn hI inferInstance⟩

end SymmetricSubgroupAsymptotics.ActualWreathSolvableChiefProfile
