import SymmetricSubgroupAsymptotics.ActualWreathCharacteristicChiefProfile

/-! The elementary prime-power order product divides the ACTUAL local
component order along the same finite chief trace. This strengthens the
existing order inequality without modifying its checked profile source. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.ActualWreathChiefOrderDivisibility
open PermutationalWreathProduct ActualWreathCharacteristicChiefProfile

structure DivisibleProfile (t cost localOrder : ℕ) extends Profile t cost localOrder where
  elementary_order_dvd : (charges.map (fun c => c.p ^ c.dimension)).prod ∣ localOrder

variable {Q I : Type} [Group Q] [Fintype I] [Nonempty I]
    [MulAction Q I] [FaithfulSMul Q I]

theorem divisible_profile_of_chiefCost
    {i : I} {S : ActualWreathCompressionState Q I} {n : ℕ}
    (h : ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n)
    (hI : 2 ≤ Fintype.card I) :
    Nonempty (DivisibleProfile (Fintype.card I) n (Nat.card S.D)) := by
  induction h with
  | terminal S hD =>
      refine ⟨{
        charges := []
        simpleRank := 0
        total := by simp
        order_bound := ?_
        elementary_order_dvd := by simp }⟩
      simpa only [List.map_nil, List.prod_nil, pow_zero, one_mul] using
        (Nat.card_pos (α := S.D))
  | vanishing S D' phi hphi hmin hz n next ih =>
      obtain ⟨P⟩ := ih
      exact ⟨{
        charges := P.charges
        simpleRank := P.simpleRank
        total := P.total
        order_bound := P.order_bound.trans (Nat.card_le_card_of_surjective phi hphi)
        elementary_order_dvd :=
          P.elementary_order_dvd.trans (Subgroup.card_dvd_of_surjective phi hphi) }⟩
  | elementary S D' phi hphi hmin C n next ih =>
      obtain ⟨P⟩ := ih
      refine ⟨{
        charges := actualCharge S phi C i hI :: P.charges
        simpleRank := P.simpleRank
        total := ?_
        order_bound := ?_
        elementary_order_dvd := ?_ }⟩
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
      obtain ⟨P⟩ := ih
      refine ⟨{
        charges := P.charges
        simpleRank := MarkedC4.genRank (C.factor j) + P.simpleRank
        total := ?_
        order_bound := ?_
        elementary_order_dvd :=
          P.elementary_order_dvd.trans (Subgroup.card_dvd_of_surjective phi hphi) }⟩
      · have ht := P.total
        omega
      · calc
          _ = 2 ^ MarkedC4.genRank (C.factor j) *
              ((P.charges.map (fun c => c.p ^ c.dimension)).prod * 2 ^ P.simpleRank) := by
            rw [pow_add]
            ac_rfl
          _ ≤ Nat.card phi.ker * Nat.card D' :=
            Nat.mul_le_mul
              (ActualWreathChiefFactorOrder.two_pow_factor_genRank_le_local_kernel
                S.rho phi S.rho_injective C j) P.order_bound
          _ = Nat.card S.D :=
            ActualWreathChiefHalfOrderBudget.card_kernel_mul_card_of_surjective phi hphi

theorem exists_divisible_profile (S : ActualWreathCompressionState Q I)
    (i : I) (hI : 2 ≤ Fintype.card I) :
    ∃ n : ℕ, ActualWreathOrdinaryChiefRecurrence.ChiefCost i S n ∧
      Nonempty (DivisibleProfile (Fintype.card I) n (Nat.card S.D)) := by
  obtain ⟨n, hn⟩ := ActualWreathOrdinaryChiefRecurrence.exists_chiefCost i S
  exact ⟨n, hn, divisible_profile_of_chiefCost hn hI⟩

end SymmetricSubgroupAsymptotics.ActualWreathChiefOrderDivisibility
