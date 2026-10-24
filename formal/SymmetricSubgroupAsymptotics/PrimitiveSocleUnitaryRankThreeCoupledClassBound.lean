import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeCoupledIndex
import SymmetricSubgroupAsymptotics.CFSGUnitaryRankThreeBinaryOrderUpper
import SymmetricSubgroupAsymptotics.UnitaryRankThreeClassEquationNumerics
import SymmetricSubgroupAsymptotics.PrimitiveSocleClassicalClassEquationCapacity
import SymmetricSubgroupAsymptotics.ClassicalClassEquationSmallParameters

/-! The actual rank-three unitary index bounds pay both remaining field
orders through the shared class-equation budget. The binary order bound
uses the first isotropic-column carrier. The original model, raw factor
counts, both degree forms and subnormal subgroup are unchanged. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
open CFSGReduction CFSGTwistedAUnitaryCoordinates ClassicalClassEquationCapacity
open UnitaryRankThreeClassEquationNumerics
variable {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]

theorem NonaffineData.subnormal_class_cube_le_of_unitary_rank_three_coupled
    (D : NonaffineData G X) (q : CFSG.PrimePower) (hq : q.order=2 ∨ q.order=3)
    (e : D.Simple ≃* CFSG.Models.TwistedA 3 q)
    (H : Subgroup G) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card X-1) := by
  letI : IsSimpleGroup (CFSG.Models.TwistedA 3 q) := e.symm.isSimpleGroup
  letI : Finite (CFSG.Models.TwistedA 3 q) := Finite.of_equiv D.Simple e.toEquiv
  have hr : 2≤(3:ℕ) := by decide
  have hsmall : (3:ℕ)=2 → q.order≠2 := by omega
  have hnc : ¬IsMulCommutative (CFSG.Models.TwistedA 3 q) :=
    fun h => D.noncommutative ((isMulCommutative_congr e).mpr h)
  have he : q.exponent=1 := by
    apply exponent_eq_one_of_prime_order q
    rcases hq with hq | hq <;> rw [hq] <;> decide
  have ho : Nat.card (Outer (CFSG.Models.TwistedA 3 q)) ≤ 8 := by
    simpa only [he,Nat.mul_one] using
      (twistedA_admissible_raw_outer_order_le 3 hr q hsmall hnc)
  have hd : ∃ b N : ℕ, 3≤b ∧
      (∀ K : Subgroup (CFSG.Models.TwistedA 3 q), K≠⊤ → b≤K.index) ∧
      Nat.card (CFSG.Models.TwistedA 3 q)≤N ∧
      ((N/b+1)*8)^3≤5^(b-1) := by
    rcases hq with hq | hq
    · exact ⟨24,655360,by decide,
        fun K hK => twistedA_rankThree_binary_coupled_proper_index q hq K hK,
        twistedA_rankThree_binary_order_le q hq,binary_capacity⟩
    · refine ⟨48,3^20,by decide,
        fun K hK => twistedA_rankThree_ternary_coupled_proper_index q hq K hK,?_,
        ternary_capacity⟩
      simpa only [hq] using
        (twistedA_admissible_order_le_isometry_power 3 hr q hsmall)
  obtain ⟨b,N,hb,hi,hN,hbudget⟩ := hd
  exact D.subnormal_class_cube_le_of_model_class_equation_budget
    (CFSG.Models.TwistedA 3 q) e b N 8 hb hi hN ho
    (twistedA_admissible_leastIndex_square_lt 3 hr q hsmall) hbudget H hH

end SymmetricSubgroupAsymptotics.PrimitiveSocleRawStructure
