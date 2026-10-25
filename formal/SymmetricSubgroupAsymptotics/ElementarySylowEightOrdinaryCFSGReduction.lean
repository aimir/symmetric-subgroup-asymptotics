import SymmetricSubgroupAsymptotics.ElementarySylowEightBinaryBlockOrdinary
import SymmetricSubgroupAsymptotics.ElementarySylowEightTwoBlockOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveSoclePairedDegreeEightOrdinary
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeEightSubnormalOrdinaryGenerators
import SymmetricSubgroupAsymptotics.PrimitiveSocleElevenPointTitsExclusion

/-! An actual transitive eight-point group with elementary Sylow two is
paid by three ordinary generators, except for a literal primitive
sporadic source of rank greater than three. This residual retains the
SAME original source and Sylow subgroup. It is NOT called a failed
half-degree action: rank four at degree eight satisfies the half bound. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.ElementarySylowEightOrdinaryCFSGReduction
open PrimitiveSocleRawStructure PrimitiveSocleLargeOneFactorOrdinaryCFSGReduction

variable (J : Subgroup (Equiv.Perm (Fin 8)))
    [MulAction.IsPretransitive J (Fin 8)]

structure PrimitiveSporadicObstruction (P : Sylow 2 J) where
  elementary : ∀ g : P, g^2 = 1
  not_sixteen : ¬16 ∣ Nat.card J
  primitive : MulAction.IsPreprimitive J (Fin 8)
  failed_three : 3 < MarkedC4.genRank J
  socle : NonaffineData J (Fin 8)
  sporadic : CFSG.Sporadic
  equiv : socle.Simple ≃* sporadic.Model

theorem genRank_le_three_or_actual_sporadic (hCFSG : CFSG.CFSGClassification)
    (P : Sylow 2 J) (hel : ∀ g : P, g^2 = 1) :
    MarkedC4.genRank J ≤ 3 ∨ Nonempty (PrimitiveSporadicObstruction J P) := by
  by_cases hpaid : MarkedC4.genRank J ≤ 3
  · exact Or.inl hpaid
  have hnot16 : ¬16 ∣ Nat.card J :=
    ElementarySylowTransitiveOrderObstruction.sixteen_not_dvd_card_of_degree_eight
      (X := Fin 8) P hel (by simp only [Nat.card_fin])
  by_cases hprimitive : MulAction.IsPreprimitive J (Fin 8)
  · letI : MulAction.IsPreprimitive J (Fin 8) := hprimitive
    obtain ⟨D⟩ := publishedONanScottStructure J (Fin 8)
    cases D with
    | inr A =>
        have hh := A.subnormal_genRank_le_three_of_degreeEight hprimitive (0 : Fin 8)
          (by simp only [Nat.card_fin]) ⊤ (by exact Subgroup.Normal.isSubnormal inferInstance)
        rw [CoprimeNilpotentProductGenerators.genRank_mulEquiv
          (Subgroup.topEquiv : (⊤ : Subgroup J) ≃* J)] at hh
        exact Or.inl hh
    | inl D =>
        rcases PrimitiveSoclePairedDegreeEightOrdinary.genRank_le_three_or_actual_remaining_model
          D hCFSG (by simp only [Nat.card_fin]) hnot16 with hh | ⟨j,hj,⟨e⟩⟩
        · exact Or.inl hh
        · cases j <;> try exact hj.elim
          · exact (PrimitiveSocleElevenPointTitsExclusion.not_tits_of_degree_le_eleven
              D (by simp only [Nat.card_fin]; decide) e).elim
          · rename_i s
            exact Or.inr ⟨⟨hel,hnot16,hprimitive,by omega,D,s,e⟩⟩
  · obtain ⟨block⟩ := originalMinimalBlock_nonempty (A := J) (0 : Fin 8) hprimitive
    letI : Fintype block.Points := Fintype.ofFinite _
    have hprod : Nat.card block.Fibre*Nat.card block.Points = 8 := by
      simpa only [Nat.card_fin] using block.degree_product
    obtain ⟨hr,ht⟩ := block.degrees_ge_two
    have hr4 : Nat.card block.Fibre ≤ 4 := by nlinarith only [hprod,ht]
    have hcases : Nat.card block.Fibre = 2 ∨ Nat.card block.Fibre = 4 := by
      have hthree : Nat.card block.Fibre ≠ 3 := by intro h; rw [h] at hprod; omega
      omega
    rcases hcases with h2 | h4
    · exact Or.inl (ElementarySylowEightBinaryBlockOrdinary.genRank_le_three J block P hel h2)
    · exact Or.inl (ElementarySylowEightTwoBlockOrdinary.genRank_le_three J block P hel h4)

end SymmetricSubgroupAsymptotics.ElementarySylowEightOrdinaryCFSGReduction
