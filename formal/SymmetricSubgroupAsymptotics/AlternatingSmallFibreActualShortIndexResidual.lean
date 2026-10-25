import SymmetricSubgroupAsymptotics.AlternatingMultiFactorAllDegreeSmallFibreSubnormalGap
import SymmetricSubgroupAsymptotics.AlternatingSingleFactorFarIndexSmallFibreSubnormalGap
import SymmetricSubgroupAsymptotics.AlternatingSingleFactorNaturalBinarySubnormalGap

/-! The alternating small-fibre gap leaves an explicit interval in the
SAME actual proper index. All multiplicities >=2 and all far indices
are discharged. Natural binary actions of degree >=10 are recognized
before their gap is applied. No stronger index gap is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingSmallFibreActualShortIndexResidual
open PrimitiveSocleRawStructure OriginalBlockClassBound

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω] [MulAction.IsPretransitive A X]

theorem subnormal_class_cube_gap_or_actual_short_index
    (b : Ω → X) (hb : ∀ (g : A) (ω : Ω), b (g • ω)=g • b ω)
    (c : ℕ) (hc : c=2 ∨ c=3) (hsize : ∀ x, Nat.card (originalBlockFibre b x)=c)
    (D : NonaffineData (Top (A := A) (X := X)) X)
    (m : ℕ) (hm : 5 ≤ m) (e : D.Simple ≃* alternatingGroup (Fin m))
    (K : Subgroup D.Simple) (hK : K ≠ ⊤)
    (hdegree : Nat.card X=K.index^D.factorCount)
    (H : Subgroup A) (hH : H.IsSubnormal) :
    Nat.card (ConjClasses H)^3 ≤ 5^(Nat.card Ω-2) ∨
      (D.factorCount=1 ∧ m ≤ K.index ∧ K.index < 2*m+2 ∧
        (c=2 → K.index ≠ m ∨ m ≤ 9)) := by
  by_cases hk2 : 2 ≤ D.factorCount
  · exact Or.inl
      (AlternatingMultiFactorAllDegreeSmallFibreSubnormalGap.subnormal_class_cube_gap
        b hb c hc hsize D m hm e hk2 K hK hdegree H hH)
  have hk1 : D.factorCount=1 := by have hp := D.factorCount_pos; omega
  have hd : Nat.card X=K.index := by simpa only [hk1,pow_one] using hdegree
  have hmin := (CFSGReduction.leastProperIndex_of_mulEquiv e.symm m
    (CFSGAlternatingMinimumIndex.leastProperIndex_degree m hm)).2 K hK
  by_cases hfar : 2*m+2 ≤ Nat.card X
  · exact Or.inl
      (AlternatingSingleFactorFarIndexSmallFibreSubnormalGap.subnormal_class_cube_gap
        b hb c hc hsize D m hm e hk1 hfar H hH)
  by_cases hnatural : c=2 ∧ K.index=m ∧ 10 ≤ m
  · obtain ⟨hc2,hindex,hm10⟩ := hnatural
    have hnat : Nat.card X=m := hd.trans hindex
    letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    let x₀ : X := Classical.choice inferInstance
    have htwo : Nat.card (originalBlockFibre b x₀)=2 := (hsize x₀).trans hc2
    exact Or.inl
      (AlternatingSingleFactorNaturalBinarySubnormalGap.subnormal_class_cube_gap
        b hb x₀ htwo D m hm10 e hk1 hnat H hH)
  · refine Or.inr ⟨hk1,hmin,by omega,?_⟩
    intro hc2
    by_cases heq : K.index=m
    · have hnot : ¬ 10 ≤ m := fun hm10 => hnatural ⟨hc2,heq,hm10⟩
      exact Or.inr (by omega)
    · exact Or.inl heq

end SymmetricSubgroupAsymptotics.AlternatingSmallFibreActualShortIndexResidual
