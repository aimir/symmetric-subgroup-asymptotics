import SymmetricSubgroupAsymptotics.AlternatingSmallFibreActualShortIndexResidual
import SymmetricSubgroupAsymptotics.OriginalTernaryBlockSubnormalClassGap

/-! The same actual short-index residual, refined by checked natural
ternary fusion. Both binary and ternary natural equalities are excluded
above their proved thresholds. The remaining interval is explicit;
no nonnatural-index gap is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.AlternatingSmallFibreRefinedShortIndexResidual
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
        (c=2 → K.index ≠ m ∨ m ≤ 9) ∧
        (c=3 → K.index ≠ m ∨ m ≤ 27)) := by
  rcases AlternatingSmallFibreActualShortIndexResidual.subnormal_class_cube_gap_or_actual_short_index
    b hb c hc hsize D m hm e K hK hdegree H hH with h | ⟨hk1,hmin,hmax,hbinary⟩
  · exact Or.inl h
  · have hd : Nat.card X=K.index := by simpa only [hk1,pow_one] using hdegree
    by_cases hnatural : c=3 ∧ K.index=m ∧ 28 ≤ m
    · obtain ⟨hc3,hindex,hm28⟩ := hnatural
      have hnat : Nat.card X=m := hd.trans hindex
      letI : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      let x₀ : X := Classical.choice inferInstance
      have hthree : Nat.card (originalBlockFibre b x₀)=3 := (hsize x₀).trans hc3
      exact Or.inl
        (OriginalTernaryBlockSubnormalClassGap.subnormal_class_cube_gap_of_single_natural_factor
          b hb x₀ hthree D m hm28 e hk1 hnat H hH)
    · refine Or.inr ⟨hk1,hmin,hmax,hbinary,?_⟩
      intro hc3
      by_cases heq : K.index=m
      · have hnot : ¬ 28 ≤ m := fun hm28 => hnatural ⟨hc3,heq,hm28⟩
        exact Or.inr (by omega)
      · exact Or.inl heq

end SymmetricSubgroupAsymptotics.AlternatingSmallFibreRefinedShortIndexResidual
