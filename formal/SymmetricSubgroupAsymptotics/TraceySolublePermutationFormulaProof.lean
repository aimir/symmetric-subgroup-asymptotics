import SymmetricSubgroupAsymptotics.SolubleInducedBinomialCapacity
import SymmetricSubgroupAsymptotics.InducedGenerationCoprimeSylow
import SymmetricSubgroupAsymptotics.OddHallOrbitPrice
import SymmetricSubgroupAsymptotics.SolubleOddHall
import SymmetricSubgroupAsymptotics.PermutationStabilizerInduced
import SymmetricSubgroupAsymptotics.TraceySolublePermutationFormulaRaw

/-! The exact soluble permutation formula follows from two independently
proved uniform capacities on the same original module: the actual
mixed-prime grid and the actual odd Hall subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

/-- This proves the complete raw permutation consumer, not the stronger
arbitrary-local-module per-soluble-orbit input. -/
theorem traceySolublePermutationFormulaRawInput_proved : TraceySolublePermutationFormulaRawInput := by
  intro G X _ _ _ _ _ _
  by_cases hx0 : Nat.card X=0
  · refine ⟨0,?_,?_⟩
    · rw [hx0]
      simp [TraceyBinarySolubleFormulaBounds,traceyBinaryK]
    · simpa only [hx0] using
        (PermutationStabilizerInduced.uniform_card (k := ZMod 2) (G := G) (X := X))
  · obtain ⟨x⟩ := (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero hx0)).1
    let H := MulAction.stabilizer G x
    let rho := Representation.trivial (ZMod 2) H (ZMod 2)
    obtain ⟨w,hw,hBin⟩ := soluble_induced_binomial_capacity H rho
    simp only [Module.finrank_self,one_mul] at hBin
    obtain ⟨P,hP⟩ := exists_isTwoComplement_of_isSolvable (G := G)
    let Q := DoubleCoset.Quotient (H : Set G) (P : Set G)
    letI : Finite Q := Finite.of_injective (inducedDoubleCosetOrbitEquiv H P)
      (inducedDoubleCosetOrbitEquiv H P).injective
    letI : Fintype Q := Fintype.ofFinite _
    letI : NeZero (Nat.card P : ZMod 2) := ⟨oddHall_order_cast_ne_zero P hP⟩
    let b := Fintype.card Q
    have hHall : UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho) b := by
      simpa only [Module.finrank_self,mul_one] using induced_coprime_subgroup_uniform H P rho
    have hb : b≤ordProj[2] H.index := oddHall_doubleCoset_count H P hP
    have hi : H.index=Nat.card X := MulAction.index_stabilizer_of_transitive G x
    let d := min w b
    have hformula : TraceyBinarySolubleFormulaBounds (Nat.card X) d := by
      constructor
      · rw [←hi]
        exact (min_le_right w b).trans hb
      · rw [←hi]
        exact (Nat.mul_le_mul_left _ (min_le_left w b)).trans hw
    have hInd : UniformSubrepresentationGeneratorBound (Representation.ind H.subtype rho) d := by
      by_cases hwb : w≤b
      · simpa only [d,Nat.min_eq_left hwb] using hBin
      · simpa only [d,Nat.min_eq_right (Nat.le_of_lt (lt_of_not_ge hwb))] using hHall
    exact ⟨d,hformula,hInd.of_injective (PermutationStabilizerInduced.toInduced x)
      (PermutationStabilizerInduced.toInduced_injective x)⟩

end SymmetricSubgroupAsymptotics
