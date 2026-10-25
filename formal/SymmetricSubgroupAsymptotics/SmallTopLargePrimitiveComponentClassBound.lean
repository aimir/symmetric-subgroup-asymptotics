import SymmetricSubgroupAsymptotics.LargePrimitiveSubnormalClassGap
import SymmetricSubgroupAsymptotics.SubnormalCoordinateClassPowerBound
import SymmetricSubgroupAsymptotics.SubnormalPermutationBlockClassReduction

/-! A literal top of size two or three over large primitive components.
Only the actual coordinate images and successive normal kernels are
used. Component primitivity is an explicit hypothesis; it is not
inferred from an unrelated maximal block choice. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound
open OriginalBlockClassBound SubnormalPermutationBlockClassReduction
open SubnormalCoordinateClassPowerBound LargeTopFiniteModelResidual
open PrimitiveSocleRawStructure

variable {A Ω X : Type} [Group A] [MulAction A Ω] [MulAction A X]
    [Finite A] [Finite Ω] [Finite X] [FaithfulSMul A Ω]

theorem class_cube_le_of_subnormal_component_gaps (b : Ω → X)
    (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (a : ℕ) (ha : 2 ≤ a) (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = a)
    (hgap : ∀ x (L : Subgroup (originalBlockComponent b hb x)), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (a - 2)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) := by
  letI : Fintype X := Fintype.ofFinite _
  have hker := class_power_le_finite_subnormal_coordinate_bounds 3
    (fun x => originalBlockComponent b hb x) (fun _ => 5 ^ (a - 2))
    (Kernel (A := A) (X := X)) (componentCoordinate b hb)
    (fun x => (componentCoordinate_range_normal b hb x).isSubnormal) hgap
    (componentCoordinates_injective b hb)
  have hker' : Nat.card (ConjClasses (Kernel (A := A) (X := X))) ^ 3 ≤
      5 ^ ((a - 2) * Nat.card X) := by
    simpa only [Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card,← pow_mul] using hker
  have ht : Nat.card (ConjClasses (Top (A := A) (X := X))) ≤ Nat.card X := by
    rcases hblocks with h | h
    · rw [h]
      exact SmallPermutationClassBudgets.subgroup_class_card_le_two h.le _
    · rw [h]
      exact SmallPermutationClassBudgets.subgroup_class_card_le_three h.le _
  have htop : Nat.card (ConjClasses (Top (A := A) (X := X))) ^ 3 ≤
      5 ^ (2 * Nat.card X - 1) := by
    apply (Nat.pow_le_pow_left ht 3).trans
    rcases hblocks with h | h <;> rw [h] <;> decide +kernel
  have hrec := conjugacyClass_card_le_kernel_mul_range (topMap (A := A) (X := X))
  have hrec' : Nat.card (ConjClasses A) ^ 3 ≤
      Nat.card (ConjClasses (Kernel (A := A) (X := X))) ^ 3 *
        Nat.card (ConjClasses (Top (A := A) (X := X))) ^ 3 := by
    simpa only [mul_pow] using Nat.pow_le_pow_left hrec 3
  have hd := GaronziMarotiLargeBlockReduction.card_eq_blocks_mul_fibre b a hsize
  calc
    _ ≤ 5 ^ ((a - 2) * Nat.card X) * 5 ^ (2 * Nat.card X - 1) :=
      hrec'.trans (Nat.mul_le_mul hker' htop)
    _ = _ := by
      rw [← pow_add,hd]
      congr 1
      rcases hblocks with h | h <;> rw [h] <;> omega

theorem primitive_component_cube_or_actual_finite_model
    (hCFSG : CFSG.CFSGClassification)
    (b : Ω → X) (hb : ∀ (a : A) (ω : Ω), b (a • ω) = a • b ω)
    (a : ℕ) (ha : 4096 ≤ a) (hblocks : Nat.card X = 2 ∨ Nat.card X = 3)
    (hsize : ∀ x, Nat.card (originalBlockFibre b x) = a)
    (hprimitive : ∀ x, MulAction.IsPreprimitive
      (originalBlockComponent b hb x) (originalBlockFibre b x)) :
    Nat.card (ConjClasses A) ^ 3 ≤ 5 ^ (Nat.card Ω - 1) ∨
      ∃ x : X, ∃ L : Subgroup (originalBlockComponent b hb x), L.IsSubnormal ∧
        ∃ D : NonaffineData (originalBlockComponent b hb x) (originalBlockFibre b x),
          ∃ i : CFSG.Index, RemainingFiniteSimpleType i ∧ Nonempty (D.Simple ≃* i.Model) ∧
            ∃ K : Subgroup D.Simple, K ≠ ⊤ ∧ a = K.index ^ D.factorCount ∧
              K.index ^ (4 * Nat.log 2 K.index + 23) <
                Nat.card D.Simple * Nat.card (Outer D.Simple) ∧
              K.index ^ 66 < Nat.card D.Simple * Nat.card (Outer D.Simple) := by
  by_cases hall : ∀ x (L : Subgroup (originalBlockComponent b hb x)), L.IsSubnormal →
      Nat.card (ConjClasses L) ^ 3 ≤ 5 ^ (a - 2)
  · exact Or.inl (class_cube_le_of_subnormal_component_gaps b hb a (by omega) hblocks hsize hall)
  · simp only [not_forall,_root_.not_imp] at hall
    obtain ⟨x,L,hL,hnot⟩ := hall
    have hn : 4096 ≤ Nat.card (originalBlockFibre b x) := by rw [hsize]; exact ha
    rcases LargePrimitiveSubnormalClassGap.primitive_subnormal_cube_gap_or_actual_finite_model
      hCFSG (hprimitive x) hn L hL with h | ⟨D,i,hi,he,K,hK,hdegree,hlog,hbound⟩
    · exact (hnot (by simpa only [hsize] using h)).elim
    · have hd : a = K.index ^ D.factorCount := by simpa only [hsize] using hdegree
      exact Or.inr ⟨x,L,hL,D,i,hi,he,K,hK,hd,hlog,hbound⟩

end SymmetricSubgroupAsymptotics.SmallTopLargePrimitiveComponentClassBound
