import SymmetricSubgroupAsymptotics.BinarySmallClassBaseReduction
import SymmetricSubgroupAsymptotics.BinaryMenuSmallCoverage
import SymmetricSubgroupAsymptotics.FinitePermutationConjugacyCover

/-! Actual degree-two and degree-four class bases. Complete original-action
coverage is supplied by the small finite registry. The sole nonabelian row
uses five representative labels and conjugators in its own eight original
rows, verified on the original four points. Degree eight remains separate.
-/

set_option autoImplicit false
noncomputable section
open scoped Pointwise

namespace SymmetricSubgroupAsymptotics

/-- Class counts transport through the actual ambient conjugation in an
action-coverage witness. No class-count monotonicity for subgroups is used. -/
theorem conjugacyClass_card_le_of_actionRegistryCovered
    {X I : Type*} [Finite X]
    (actions : I → Subgroup (Equiv.Perm X)) (c : ℕ)
    (hclasses : ∀ i, Nat.card (ConjClasses (actions i)) ≤ c)
    (H : Subgroup (Equiv.Perm X)) (hcovered : ActionRegistryCovered actions H) :
    Nat.card (ConjClasses H) ≤ c := by
  obtain ⟨i, g, hg⟩ := hcovered
  calc
    _ = Nat.card (ConjClasses ↥(MulAut.conj g • H)) :=
      conjugacyClass_card_congr (Subgroup.equivSMul (MulAut.conj g) H)
    _ = Nat.card (ConjClasses (actions i)) := by rw [hg]
    _ ≤ c := hclasses i

namespace BinarySmallConjugacyClassBase

private theorem class_card_le_order (G : Type*) [Group G] [Finite G] :
    Nat.card (ConjClasses G) ≤ Nat.card G :=
  Nat.card_le_card_of_surjective (@ConjClasses.mk G _) ConjClasses.mk_surjective

/-- The actual C2 closure has order two; quotienting elements by conjugacy
cannot increase that cardinality. -/
theorem class_card_le_two_2T1 :
    Nat.card (ConjClasses (Subgroup.closure
      (Set.range BinaryMenuCayley2T1.generators))) ≤ 2 := by
  have h := class_card_le_order
    (Subgroup.closure (Set.range BinaryMenuCayley2T1.generators))
  rwa [BinaryMenuCayley2T1.exact_card] at h

theorem class_card_le_four_4T1 :
    Nat.card (ConjClasses (Subgroup.closure
      (Set.range BinaryMenuCayley4T1.generators))) ≤ 4 := by
  have h := class_card_le_order
    (Subgroup.closure (Set.range BinaryMenuCayley4T1.generators))
  rwa [BinaryMenuCayley4T1.exact_card] at h

theorem class_card_le_four_4T2 :
    Nat.card (ConjClasses (Subgroup.closure
      (Set.range BinaryMenuCayley4T2.generators))) ≤ 4 := by
  have h := class_card_le_order
    (Subgroup.closure (Set.range BinaryMenuCayley4T2.generators))
  rwa [BinaryMenuCayley4T2.exact_card] at h

private def representative : Fin 5 → Fin 8 := ![7, 2, 1, 0, 3]
private def label : Fin 8 → Fin 5 := ![3, 2, 1, 4, 2, 3, 4, 0]
private def conjugator : Fin 8 → Fin 8 := ![7, 7, 7, 7, 6, 1, 1, 7]

private theorem conjugates_pointwise : ∀ (i : Fin 8) (x : Fin 4),
    finFunctionFinEquiv.symm (BinaryMenuCayley4T3.certificate.rows (conjugator i))
        (finFunctionFinEquiv.symm (BinaryMenuCayley4T3.certificate.rows i) x) =
      finFunctionFinEquiv.symm
        (BinaryMenuCayley4T3.certificate.rows (representative (label i)))
          (finFunctionFinEquiv.symm
            (BinaryMenuCayley4T3.certificate.rows (conjugator i)) x) := by
  decide +kernel

/-- All eight original D8 rows are conjugate inside that same group to
one of five labels. Only the upper class bound is asserted. -/
theorem class_card_le_five_4T3 :
    Nat.card (ConjClasses (Subgroup.closure
      (Set.range BinaryMenuCayley4T3.generators))) ≤ 5 :=
  BinaryMenuCayley4T3.certificate.permutation_conjClasses_card_le
    representative label conjugator conjugates_pointwise

private theorem original_transitive {X : Type*}
    (P : Subgroup (Equiv.Perm X)) [MulAction.IsPretransitive P X] :
    PermutationSubgroupTransitive P := by
  intro x y
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P x y
  exact ⟨g, g.property, hg⟩

/-- Every actual transitive binary action on the original two points
has at most two conjugacy classes. -/
theorem degree_two : TransitiveBinaryClassBound 2 2 := by
  intro P hP ht
  letI : MulAction.IsPretransitive P (Fin 2) := ht
  exact conjugacyClass_card_le_of_actionRegistryCovered
    (fun _ : Unit => Subgroup.closure (Set.range BinaryMenuCayley2T1.generators))
    2 (fun _ => class_card_le_two_2T1) P
    (BinaryMenuSmallCoverage.width2_complete P hP (original_transitive P))

/-- Every actual transitive binary action on the original four points
has at most five conjugacy classes. -/
theorem degree_four : TransitiveBinaryClassBound 4 5 := by
  intro P hP ht
  letI : MulAction.IsPretransitive P (Fin 4) := ht
  apply conjugacyClass_card_le_of_actionRegistryCovered
    BinaryMenuSmallCoverage.actions4 5 ?_ P
    (BinaryMenuSmallCoverage.width4_complete P hP (original_transitive P))
  intro i
  fin_cases i
  · change Nat.card (ConjClasses (Subgroup.closure
      (Set.range BinaryMenuCayley4T1.generators))) ≤ 5
    exact class_card_le_four_4T1.trans (by decide)
  · change Nat.card (ConjClasses (Subgroup.closure
      (Set.range BinaryMenuCayley4T2.generators))) ≤ 5
    exact class_card_le_four_4T2.trans (by decide)
  · change Nat.card (ConjClasses (Subgroup.closure
      (Set.range BinaryMenuCayley4T3.generators))) ≤ 5
    exact class_card_le_five_4T3

/-- The only remaining finite class input is degree eight. -/
theorem eightPointClassBase_of_degree_eight
    (h8 : TransitiveBinaryClassBound 8 25) : BinaryEightPointClassBase :=
  binaryEightPointClassBase_of_transitive_bounds degree_two degree_four h8

theorem permutationTwoGroup_class_bound_of_degree_eight
    (h8 : TransitiveBinaryClassBound 8 25)
    (G X : Type) [Group G] [Finite G] [Finite X]
    [MulAction G X] [FaithfulSMul G X] (hG : IsPGroup 2 G) :
    Nat.card (ConjClasses G) ^ 7 ≤ 5 ^ (2 * Nat.card X) :=
  permutationTwoGroup_conjugacyClass_pow_seven_le
    (eightPointClassBase_of_degree_eight h8) G X hG

end BinarySmallConjugacyClassBase
end SymmetricSubgroupAsymptotics

end
