import SymmetricSubgroupAsymptotics.FiniteIsotypicCardBudget
import SymmetricSubgroupAsymptotics.SolubleSocleHighActionCentralizer
import SymmetricSubgroupAsymptotics.SolubleSocleSubmoduleLattice
import SymmetricSubgroupAsymptotics.AbelianSectionOmegaTransfer
import SymmetricSubgroupAsymptotics.OrdinaryGeneratorQuotientLift

/-! A bounded chief-section socle splits into a small normally generated
part and a high part with a cheaply generated centralizer quotient. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical IsMulCommutative MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open SolubleSocleConjugationModule
open MarkedC4.OrdinaryNilpotentGeneration MarkedC4.AbelianSectionSize

theorem bounded_semisimple_normal_split
    {G : Type} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    [IsMulCommutative N] [IsSemisimpleModule ℤ[G] (representation N).asModule]
    (b m : ℕ) (hb : BoundedChiefSections b G) (hm : SectionOmegaBound m G) :
    ∃ A B C : Subgroup G, A.Normal ∧ B.Normal ∧ C.Normal ∧
      A ⊔ B=N ∧ N ≤ C ∧ C ≤ Subgroup.centralizer (B : Set G) ∧
      MarkedC4.normalGen A ≤ m.sqrt ∧
      ∃ T : Finset G, T.card ≤ b.factorial*m.sqrt ∧
        Subgroup.closure (T : Set G) ⊔ C=⊤ := by
  letI : CommGroup N := { (inferInstance : Group N) with mul_comm := mul_comm }
  let M := (representation N).asModule
  letI : Finite M := Finite.of_equiv N (Additive.toMul : M ≃ N).symm
  let D : FiniteIsotypicRowData ℤ[G] M :=
    (finite_isotypic_rowData_nonempty ℤ[G] M).some
  let A := submoduleGroup N (D.lowModule m.sqrt)
  let B := submoduleGroup N (D.highModule m.sqrt)
  let C := Subgroup.centralizer (B : Set G)
  have hAB : A ⊔ B=N := by
    rw [←submoduleGroup_sup,D.low_sup_high,submoduleGroup_top]
  have hNC : N ≤ C := (Subgroup.le_centralizer N).trans
    (Subgroup.centralizer_le (submoduleGroup_le N (D.highModule m.sqrt)))
  have hA : MarkedC4.normalGen A ≤ m.sqrt :=
    normalGen_submoduleGroup_le_of_moduleGeneratedBy N _ _ (D.lowModule_generated m.sqrt)
  have hmass : omega (Nat.card M) ≤ m := by
    have h := hm N N N.subtype Subtype.val_injective (MonoidHom.id N) Function.surjective_id
    have he : Nat.card M=Nat.card N :=
      Nat.card_congr (Additive.toMul : Additive N ≃ N)
    rw [he]
    exact h
  have hhigh := D.highIndex_card_le_sqrt m hmass
  have hcard : Nat.card (G⧸C) ≤ b.factorial^m.sqrt := by
    have h0 := D.highAction_quotient_card_le m.sqrt b (fun i =>
      simple_card_le_of_boundedChiefSections N (D.simplePart i.val) (D.simple i.val) b hb)
    rw [highAction_ker_eq_centralizer N D m.sqrt] at h0
    exact h0.trans (Nat.pow_le_pow_right (Nat.factorial_pos b) hhigh)
  obtain ⟨T,hT,hgen⟩ := exists_generating_supplement_of_quotient_card_le_pow C _ _ hcard
  exact ⟨A,B,C,inferInstance,inferInstance,inferInstance,hAB,hNC,le_rfl,hA,T,hT,hgen⟩

end SymmetricSubgroupAsymptotics
