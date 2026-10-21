import SymmetricSubgroupAsymptotics.BinaryTriangularHeadFourMinimumGenerators
import SymmetricSubgroupAsymptotics.BinaryPairTriangularShearUniformBound
import SymmetricSubgroupAsymptotics.BooleanFourAntichainFourAlternatives
import SymmetricSubgroupAsymptotics.BinaryFourQuadraticPairWidth
import SymmetricSubgroupAsymptotics.BinaryFourQuadraticSmallSupportClosure
import SymmetricSubgroupAsymptotics.BinaryBooleanFourCubicQuadraticShadow
import SymmetricSubgroupAsymptotics.BinaryTrianglePairWidth
import SymmetricSubgroupAsymptotics.BinaryPairAxisNaturalModule

/-! An original nonelementary triangular top and its actual head-four
axis give uniform natural-module generation by seven elements. Every
leading shear is lifted from the same original correlated pair kernel. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem variable_support : ∀ i : Fin 4, support (variableIndex i) = {i} := by decide
private theorem opposite_triangle_card : ∀ i : Fin 4,
    (quadraticMasks.filter (fun q => i ∉ support q)).card = 3 := by decide
private theorem opposite_triangle_covers : ∀ (i : Fin 4) (b : Fin 16),
    i ∉ support b → (support b).card ≤ 2 →
      ∃ q ∈ quadraticMasks, i ∉ support q ∧ support b ⊆ support q := by decide

variable {X : Type} [Finite X] {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin 16))

theorem uniform_generatedBy_seven_of_nonelementary_triangular_axis_head_four
    (T : BinaryTriangularPointCoordinates F.top.range (Fin 16) 4)
    (hG : IsPGroup 2 F.top.range)
    (hnon : ¬BinarySquareActionStructure.SquaresActTrivially (G := F.top.range) (X := Fin 16))
    (hhead : Module.finrank (ZMod 2)
      ((F.axisNaturalSubrepresentation F.top.ker).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) F.top.range (ZMod 2))) = 4) :
    UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
  let W := F.axisNaturalSubrepresentation F.top.ker
  let E := T.subrepresentationModuleCoordinates W
  let Actual : Fin 16 → Prop := fun a =>
    ∃ v : W.toRepresentation.asModule, FiniteRowLeadingWeight.HasLeading (E v) a
  have hdown (a b : Fin 16) (hab : support b ⊆ support a) (ha : Actual a) : Actual b := by
    obtain ⟨v, hv⟩ := ha
    obtain ⟨r, hr⟩ := T.exists_actual_module_operator_leading_subset W v a b hv hab
    exact ⟨r • v, hr⟩
  have hkernel (b : Fin 16) (hb : Actual b) : ∃ a : V,
      FiniteRowLeadingWeight.HasLeading a b ∧
        (fun x => evaluate a (T.booleanPointLabels x)) ∈ F.kernelSpace := by
    obtain ⟨v, hv⟩ := hb
    let f := (W.toRepresentation.asModuleEquiv v).val
    have he : (fun x => evaluate (E v) (T.booleanPointLabels x)) = f := by
      change (fun x => evaluate (evaluate (fun j => f (T.booleanPointLabels.symm j)))
        (T.booleanPointLabels x)) = f
      rw [evaluate_involutive]
      funext x
      rw [Equiv.symm_apply_apply]
    refine ⟨E v, hv, ?_⟩
    rw [he]
    exact F.ambientAxis_le_kernelSpace F.top.ker (W.toRepresentation.asModuleEquiv v).property
  have hquad (Q : Finset (Fin 16)) (hQ : ∀ a ∈ Q, (support a).card = 2)
      (hQc : 4 ≤ Q.card) (hQA : ∀ a ∈ Q, Actual a) :
      UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
    apply F.uniform_generatedBy_of_triangular_leading_shears T (BinaryFourQuadraticPairWidth.Allowed Q) 7
    · intro b hb
      apply hkernel
      rcases hb with hb | ⟨a, ha, he⟩
      · obtain ⟨a, ha, hab⟩ := every_small_support_covered_by_four_quadratics Q hQ hQc b hb
        exact hdown a b hab (hQA a ha)
      · have hba : b = a := BinaryBooleanFourSupportRelabel.supportEquiv.injective he
        exact hba.symm ▸ hQA a ha
    · exact BinaryFourQuadraticPairWidth.antichain_card_le_seven Q hQ hQc
  obtain ⟨v, label, hv, hlead, hinj, hcollision, hanti⟩ := T.exists_head_four_minimum_generators hG W hhead
  let L := Finset.univ.image label
  have hLc : L.card = 4 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hLA (a : Fin 16) (ha : a ∈ L) : Actual a := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact ⟨v i, (hlead i).2⟩
  have hLanti : IsAntichain (fun a b => support a ⊆ support b) (L : Set (Fin 16)) := by
    intro a ha b hb hne hab
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact hanti j i (fun he => hne (congrArg label he).symm) hab
  let A := L.image support
  have hAc : A.card = 4 := by
    calc
      A.card = (L.image support).card := rfl
      _ = L.card := Finset.card_image_of_injective L
        (show Function.Injective support from BinaryBooleanFourSupportRelabel.supportEquiv.injective)
      _ = 4 := hLc
  have hA : IsAntichain (· ⊆ ·) (A : Set (Finset (Fin 4))) := by
    intro a ha b hb hne hab
    change a ∈ L.image support at ha
    change b ∈ L.image support at hb
    obtain ⟨a0, ha0, hea⟩ := Finset.mem_image.mp ha
    obtain ⟨b0, hb0, heb⟩ := Finset.mem_image.mp hb
    apply hLanti ha0 hb0
    · intro he
      exact hne (hea.symm.trans ((congrArg support he).trans heb))
    · rw [hea, heb]
      exact hab
  have hAmem (a : Fin 16) (ha : a ∈ L) : support a ∈ A := Finset.mem_image.mpr ⟨a, ha, rfl⟩
  have hcubic (a : Fin 16) (ha : a ∈ L) (hac : (support a).card = 3)
      (hlow : ∀ b ∈ L, 2 ≤ (support b).card) :
      UniformSubrepresentationGeneratorBound (permutationFunctionRepresentation (ZMod 2) U X) 7 := by
    apply hquad (quadraticShadow L)
    · intro q hq
      exact (mem_quadraticMasks_iff q).mp (Finset.mem_filter.mp hq).1
    · exact quadraticShadow_card_ge_four_of_cubic L hLanti (by omega) hlow a ha hac
    · intro q hq
      obtain ⟨_, a, ha, hqa⟩ := Finset.mem_filter.mp hq
      exact hdown a q hqa (hLA a ha)
  rcases boolean_four_antichain_four_alternatives A hA (by omega) with
    hone | htwo | hthree | ⟨i, hi, hshape⟩ | ⟨i, hi, hshape⟩
  · exact False.elim (hnon (T.squaresActTrivially_of_minimum_singleton_supports W v label
      (fun j => (hlead j).2) hinj (fun j => hone _ (hAmem _ (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ j, rfl⟩))) hcollision))
  · exact hquad L (fun a ha => htwo _ (hAmem a ha)) (by omega) hLA
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < L.card)
    exact hcubic a ha (hthree _ (hAmem a ha)) (fun b hb => by rw [hthree _ (hAmem b hb)]; omega)
  · let Q := L.filter (fun a => (support a).card = 2)
    have hQsub : Q ⊆ quadraticMasks.filter (fun a => i ∉ support a) := by
      intro a ha
      obtain ⟨haL, hac⟩ := Finset.mem_filter.mp ha
      rcases hshape _ (hAmem a haL) with he | ⟨_, hin⟩
      · have hc := congrArg Finset.card he
        rw [hac, Finset.card_singleton] at hc
        omega
      · exact Finset.mem_filter.mpr ⟨(mem_quadraticMasks_iff a).mpr hac, hin⟩
    have hLsub : L ⊆ insert (variableIndex i) Q := by
      intro a ha
      rcases hshape _ (hAmem a ha) with he | ⟨hc, _⟩
      · exact Finset.mem_insert.mpr (Or.inl (BinaryBooleanFourSupportRelabel.supportEquiv.injective
          (he.trans (variable_support i).symm)))
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨ha, hc⟩)
    have hQcard : 3 ≤ Q.card := by
      have hc := (Finset.card_le_card hLsub).trans (Finset.card_insert_le _ _)
      omega
    have hQeq : Q = quadraticMasks.filter (fun a => i ∉ support a) := by
      apply Finset.eq_of_subset_of_card_le hQsub
      rw [opposite_triangle_card]
      exact hQcard
    apply F.uniform_generatedBy_of_triangular_leading_shears T (BinaryTrianglePairWidth.Allowed i) 7
    · intro b hb
      apply hkernel
      rcases hb with ⟨hbi, hbc⟩ | he
      · obtain ⟨q, hq, hiq, hbq⟩ := opposite_triangle_covers i b hbi hbc
        have hqQ : q ∈ Q := by rw [hQeq]; exact Finset.mem_filter.mpr ⟨hq, hiq⟩
        exact hdown q b hbq (hLA q (Finset.mem_filter.mp hqQ).1)
      · obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hi
        have hba : b = a := BinaryBooleanFourSupportRelabel.supportEquiv.injective (he.trans hea.symm)
        exact hba.symm ▸ hLA a ha
    · intro s hs
      exact (BinaryTrianglePairWidth.antichain_card_le_six i s hs).trans (by decide)
  · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hi
    have hac : (support a).card = 3 := by rw [he, Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
    apply hcubic a ha hac
    intro b hb
    rcases hshape _ (hAmem b hb) with he | ⟨hc, _⟩
    · rw [he, Finset.card_compl, Fintype.card_fin, Finset.card_singleton]
      decide
    · omega

end SymmetricSubgroupAsymptotics.BinaryPairFrame
