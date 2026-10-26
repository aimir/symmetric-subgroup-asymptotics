import SymmetricSubgroupAsymptotics.CFSGMathieuElevenOrderFourConjugacy
import SymmetricSubgroupAsymptotics.CFSGOuterCardinalityCancellation
import SymmetricSubgroupAsymptotics.OuterFixedElementEvaluationBound

/-! Concrete inputs for fixed-generator outer counting on the SAME
original a/b subgroup. Every automorphism inner-aligns originalB; the
selected original x,y generate, and conjugation is injective under the
inherited pinned simplicity hypothesis. There is no accepted-image set
or assumed outer-order bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterNormalization
open CFSG.Certificates.Mathieu11 M11Certificates.ConjugacyClasses
open CFSGMathieuElevenPresentationWords CFSGMathieuElevenActualRepresentation

theorem originalB_order : orderOf originalB = 4 := by
  have ho : orderOf (representativeM11 rep4AIndex) = 4 := by
    rw [representativeM11_orderOf_eq]
    decide +kernel
  exact (orderOf_eq_of_isConj
    (CFSGMathieuElevenOrderFourConjugacy.isConj_originalB_of_order_four
      (representativeM11 rep4AIndex) ho)).symm.trans ho

theorem normalize_originalB (f : MulAut M11) :
    ∃ g : M11, (MulAut.conj g * f) originalB = originalB := by
  have hc := CFSGMathieuElevenOrderFourConjugacy.isConj_originalB_of_order_four
    (f originalB) ((f.orderOf_eq originalB).trans originalB_order)
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  exact ⟨g,hg⟩

theorem closure_pair_eq_top : Subgroup.closure ({x,y} : Set M11) = ⊤ := by
  let R := Subgroup.closure ({x,y} : Set M11)
  have htop : (⊤ : Subgroup CFSG.Models.Presentations.M11.Model) ≤
      R.comap representation := by
    rw [←PresentedGroup.closure_range_of {w | w ∈ CFSG.Models.Presentations.M11.relators}]
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change representation (PresentedGroup.of (0 : Fin 2)) ∈ R
      rw [representation_of_zero]
      exact Subgroup.subset_closure (by simp)
    · change representation (PresentedGroup.of (1 : Fin 2)) ∈ R
      rw [representation_of_one]
      exact Subgroup.subset_closure (by simp)
  apply top_unique
  intro g _
  obtain ⟨z,rfl⟩ := CFSGMathieuElevenActualEquivalence.representation_surjective g
  exact htop (by trivial)

theorem original_noncommutative : ¬ IsMulCommutative M11 := by
  let u : Perm11 := m11a ^ 2 * m11b ^ 2 * (m11a ^ 2)⁻¹
  have hx : M11Subgroup.subtype x = u := rfl
  have hy : M11Subgroup.subtype y = m11b := rfl
  have hmove : (u * m11b) (0 : Fin 11) ≠ (m11b * u) (0 : Fin 11) := by
    decide +kernel
  intro h
  letI : IsMulCommutative M11 := h
  have he := congrArg M11Subgroup.subtype (mul_comm' x y)
  rw [map_mul,map_mul,hx,hy] at he
  exact hmove (congrArg (fun p : Perm11 => p (0 : Fin 11)) he)

theorem conj_injective [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    Function.Injective (MulAut.conj : M11 →* MulAut M11) := by
  letI : Finite M11 := Finite.of_injective
    (fun g : M11 => (g : Perm11)) Subtype.val_injective
  letI : IsSimpleGroup M11 :=
    CFSGMathieuElevenActualEquivalence.actualEquivalence.symm.isSimpleGroup
  exact CFSGOuterCardinalityCancellation.conj_injective original_noncommutative

theorem outer_mul_eight_eq_fixedAutomorphisms
    [IsSimpleGroup CFSG.Models.Presentations.M11.Model] :
    Nat.card (PrimitiveSocleRawStructure.Outer M11) * 8 =
      Nat.card (OuterFixedElementEvaluationBound.fixedAutomorphisms originalB) := by
  letI : Finite M11 := Finite.of_injective
    (fun g : M11 => (g : Perm11)) Subtype.val_injective
  have h := OuterFixedElementEvaluationBound.outer_mul_centralizer_eq_fixedAutomorphisms
    originalB conj_injective normalize_originalB
  rwa [CFSGMathieuElevenOrderFourConjugacy.originalB_centralizer_card] at h

end SymmetricSubgroupAsymptotics.CFSGMathieuElevenOuterNormalization
