import SymmetricSubgroupAsymptotics.MonicPolynomialUnitCoefficientCode
import SymmetricSubgroupAsymptotics.FiniteCoefficientMultisetCardinality
import SymmetricSubgroupAsymptotics.LinearMapCyclicConstantCoefficient
import SymmetricSubgroupAsymptotics.LinearMapCyclicCodeEquivalence
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.ConjFinite

/-! Actual general-linear conjugacy classes inject into weighted
coefficient multisets over ANY finite field. Equal codes construct an
intertwiner through the existing polynomial-module charts; no canonical
choice or uniqueness of the selected decomposition is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.FiniteFieldLinearCyclicClassBound
open LinearMapPositiveCyclicDecomposition FiniteMultisetLabelMatching
open MonicPolynomialUnitCoefficientCode
variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

private def label (g : LinearMap.GeneralLinearGroup K V)
    (i : (chart (g : Module.End K V)).ι) : Kˣ × List K :=
  MonicPolynomialUnitCoefficientCode.code ((chart (g : Module.End K V)).polynomial i)
    (LinearMapCyclicConstantCoefficient.constantCoeff_ne_zero
      (chart (g : Module.End K V)) g.toLinearEquiv.surjective i)

def code (g : LinearMap.GeneralLinearGroup K V) : Multiset (Kˣ × List K) :=
  labelMultiset (label g)

theorem weight_code (g : LinearMap.GeneralLinearGroup K V) :
    FiniteCoefficientMultisetCardinality.weight (code g)=Module.finrank K V := by
  classical
  let C := chart (g : Module.End K V)
  have h (i : C.ι) : (label g i).2.length+1=(C.polynomial i).natDegree := by
    change (MonicPolynomialUnitCoefficientCode.code (C.polynomial i) _).2.length+1=_
    rw [length_code]
    have := C.positive i
    omega
  calc
    _ = ∑ i : C.ι, ((label g i).2.length+1) := by
      simp only [FiniteCoefficientMultisetCardinality.weight,code,labelMultiset,
        Multiset.map_map,Function.comp_def]
      rfl
    _ = ∑ i : C.ι, (C.polynomial i).natDegree := Finset.sum_congr rfl (fun i _ => h i)
    _ = Module.finrank K V := C.degree_sum

theorem isConj_of_code_eq (g h : LinearMap.GeneralLinearGroup K V)
    (he : code g=code h) : IsConj g h := by
  classical
  let C := chart (g : Module.End K V)
  let D := chart (h : Module.End K V)
  let E : C.ι ≃ D.ι := matchingEquiv (label g) (label h) he
  have hp (i : C.ι) : C.polynomial i=D.polynomial (E i) :=
    eq_of_code_eq (C.monic i) (D.monic (E i)) (C.positive i) (D.positive (E i))
      (LinearMapCyclicConstantCoefficient.constantCoeff_ne_zero C g.toLinearEquiv.surjective i)
      (LinearMapCyclicConstantCoefficient.constantCoeff_ne_zero D h.toLinearEquiv.surjective (E i))
      (matchingEquiv_spec (label g) (label h) he i).symm
  have hc : LinearMapCyclicCodeEquivalence.code C=LinearMapCyclicCodeEquivalence.code D := by
    change labelMultiset C.polynomial=labelMultiset D.polynomial
    calc
      _ = labelMultiset (fun i => D.polynomial (E i)) := congrArg labelMultiset (funext hp)
      _ = _ := by
        unfold labelMultiset
        change Multiset.map (D.polynomial ∘ E) Finset.univ.val=_
        rw [←Multiset.map_map,Multiset.map_univ_val_equiv]
  obtain ⟨F,hF⟩ := LinearMapCyclicCodeEquivalence.exists_intertwining_equiv C D hc
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv F
  have hu : u*g=h*u := by
    apply Units.ext
    apply LinearMap.ext
    exact hF
  exact isConj_iff.mpr ⟨u,mul_inv_eq_iff_eq_mul.mpr hu⟩

private def representative (c : ConjClasses (LinearMap.GeneralLinearGroup K V)) :
    LinearMap.GeneralLinearGroup K V := Classical.choose (ConjClasses.exists_rep c)

private theorem representative_spec (c : ConjClasses (LinearMap.GeneralLinearGroup K V)) :
    ConjClasses.mk (representative c)=c := Classical.choose_spec (ConjClasses.exists_rep c)

def classCode (c : ConjClasses (LinearMap.GeneralLinearGroup K V)) :
    {m : Multiset (Kˣ × List K) //
      FiniteCoefficientMultisetCardinality.weight m=Module.finrank K V} :=
  ⟨code (representative c),weight_code (representative c)⟩

theorem classCode_injective :
    Function.Injective (classCode (K := K) (V := V)) := by
  intro c d he
  rw [←representative_spec c,←representative_spec d]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr
    (isConj_of_code_eq _ _ (congrArg Subtype.val he))

theorem class_card_le_coefficients (hdim : 0 < Module.finrank K V) :
    Nat.card (ConjClasses (LinearMap.GeneralLinearGroup K V)) ≤
      (Nat.card K-1)*(2*Nat.card K-1)^(Module.finrank K V-1) := by
  letI : Finite {m : Multiset (Kˣ × List K) //
      FiniteCoefficientMultisetCardinality.weight m=Module.finrank K V} :=
    FiniteCoefficientMultisetCardinality.finite_weight (Module.finrank K V) hdim
  have hc := Nat.card_le_card_of_injective classCode (classCode_injective (K := K) (V := V))
  have hh := FiniteCoefficientMultisetCardinality.card_le (A := Kˣ) (B := K)
    (Module.finrank K V) hdim
  rw [Nat.card_units] at hh
  have hq : 0 < Nat.card K := Nat.card_pos
  have he : (Nat.card K-1)+Nat.card K=2*Nat.card K-1 := by omega
  rw [he] at hh
  exact hc.trans hh

end SymmetricSubgroupAsymptotics.FiniteFieldLinearCyclicClassBound
