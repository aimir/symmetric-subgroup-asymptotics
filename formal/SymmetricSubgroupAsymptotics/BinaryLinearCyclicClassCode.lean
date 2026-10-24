import SymmetricSubgroupAsymptotics.BinaryMonicPolynomialCode
import SymmetricSubgroupAsymptotics.BinaryWeightedMultisetCodes
import SymmetricSubgroupAsymptotics.LinearMapCyclicConstantCoefficient
import SymmetricSubgroupAsymptotics.LinearMapCyclicCodeEquivalence
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.Group.ConjFinite

/-! Actual binary general-linear conjugacy classes inject into a finite
coefficient-multiset cover. Equal codes construct an intertwining linear
equivalence through the checked polynomial-module charts; invariance or
uniqueness of the arbitrarily chosen charts is not assumed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryLinearCyclicClassCode
open LinearMapPositiveCyclicDecomposition FiniteMultisetLabelMatching
open BinaryMonicPolynomialCode BinaryWeightedMultisetCodes
variable {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]

def code (g : LinearMap.GeneralLinearGroup K V) : Multiset (List Bool) :=
  labelMultiset (fun i => bits ((chart (g : Module.End K V)).polynomial i))

theorem weight_code (g : LinearMap.GeneralLinearGroup K V) :
    weight (code g) = Module.finrank K V := by
  classical
  let C := chart (g : Module.End K V)
  have h (i : C.ι) : (bits (C.polynomial i)).length + 1 = (C.polynomial i).natDegree := by
    rw [length_bits]
    have := C.positive i
    omega
  calc
    weight (code g) = ∑ i : C.ι, ((bits (C.polynomial i)).length + 1) := by
      simp only [weight, code, labelMultiset, Multiset.map_map, Function.comp_def]
      rfl
    _ = ∑ i : C.ι, (C.polynomial i).natDegree := Finset.sum_congr rfl (fun i _ => h i)
    _ = Module.finrank K V := C.degree_sum

theorem isConj_of_code_eq (hK : Fintype.card K = 2)
    (g h : LinearMap.GeneralLinearGroup K V) (he : code g = code h) : IsConj g h := by
  classical
  let C := chart (g : Module.End K V)
  let D := chart (h : Module.End K V)
  let E : C.ι ≃ D.ι := matchingEquiv (fun i => bits (C.polynomial i))
    (fun i => bits (D.polynomial i)) he
  have hp (i : C.ι) : C.polynomial i = D.polynomial (E i) :=
    eq_of_bits_eq hK (C.monic i) (D.monic (E i)) (C.positive i) (D.positive (E i))
      (LinearMapCyclicConstantCoefficient.constantCoeff_ne_zero C g.toLinearEquiv.surjective i)
      (LinearMapCyclicConstantCoefficient.constantCoeff_ne_zero D h.toLinearEquiv.surjective (E i))
      (matchingEquiv_spec (fun i => bits (C.polynomial i))
        (fun i => bits (D.polynomial i)) he i).symm
  have hc : LinearMapCyclicCodeEquivalence.code C = LinearMapCyclicCodeEquivalence.code D := by
    change labelMultiset C.polynomial = labelMultiset D.polynomial
    calc
      _ = labelMultiset (fun i => D.polynomial (E i)) := congrArg labelMultiset (funext hp)
      _ = _ := by
        unfold labelMultiset
        change Multiset.map (D.polynomial ∘ E) Finset.univ.val = _
        rw [← Multiset.map_map, Multiset.map_univ_val_equiv]
  obtain ⟨F, hF⟩ := LinearMapCyclicCodeEquivalence.exists_intertwining_equiv C D hc
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv F
  have hu : u * g = h * u := by
    apply Units.ext
    apply LinearMap.ext
    exact hF
  exact isConj_iff.mpr ⟨u, mul_inv_eq_iff_eq_mul.mpr hu⟩

def classRepresentative (c : ConjClasses (LinearMap.GeneralLinearGroup K V)) :
    LinearMap.GeneralLinearGroup K V := Classical.choose (ConjClasses.exists_rep c)

omit [Fintype K] [Module.Finite K V] in
theorem classRepresentative_spec (c : ConjClasses (LinearMap.GeneralLinearGroup K V)) :
    ConjClasses.mk (classRepresentative c) = c := Classical.choose_spec (ConjClasses.exists_rep c)

def classCode (c : ConjClasses (LinearMap.GeneralLinearGroup K V)) :
    {m : Multiset (List Bool) // m ∈ codes (Module.finrank K V)} :=
  ⟨code (classRepresentative c), by
    rw [← weight_code (classRepresentative c)]
    exact mem_codes_weight _⟩

theorem classCode_injective (hK : Fintype.card K = 2) :
    Function.Injective (classCode : ConjClasses (LinearMap.GeneralLinearGroup K V) → _) := by
  intro c d he
  rw [← classRepresentative_spec c, ← classRepresentative_spec d]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_of_code_eq hK _ _ (congrArg Subtype.val he))

theorem class_card_le_codes (hK : Fintype.card K = 2) :
    Nat.card (ConjClasses (LinearMap.GeneralLinearGroup K V)) ≤
      (codes (Module.finrank K V)).card := by
  have hc := Nat.card_le_card_of_injective classCode (classCode_injective (V := V) hK)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hc

theorem class_card_le_eighteen (hK : Fintype.card K = 2) (hV : Module.finrank K V = 4) :
    Nat.card (ConjClasses (LinearMap.GeneralLinearGroup K V)) ≤ 18 := by
  simpa only [hV, card_codes_four] using class_card_le_codes (V := V) hK

theorem class_card_le_one_hundred_four (hK : Fintype.card K = 2)
    (hV : Module.finrank K V = 6) :
    Nat.card (ConjClasses (LinearMap.GeneralLinearGroup K V)) ≤ 104 := by
  simpa only [hV, card_codes_six] using class_card_le_codes (V := V) hK

end SymmetricSubgroupAsymptotics.BinaryLinearCyclicClassCode
