import SymmetricSubgroupAsymptotics.LinearMapInvertiblePrimaryLabels
import SymmetricSubgroupAsymptotics.BinaryFourIrreduciblePolynomialLabels
import SymmetricSubgroupAsymptotics.BinaryLinearCyclicClassCode

/-! The ACTUAL primary quotient chart of a binary invertible operator
of dimension four injects its conjugacy classes into the proved fourteen
weighted coefficient codes. Equal codes match actual polynomial powers
and construct an intertwiner; chosen charts need not be canonical. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryFourPrimaryClassCode
open FiniteMultisetLabelMatching BinaryFourPrimaryLabelCodes
variable {K V : Type*} [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup V] [Module K V] [Module.Finite K V]

private theorem exponent_le_four (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V))
    (i : C.cyclic.ι) : C.exponent i≤4 := by
  have h : C.exponent i≤∑ j : C.cyclic.ι, C.exponent j :=
    Finset.single_le_sum (s := Finset.univ) (f := C.exponent)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  exact (h.trans C.exponent_sum_le_dimension).trans_eq hV

private theorem index_exists (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V))
    (i : C.cyclic.ι) :
    ∃ j : Fin 7, BinaryMonicPolynomialCode.bits (C.prime i)=
      BinaryFourIrreduciblePolynomialLabels.word j ∧
      (C.prime i).natDegree=degree j :=
  BinaryFourIrreduciblePolynomialLabels.exists_index hK (C.prime i) (C.monic i)
    (C.irreducible i) (LinearMapInvertiblePrimaryLabels.prime_constantCoeff_ne_zero g C i)
    ((LinearMapInvertiblePrimaryLabels.prime_natDegree_le_finrank g C i).trans_eq hV)

private def slot (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V))
    (i : C.cyclic.ι) : Label :=
  (Classical.choose (index_exists hK hV g C i),
    ⟨C.exponent i-1,by have := exponent_le_four hV g C i; have := C.positive i; omega⟩)

private theorem slot_word (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V)) (i : C.cyclic.ι) :
    BinaryMonicPolynomialCode.bits (C.prime i)=
      BinaryFourIrreduciblePolynomialLabels.word (slot hK hV g C i).1 :=
  (Classical.choose_spec (index_exists hK hV g C i)).1

private theorem slot_degree (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V)) (i : C.cyclic.ι) :
    (C.prime i).natDegree=degree (slot hK hV g C i).1 :=
  (Classical.choose_spec (index_exists hK hV g C i)).2

private theorem slot_exponent (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V)
    (C : LinearMapPositivePrimaryDecomposition.Chart (g : Module.End K V)) (i : C.cyclic.ι) :
    (slot hK hV g C i).2.val+1=C.exponent i := by
  change C.exponent i-1+1=C.exponent i
  have := C.positive i
  omega

def code (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V) : Multiset Label :=
  let C := LinearMapPositivePrimaryDecomposition.chart (g : Module.End K V)
  labelMultiset (slot hK hV g C)

theorem weight_code (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g : LinearMap.GeneralLinearGroup K V) : weight (code hK hV g)=4 := by
  let C := LinearMapPositivePrimaryDecomposition.chart (g : Module.End K V)
  calc
    weight (code hK hV g)=∑ i : C.cyclic.ι, labelWeight (slot hK hV g C i) := by
      simp only [weight,code,labelMultiset,Multiset.map_map,Function.comp_def]
      rfl
    _=∑ i : C.cyclic.ι, C.exponent i*(C.prime i).natDegree := by
      apply Finset.sum_congr rfl
      intro i _
      change degree (slot hK hV g C i).1*((slot hK hV g C i).2.val+1)=_
      rw [slot_exponent hK hV g C i,←slot_degree hK hV g C i]
      exact Nat.mul_comm _ _
    _=4 := C.degree_sum.trans hV

theorem isConj_of_code_eq (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (g h : LinearMap.GeneralLinearGroup K V) (he : code hK hV g=code hK hV h) :
    IsConj g h := by
  let C := LinearMapPositivePrimaryDecomposition.chart (g : Module.End K V)
  let D := LinearMapPositivePrimaryDecomposition.chart (h : Module.End K V)
  let E : C.cyclic.ι ≃ D.cyclic.ι :=
    matchingEquiv (slot hK hV g C) (slot hK hV h D) he
  have hslot (i : C.cyclic.ι) : slot hK hV g C i=slot hK hV h D (E i) :=
    (matchingEquiv_spec (slot hK hV g C) (slot hK hV h D) he i).symm
  have hprime (i : C.cyclic.ι) : C.prime i=D.prime (E i) := by
    apply BinaryMonicPolynomialCode.eq_of_bits_eq hK (C.monic i) (D.monic (E i))
      (C.irreducible i).natDegree_pos (D.irreducible (E i)).natDegree_pos
      (LinearMapInvertiblePrimaryLabels.prime_constantCoeff_ne_zero g C i)
      (LinearMapInvertiblePrimaryLabels.prime_constantCoeff_ne_zero h D (E i))
    calc
      _=BinaryFourIrreduciblePolynomialLabels.word (slot hK hV g C i).1 := slot_word hK hV g C i
      _=BinaryFourIrreduciblePolynomialLabels.word (slot hK hV h D (E i)).1 :=
        congrArg (fun a : Label => BinaryFourIrreduciblePolynomialLabels.word a.1) (hslot i)
      _=_ := (slot_word hK hV h D (E i)).symm
  have hexponent (i : C.cyclic.ι) : C.exponent i=D.exponent (E i) := by
    have hh := congrArg (fun a : Label => a.2.val+1) (hslot i)
    change (slot hK hV g C i).2.val+1=(slot hK hV h D (E i)).2.val+1 at hh
    rw [slot_exponent hK hV g C i,slot_exponent hK hV h D (E i)] at hh
    exact hh
  have hp (i : C.cyclic.ι) : C.cyclic.polynomial i=D.cyclic.polynomial (E i) := by
    rw [C.power_eq,D.power_eq,hprime i,hexponent i]
  have hc : LinearMapCyclicCodeEquivalence.code C.cyclic=
      LinearMapCyclicCodeEquivalence.code D.cyclic := by
    change labelMultiset C.cyclic.polynomial=labelMultiset D.cyclic.polynomial
    calc
      _=labelMultiset (fun i => D.cyclic.polynomial (E i)) := congrArg labelMultiset (funext hp)
      _=_ := by
        unfold labelMultiset
        change Multiset.map (D.cyclic.polynomial ∘ E) Finset.univ.val=_
        rw [←Multiset.map_map,Multiset.map_univ_val_equiv]
  obtain ⟨F,hF⟩ := LinearMapCyclicCodeEquivalence.exists_intertwining_equiv C.cyclic D.cyclic hc
  let u := LinearMap.GeneralLinearGroup.ofLinearEquiv F
  have hu : u*g=h*u := by
    apply Units.ext
    apply LinearMap.ext
    exact hF
  exact isConj_iff.mpr ⟨u,mul_inv_eq_iff_eq_mul.mpr hu⟩

def classCode (hK : Fintype.card K=2) (hV : Module.finrank K V=4)
    (c : ConjClasses (LinearMap.GeneralLinearGroup K V)) :
    {m : Multiset Label // m∈codes 4} :=
  ⟨code hK hV (BinaryLinearCyclicClassCode.classRepresentative c),by
    have hm := mem_codes_weight (code hK hV (BinaryLinearCyclicClassCode.classRepresentative c))
    rwa [weight_code] at hm⟩

theorem classCode_injective (hK : Fintype.card K=2) (hV : Module.finrank K V=4) :
    Function.Injective (classCode hK hV) := by
  intro c d he
  rw [←BinaryLinearCyclicClassCode.classRepresentative_spec c,
    ←BinaryLinearCyclicClassCode.classRepresentative_spec d]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr
    (isConj_of_code_eq hK hV _ _ (congrArg Subtype.val he))

theorem class_card_le_fourteen (hK : Fintype.card K=2) (hV : Module.finrank K V=4) :
    Nat.card (ConjClasses (LinearMap.GeneralLinearGroup K V))≤14 := by
  have hc := Nat.card_le_card_of_injective (classCode hK hV) (classCode_injective hK hV)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe,card_codes_four] using hc

end SymmetricSubgroupAsymptotics.BinaryFourPrimaryClassCode
