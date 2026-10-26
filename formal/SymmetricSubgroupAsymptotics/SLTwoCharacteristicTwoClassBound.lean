import SymmetricSubgroupAsymptotics.SLTwoCharacteristicTwoConjugacyFibre
import SymmetricSubgroupAsymptotics.SLTwoConjugacyClassBound

/-! An actual q+1 conjugacy-class bound for SL2 over any finite field
of characteristic2. Every nonscalar trace has at most one original class
and the only scalar determinant-one matrix is the identity. No class
formula, model order, subgroup catalogue or numerical capacity is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SLTwoCharacteristicTwoClassBound
open SLTwoConjugacyClassBound
variable (K : Type*) [Field K] [Finite K]

local instance slFinite : Finite (SL K) :=
  Finite.of_injective (fun g : SL K=>g.val) Subtype.val_injective
local instance classesFinite : Finite (ConjClasses (SL K)) :=
  Finite.of_surjective (@ConjClasses.mk (SL K) _) ConjClasses.mk_surjective

theorem nonscalar_trace_fibre_card_le_one (hchar : ringChar K=2) (t : K) :
    Nat.card {c : NonscalarClasses K // classTrace K c.val=t}≤1 := by
  letI : Finite (ConjClasses (Matrix.GeneralLinearGroup (Fin 2) K)) :=
    Finite.of_surjective (@ConjClasses.mk (Matrix.GeneralLinearGroup (Fin 2) K) _)
      ConjClasses.mk_surjective
  by_cases he : Nonempty {c : NonscalarClasses K // classTrace K c.val=t}
  · obtain ⟨a⟩ := he
    let A := representative K a.val.val
    let encode : {c : NonscalarClasses K // classTrace K c.val=t} →
        {c : ConjClasses (SL K) // ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
          ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} := fun c => ⟨c.val.val, by
      rw [← mk_representative K c.val.val]
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply FiniteTwoTraceConjugacy.isConj_toGL_of_trace_eq
        (representative K c.val.val) A c.val.property a.val.property
      exact c.property.trans a.property.symm⟩
    have hinj : Function.Injective encode := by
      intro c d h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {c : ConjClasses (SL K) //
        ConjClasses.map Matrix.SpecialLinearGroup.toGL c=
          ConjClasses.mk (Matrix.SpecialLinearGroup.toGL A)} => z.val) h
    exact (Nat.card_le_card_of_injective encode hinj).trans
      (SLTwoCharacteristicTwoConjugacyFibre.class_fibre_card_le_one K hchar A)
  · letI : IsEmpty {c : NonscalarClasses K // classTrace K c.val=t} :=
      ⟨fun c => he ⟨c⟩⟩
    simp only [Nat.card_of_isEmpty, Nat.zero_le]

theorem nonscalar_class_card_le_field (hchar : ringChar K=2) :
    Nat.card (NonscalarClasses K)≤Nat.card K := by
  letI : Fintype K := Fintype.ofFinite K
  calc
    Nat.card (NonscalarClasses K)=
        Nat.card (Σt:K,{c:NonscalarClasses K // classTrace K c.val=t}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv
        (fun c:NonscalarClasses K=>classTrace K c.val))).symm
    _=∑t:K,Nat.card {c:NonscalarClasses K // classTrace K c.val=t} := Nat.card_sigma
    _≤∑_t:K,1 := Finset.sum_le_sum (fun t _=>nonscalar_trace_fibre_card_le_one K hchar t)
    _=Nat.card K := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
      mul_one,Nat.card_eq_fintype_card,Nat.cast_id]

omit [Finite K] in
theorem scalar_class_card_le_one (hchar : ringChar K=2) :
    Nat.card (ScalarClasses K)≤1 := by
  have hrep : ∀c:ScalarClasses K,(representative K c.val).val=1 := by
    intro c
    obtain ⟨a,ha⟩ := not_not.mp c.property
    have hd : (Matrix.scalar (Fin 2) a).det=1 := by
      rw [ha]
      exact (representative K c.val).property
    have hs : a^2=1 := by
      simpa [Matrix.scalar_apply,Matrix.det_fin_two,pow_two] using hd
    have ha1 : a=1 := (sq_eq_one_iff.mp hs).elim id
      (fun h=>h.trans (neg_one_eq_one_iff.mpr hchar))
    exact ha.symm.trans (by rw [ha1,map_one])
  let code : ScalarClasses K→Unit := fun _=>()
  have hi : Function.Injective code := by
    intro c d _
    apply Subtype.ext
    apply representative_injective K
    apply Subtype.ext
    exact (hrep c).trans (hrep d).symm
  exact (Nat.card_le_card_of_injective code hi).trans_eq (by simp)

/-- The full original SL2 class space, including its actual scalar class. -/
theorem class_card_le_field_add_one (hchar : ringChar K=2) :
    Nat.card (ConjClasses (SL K))≤Nat.card K+1 := by
  have hsplit : Nat.card (NonscalarClasses K)+Nat.card (ScalarClasses K)=
      Nat.card (ConjClasses (SL K)) := by
    rw [←Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl
      (fun c:ConjClasses (SL K)=>(representative K c).val∉Set.range (Matrix.scalar (Fin 2))))
  have hn := nonscalar_class_card_le_field K hchar
  have hs := scalar_class_card_le_one K hchar
  omega

end SymmetricSubgroupAsymptotics.SLTwoCharacteristicTwoClassBound
