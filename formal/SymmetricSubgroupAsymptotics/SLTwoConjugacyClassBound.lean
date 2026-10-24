import SymmetricSubgroupAsymptotics.SLTwoConjugacyFibre
import SymmetricSubgroupAsymptotics.FiniteTwoTraceConjugacy
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! An actual class bound for SL2 over every finite field. Nonscalar
classes are grouped by their actual trace; each trace fibre injects into
one GL2 conjugacy fibre, which has at most two SL2 classes. The scalar
classes are coded by the two roots of a^2=1. No subgroup/class table or
classification of semisimple/unipotent elements is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SLTwoConjugacyClassBound
variable (K : Type*) [Field K]
abbrev SL := Matrix.SpecialLinearGroup (Fin 2) K

def representative (c : ConjClasses (SL K)) : SL K :=
  Classical.choose (ConjClasses.exists_rep c)

theorem mk_representative (c : ConjClasses (SL K)) :
    ConjClasses.mk (representative K c)=c := Classical.choose_spec (ConjClasses.exists_rep c)

theorem representative_injective : Function.Injective (representative K) := by
  intro c d he
  exact (mk_representative K c).symm.trans
    ((congrArg ConjClasses.mk he).trans (mk_representative K d))

def classTrace (c : ConjClasses (SL K)) : K := (representative K c).val.trace

abbrev NonscalarClasses :=
  {c : ConjClasses (SL K) // (representative K c).val ∉ Set.range (Matrix.scalar (Fin 2))}

abbrev ScalarClasses :=
  {c : ConjClasses (SL K) // ¬(representative K c).val ∉ Set.range (Matrix.scalar (Fin 2))}

local instance slTwoFinite [Finite K] : Finite (SL K) :=
  Finite.of_injective (fun g : SL K => g.val) Subtype.val_injective

local instance classesFinite [Finite K] : Finite (ConjClasses (SL K)) :=
  Finite.of_surjective (@ConjClasses.mk (SL K) _) ConjClasses.mk_surjective

theorem scalar_class_card_le_two [Finite K] : Nat.card (ScalarClasses K)≤2 := by
  have hcase (c : ScalarClasses K) : (representative K c.val).val=1 ∨
      (representative K c.val).val=Matrix.scalar (Fin 2) (-1:K) := by
    obtain ⟨a,ha⟩ := not_not.mp c.property
    have hd : (Matrix.scalar (Fin 2) a).det=1 := by
      rw [ha]
      exact (representative K c.val).property
    have ha2 : a^2=1 := by
      simpa [Matrix.scalar_apply, Matrix.det_fin_two, pow_two] using hd
    rcases sq_eq_one_iff.mp ha2 with h | h
    · left
      simpa only [h, map_one] using ha.symm
    · right
      simpa only [h] using ha.symm
  let code : ScalarClasses K → Bool := fun c => decide ((representative K c.val).val=1)
  have hinj : Function.Injective code := by
    intro c d he
    apply Subtype.ext
    apply representative_injective K
    apply Subtype.ext
    change decide ((representative K c.val).val=1)=
      decide ((representative K d.val).val=1) at he
    have hi : ((representative K c.val).val=1 ↔ (representative K d.val).val=1) :=
      decide_eq_decide.mp he
    by_cases hc : (representative K c.val).val=1
    · exact hc.trans (hi.mp hc).symm
    · have hd : (representative K d.val).val≠1 := fun h => hc (hi.mpr h)
      exact ((hcase c).resolve_left hc).trans ((hcase d).resolve_left hd).symm
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using Nat.card_le_card_of_injective code hinj

theorem nonscalar_trace_fibre_card_le_two [Finite K] (t : K) :
    Nat.card {c : NonscalarClasses K // classTrace K c.val=t}≤2 := by
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
      (SLTwoConjugacyFibre.class_fibre_card_le_two K A)
  · letI : IsEmpty {c : NonscalarClasses K // classTrace K c.val=t} :=
      ⟨fun c => he ⟨c⟩⟩
    simp only [Nat.card_of_isEmpty, Nat.zero_le]

theorem nonscalar_class_card_le [Finite K] : Nat.card (NonscalarClasses K)≤2*Nat.card K := by
  letI : Fintype K := Fintype.ofFinite K
  calc
    Nat.card (NonscalarClasses K)=
        Nat.card (Σ t : K, {c : NonscalarClasses K // classTrace K c.val=t}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv (fun c : NonscalarClasses K => classTrace K c.val))).symm
    _ =∑ t : K, Nat.card {c : NonscalarClasses K // classTrace K c.val=t} := Nat.card_sigma
    _ ≤∑ _t : K, 2 := Finset.sum_le_sum (fun t _ => nonscalar_trace_fibre_card_le_two K t)
    _ =2*Nat.card K := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card, Nat.cast_id, Nat.mul_comm]

theorem class_card_le_two_mul_add_two [Finite K] :
    Nat.card (ConjClasses (SL K))≤2*Nat.card K+2 := by
  have hsplit : Nat.card (NonscalarClasses K)+Nat.card (ScalarClasses K)=
      Nat.card (ConjClasses (SL K)) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl
      (fun c : ConjClasses (SL K) => (representative K c).val ∉ Set.range (Matrix.scalar (Fin 2))))
  have hn := nonscalar_class_card_le K
  have hs := scalar_class_card_le_two K
  omega

theorem class_card_le [Finite K] : Nat.card (ConjClasses (SL K))≤2*Nat.card K+4 :=
  (class_card_le_two_mul_add_two K).trans (by omega)

end SymmetricSubgroupAsymptotics.SLTwoConjugacyClassBound
