import SymmetricSubgroupAsymptotics.SLTwoConjugacyClassBound
import SymmetricSubgroupAsymptotics.SLTwoRegularTraceConjugacy
import Mathlib.Data.Fintype.BigOperators

/-! A uniform q+4 bound for the actual SL2 conjugacy classes. Away from
trace squared equal to four, the determinant-correcting centralizer
gives at most one nonscalar class. There are at most two exceptional
traces, each retaining the checked two-class bound. Scalar classes
contribute at most two. No class formula or torus classification is
assumed, and characteristic two is included. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.SLTwoSharpConjugacyClassBound
open SLTwoConjugacyClassBound
variable (K : Type*) [Field K] [Finite K]

local instance sharpSLFinite : Finite (SL K) :=
  Finite.of_injective (fun g : SL K => g.val) Subtype.val_injective

local instance sharpClassesFinite : Finite (ConjClasses (SL K)) :=
  Finite.of_surjective (@ConjClasses.mk (SL K) _) ConjClasses.mk_surjective

theorem regular_trace_fibre_card_le_one (t : K) (ht : t^2≠4) :
    Nat.card {c : NonscalarClasses K // classTrace K c.val=t}≤1 := by
  have hsub (c d : {c : NonscalarClasses K // classTrace K c.val=t}) : c=d := by
    apply Subtype.ext
    apply Subtype.ext
    have hc : IsConj (representative K c.val.val) (representative K d.val.val) := by
      apply SLTwoRegularTraceConjugacy.isConj_of_trace_eq
        (representative K c.val.val) (representative K d.val.val)
        c.val.property d.val.property
      · have he : (representative K c.val.val).val.trace=t := c.property
        simpa only [he] using ht
      · exact c.property.trans d.property.symm
    exact (mk_representative K c.val.val).symm.trans
      ((ConjClasses.mk_eq_mk_iff_isConj.mpr hc).trans (mk_representative K d.val.val))
  let code : {c : NonscalarClasses K // classTrace K c.val=t} → Fin 1 := fun _ => 0
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective code (fun c d _ => hsub c d)

theorem exceptional_trace_card_le_two : Nat.card {t : K // t^2=4}≤2 := by
  have hcase (t : {t : K // t^2=4}) : t.val=2 ∨ t.val= -2 := by
    have htwo : (2 : K)^2=4 := by ring
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (t.property.trans htwo.symm)
  let code : {t : K // t^2=4} → Bool := fun t => decide (t.val=2)
  have hinj : Function.Injective code := by
    intro t u he
    apply Subtype.ext
    change decide (t.val=2)=decide (u.val=2) at he
    have hi : (t.val=2 ↔ u.val=2) := decide_eq_decide.mp he
    by_cases ht : t.val=2
    · exact ht.trans (hi.mp ht).symm
    · have hu : u.val≠2 := fun h => ht (hi.mpr h)
      exact ((hcase t).resolve_left ht).trans ((hcase u).resolve_left hu).symm
  simpa only [Nat.card_eq_fintype_card, Fintype.card_bool] using
    Nat.card_le_card_of_injective code hinj

private theorem sum_indicator {T : Type*} [Fintype T]
    (P : T → Prop) [DecidablePred P] :
    (∑ t : T, if P t then (1 : ℕ) else 0)=Nat.card {t : T // P t} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.sum_filter]
  simp

theorem nonscalar_class_card_le : Nat.card (NonscalarClasses K)≤Nat.card K+2 := by
  letI : Fintype K := Fintype.ofFinite K
  have hb (t : K) : Nat.card {c : NonscalarClasses K // classTrace K c.val=t}≤
      1+(if t^2=4 then 1 else 0) := by
    by_cases ht : t^2=4
    · simpa only [if_pos ht] using nonscalar_trace_fibre_card_le_two K t
    · simpa only [if_neg ht, add_zero] using regular_trace_fibre_card_le_one K t ht
  calc
    Nat.card (NonscalarClasses K)=
        Nat.card (Σ t : K, {c : NonscalarClasses K // classTrace K c.val=t}) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv (fun c : NonscalarClasses K => classTrace K c.val))).symm
    _ =∑ t : K, Nat.card {c : NonscalarClasses K // classTrace K c.val=t} := Nat.card_sigma
    _ ≤∑ t : K, (1+(if t^2=4 then 1 else 0)) := Finset.sum_le_sum (fun t _ => hb t)
    _ =(∑ _t : K, (1 : ℕ))+(∑ t : K, if t^2=4 then 1 else 0) := Finset.sum_add_distrib
    _ =Nat.card K+Nat.card {t : K // t^2=4} := congrArg₂ Nat.add
      (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Nat.card_eq_fintype_card, Nat.cast_id]) (sum_indicator (fun t : K => t^2=4))
    _ ≤Nat.card K+2 := Nat.add_le_add_left (exceptional_trace_card_le_two K) _

theorem class_card_le : Nat.card (ConjClasses (SL K))≤Nat.card K+4 := by
  have hsplit : Nat.card (NonscalarClasses K)+Nat.card (ScalarClasses K)=
      Nat.card (ConjClasses (SL K)) := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl
      (fun c : ConjClasses (SL K) => (representative K c).val ∉ Set.range (Matrix.scalar (Fin 2))))
  have hn := nonscalar_class_card_le K
  have hs := scalar_class_card_le_two K
  omega

end SymmetricSubgroupAsymptotics.SLTwoSharpConjugacyClassBound
