import SymmetricSubgroupAsymptotics.CentralInvolutionQuotientClassBound
import SymmetricSubgroupAsymptotics.SLTwoSharpConjugacyClassBound
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-! Odd-characteristic projective SL2 has at most half of q+5
conjugacy classes. Multiplication by the actual negative identity fixes
only classes of trace zero. Such a trace is regular, hence contributes
at most one fixed class. The generic central-involution formula uses
the literal generated subgroup and then a surjection onto the full
central quotient; no description of the full SL2 centre is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.SLTwoProjectiveClassHalving
open SLTwoConjugacyClassBound
variable (K : Type*) [Field K]

def negIdentity : SL K := ⟨Matrix.scalar (Fin 2) (-1), by
  simp [Matrix.scalar_apply]⟩

theorem negIdentity_central : negIdentity K ∈ Subgroup.center (SL K) := by
  apply Subgroup.mem_center_iff.mpr
  intro A
  apply Subtype.ext
  exact (Matrix.scalar_commute (n:=Fin 2) (-1 : K) (Commute.all (-1)) A.val).symm

theorem negIdentity_square : negIdentity K*negIdentity K=1 := by
  apply Subtype.ext
  change Matrix.scalar (Fin 2) (-1 : K)*Matrix.scalar (Fin 2) (-1 : K)=1
  rw [← map_mul]
  simp only [neg_mul_neg,mul_one,map_one]

theorem negIdentity_mul_trace (A : SL K) :
    (negIdentity K*A).val.trace= -A.val.trace := by
  change (Matrix.scalar (Fin 2) (-1 : K)*A.val).trace= -A.val.trace
  simp [Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two,Matrix.scalar_apply,add_comm]

private theorem trace_eq_of_isConj (A B : SL K) (h : IsConj A B) :
    A.val.trace=B.val.trace := by
  obtain ⟨g,hg⟩ := isConj_iff.mp h
  have he := congrArg Matrix.SpecialLinearGroup.toGL hg
  rw [map_mul,map_mul,map_inv] at he
  have ht := congrArg
    (fun u : Matrix.GeneralLinearGroup (Fin 2) K => u.val.trace) he
  change ((Matrix.SpecialLinearGroup.toGL g).val*A.val*
    ((Matrix.SpecialLinearGroup.toGL g)⁻¹).val).trace=B.val.trace at ht
  exact (Matrix.trace_units_conj (Matrix.SpecialLinearGroup.toGL g) A.val).symm.trans ht

theorem trace_zero_nonscalar (h2 : (2 : K)≠0) (A : SL K) (ht : A.val.trace=0) :
    A.val ∉ Set.range (Matrix.scalar (Fin 2)) := by
  rintro ⟨a,ha⟩
  have hs : a+a=0 := by simpa only
    [← ha,Matrix.trace_fin_two,Matrix.scalar_apply,Matrix.diagonal_apply_eq] using ht
  have hm : (2 : K)*a=0 := by simpa only [two_mul] using hs
  have ha0 : a=0 := (mul_eq_zero.mp hm).resolve_left h2
  have hd : a^2=1 := by
    simpa [← ha,Matrix.det_fin_two,Matrix.scalar_apply,pow_two] using A.property
  rw [ha0,zero_pow (by decide : (2 : ℕ)≠0)] at hd
  exact zero_ne_one hd

theorem fixed_class_trace_zero (h2 : (2 : K)≠0) (c : ConjClasses (SL K))
    (hc : CentralInvolutionConjugacyClasses.translate (negIdentity K)
      (negIdentity_central K) c=c) : classTrace K c=0 := by
  let A := representative K c
  have he : IsConj (negIdentity K*A) A := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    calc
      ConjClasses.mk (negIdentity K*A)=
          CentralInvolutionConjugacyClasses.translate (negIdentity K) (negIdentity_central K)
            (ConjClasses.mk A) := rfl
      _ =CentralInvolutionConjugacyClasses.translate (negIdentity K) (negIdentity_central K) c :=
        congrArg _ (mk_representative K c)
      _ =c := hc
      _ =ConjClasses.mk A := (mk_representative K c).symm
  have ht := trace_eq_of_isConj K (negIdentity K*A) A he
  rw [negIdentity_mul_trace] at ht
  have hm : (2 : K)*A.val.trace=0 := by linear_combination -ht
  exact (mul_eq_zero.mp hm).resolve_left h2

local instance halvingSLFinite [Finite K] : Finite (SL K) :=
  Finite.of_injective (fun A : SL K => A.val) Subtype.val_injective

local instance halvingClassesFinite [Finite K] : Finite (ConjClasses (SL K)) :=
  Finite.of_surjective (@ConjClasses.mk (SL K) _) ConjClasses.mk_surjective

theorem fixed_class_card_le_one [Finite K] (h2 : (2 : K)≠0) :
    Nat.card {c : ConjClasses (SL K) // CentralInvolutionConjugacyClasses.translate
      (negIdentity K) (negIdentity_central K) c=c}≤1 := by
  let code : {c : ConjClasses (SL K) // CentralInvolutionConjugacyClasses.translate
      (negIdentity K) (negIdentity_central K) c=c} →
      {c : NonscalarClasses K // classTrace K c.val=0} := fun c =>
    ⟨⟨c.val,trace_zero_nonscalar K h2 (representative K c.val)
      (fixed_class_trace_zero K h2 c.val c.property)⟩,
      fixed_class_trace_zero K h2 c.val c.property⟩
  have hinj : Function.Injective code := by
    intro c d he
    apply Subtype.ext
    exact congrArg (fun u : {c : NonscalarClasses K // classTrace K c.val=0} => u.val.val) he
  have h4 : (4 : K)≠0 := by
    simpa only [show (4 : K)=2*2 by ring] using mul_ne_zero h2 h2
  exact (Nat.card_le_card_of_injective code hinj).trans
    (SLTwoSharpConjugacyClassBound.regular_trace_fibre_card_le_one K 0
      (by simpa only [zero_pow (by decide : (2 : ℕ)≠0)] using h4.symm))

theorem twice_projective_class_card_le [Finite K] (hchar : ringChar K≠2) :
    2*Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))≤Nat.card K+5 := by
  have hb := CentralInvolutionQuotientClassBound.twice_central_quotient_class_card_le
    (negIdentity K) (negIdentity_central K) (negIdentity_square K)
  change 2*Nat.card (ConjClasses (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K))≤
    Nat.card (ConjClasses (SL K))+Nat.card {c : ConjClasses (SL K) //
      CentralInvolutionConjugacyClasses.translate (negIdentity K) (negIdentity_central K) c=c} at hb
  have hf := fixed_class_card_le_one K (Ring.two_ne_zero hchar)
  have hs := SLTwoSharpConjugacyClassBound.class_card_le K
  omega

end SymmetricSubgroupAsymptotics.SLTwoProjectiveClassHalving
