import SymmetricSubgroupAsymptotics.CFSGSignedSemilinearFaithfulness
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSimpleStabilizer
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalCommonField
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalParameterFaithful

/-! Actual positive-parameter faithfulness and common-field data for the
original G2 signed-label kernel. The full signed field description and
signed-generation faithfulness are proved original-model dependencies,
not additional hypotheses of these counting interfaces. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckStabilizerParameters
open CFSGSignedSemilinearFaithfulness CFSGGTwoD4GeckOriginalSimpleStabilizer
open CFSGGTwoD4GeckOriginalCommonField CFSGGTwoD4GeckOriginalParameterFaithful
open CFSGGTwoD4GeckOriginalSimpleParameters CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

def axisBool : Fin 2→Bool := ![false,true]

theorem axisIndex_axisBool (i : Fin 2) : (if axisBool i then 1 else 0 : Fin 2)=i := by
  fin_cases i <;> simp [axisBool]

def positiveParameter (i : Fin 2) (t : K) : Projective CartanMatrix.G₂ K :=
  originalSimpleHom K false (axisBool i) (Multiplicative.ofAdd t)

theorem parameters_faithful (f g : simpleStabilizer K p)
    (hparam : ∀i t,simpleStabilizerAction K p f (positiveParameter K i t)=
      simpleStabilizerAction K p g (positiveParameter K i t)) : f=g := by
  refine positive_faithful_of_signed_semilinear
    (fun neg a t=>originalSimpleHom K neg a (Multiplicative.ofAdd t))
    (simpleStabilizerAction K p) false ?_ ?_ ?_ f g ?_
  · intro a x y he
    exact congrArg Multiplicative.toAdd (originalSimpleHom_injective K false a he)
  · intro h k hfull
    apply Subtype.ext
    apply Subtype.ext
    apply original_parameters_faithful K
    intro neg a t
    exact hfull neg a t.toAdd
  · intro h
    obtain ⟨c,tau,hsem⟩ := original_simple_stabilizer_field_description K p h
    exact ⟨(fun a=>c (if a then 1 else 0)),tau,fun neg a t=>hsem neg a (Multiplicative.ofAdd t)⟩
  · intro a t
    cases a
    · exact hparam 0 t
    · exact hparam 1 t

theorem semilinear_parameters (f : simpleStabilizer K p) :
    ∃(tau : RingAut K)(c : Fin 2→Kˣ),∀i t,
      simpleStabilizerAction K p f (positiveParameter K i t)=
        positiveParameter K i ((c i : K)*tau t) := by
  obtain ⟨c,tau,hsem⟩ := original_simple_stabilizer_field_description K p f
  refine ⟨tau,c,?_⟩
  intro i t
  have he := hsem false (axisBool i) (Multiplicative.ofAdd t)
  simpa only [positiveParameter,Bool.false_eq_true,if_false,axisIndex_axisBool] using he

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckStabilizerParameters
