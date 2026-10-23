import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalSimpleStabilizer
import SymmetricSubgroupAsymptotics.CFSGFFourE6OriginalParameterFaithful

/-! Actual faithful common-field data on the signed simple-label kernel
inside the original F4 opposed-Sylow stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFFourE6StabilizerParameters
open CFSGFFourE6OriginalSimpleStabilizer CFSGFFourE6OriginalParameterFaithful
open CFSGFFourE6OriginalFieldAgreement CFSGFFourE6OriginalSimpleParameters CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]
    [IsSimpleGroup (Projective CartanMatrix.F₄ K)]

theorem parameters_faithful (f g : simpleStabilizer K p)
    (hparam : ∀i a,simpleStabilizerAction K p f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
      simpleStabilizerAction K p g (originalSimpleHom K false i (Multiplicative.ofAdd a))) : f=g := by
  apply inv_mul_eq_one.mp
  apply Subtype.ext
  apply Subtype.ext
  apply eq_one_of_positive_parameters_fixed K p (simpleStabilizerAction K p (f⁻¹*g))
    (simple_preserves_chart K p (f⁻¹*g))
  intro i a
  change (simpleStabilizerAction K p f).symm
    (simpleStabilizerAction K p g (originalSimpleHom K false i (Multiplicative.ofAdd a)))=_
  rw [←hparam i a]
  exact (simpleStabilizerAction K p f).symm_apply_apply _

theorem semilinear_parameters (f : simpleStabilizer K p) :
    ∃(tau : RingAut K) (c : Fin 4→Kˣ),∀i a,
      simpleStabilizerAction K p f (originalSimpleHom K false i (Multiplicative.ofAdd a))=
        originalSimpleHom K false i (Multiplicative.ofAdd ((c i : K)*tau a)) := by
  obtain ⟨tau,c,hsem⟩ := exists_common_field_parameters K p (simpleStabilizerAction K p f)
    (simple_preserves_chart K p f)
  exact ⟨tau,c,hsem false⟩

end SymmetricSubgroupAsymptotics.CFSGFFourE6StabilizerParameters
