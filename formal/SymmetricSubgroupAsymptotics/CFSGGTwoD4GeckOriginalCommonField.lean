import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPositiveScalarNormalization
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalSignedSemilinear
import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalMiddleTorus

/-! The literal middle torus has Cartan exponent minus one on the short
axis, so the two normalized signed field actions agree. Undoing the
actual inner torus gives the complete common-field and reciprocal-scalar
description of the SAME original signed-label stabilizer. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalCommonField
open CFSGGTwoD4GeckPositiveScalarNormalization CFSGGTwoD4GeckOriginalSignedSemilinear
open CFSGGTwoD4GeckOriginalSimpleStabilizer CFSGGTwoD4GeckOriginalSimpleParameters
open CFSGGTwoD4GeckOriginalMiddleTorus CFSGRankOneTorusFieldCoupling
open CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]

theorem normalized_common_field (f : MulAut (Projective CartanMatrix.G₂ K))
    (tau : Bool → RingAut K)
    (h : ∀(neg a:Bool) (t:K),f (originalSimpleHom K neg a (Multiplicative.ofAdd t))=
      originalSimpleHom K neg a (Multiplicative.ofAdd (tau a t))) : tau false=tau true :=
  field_eq_of_inverse_torus_action (originalSimpleHom K false false)
    (originalSimpleHom_injective K false false)
    (fun neg=>originalSimpleHom K neg true) (long_torusWord_short_action K)
    f (tau false) (tau true) (h false false) (fun neg=>h neg true)

theorem original_simple_stabilizer_field_description (p : ℕ) [Fact p.Prime] [CharP K p]
    (f : simpleStabilizer K p) :
    ∃ (c : Fin 2→Kˣ) (tau : RingAut K), ∀(neg a:Bool) (t:Multiplicative K),
      simpleStabilizerAction K p f (originalSimpleHom K neg a t)=
        originalSimpleHom K neg a (Multiplicative.ofAdd
          (((if neg then (c (if a then 1 else 0))⁻¹ else c (if a then 1 else 0):Kˣ):K)*tau t.toAdd)) := by
  classical
  obtain ⟨c,tau,d,hd,hrange,hpos⟩ := exists_positive_normalization K p f
  let F := postInner d (simpleStabilizerAction K p f)
  have hsigned (neg a:Bool) (t:K) : F (originalSimpleHom K neg a (Multiplicative.ofAdd t))=
      originalSimpleHom K neg a (Multiplicative.ofAdd (tau a t)) :=
    signed_parameter_action K p F a (tau a) (hrange true a) (hpos a) neg t
  have htau := normalized_common_field K F tau hsigned
  have hfield (a:Bool) : tau a=tau false := by
    cases a
    · rfl
    · exact htau.symm
  let C : Fin 2→Kˣ := fun i=>if i=0 then c false else c true
  have hC (a:Bool) : C (if a then 1 else 0)=c a := by
    cases a
    · rfl
    · exact if_neg (by decide)
  refine ⟨C,tau false,?_⟩
  intro neg a t
  rw [hC]
  let b : Kˣ := if neg then (c a)⁻¹ else c a
  have hcancel : (((if neg then c a else (c a)⁻¹ : Kˣ):K)*(b:K))=1 := by
    cases neg <;> simp only [b,Bool.false_eq_true,if_true,if_false,Units.val_inv_eq_inv_val]
    · exact inv_mul_cancel₀ (c a).ne_zero
    · exact mul_inv_cancel₀ (c a).ne_zero
  have hback : d*originalSimpleHom K neg a (Multiplicative.ofAdd ((b:K)*tau false t.toAdd))*d⁻¹=
      originalSimpleHom K neg a (Multiplicative.ofAdd (tau false t.toAdd)) := by
    have he := hd neg a ((b:K)*tau false t.toAdd)
    rw [←mul_assoc,hcancel,one_mul] at he
    exact he
  have he := hsigned neg a t.toAdd
  rw [hfield a] at he
  have heq := he.trans hback.symm
  change (MulAut.conj d) (simpleStabilizerAction K p f (originalSimpleHom K neg a t))=
    (MulAut.conj d) (originalSimpleHom K neg a (Multiplicative.ofAdd ((b:K)*tau false t.toAdd))) at heq
  exact (MulAut.conj d).injective heq

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalCommonField
