import SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckOriginalPositiveSemilinear
import SymmetricSubgroupAsymptotics.CFSGSubgroupConjugateOrbitCardinality

/-! An actual original inner torus removes both positive scalar constants
and preserves every signed simple range. The normalizing element has the
reciprocal signed action required to undo the normalization later. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPositiveScalarNormalization
open CFSGGTwoD4GeckOriginalPositiveSemilinear CFSGGTwoD4GeckOriginalSimpleStabilizer
open CFSGGTwoD4GeckOriginalSimpleParameters CFSGGTwoD4GeckOriginalProductTorusAction
open CFSGGTwoD4GeckProductTorusParameters CFSGGTwoD4GeckScalarTorus
open CFSGGTwoD4GeckProductTorus CFSG.Models.Chevalley
variable (K : Type) [Field K] [Finite K] [IsSimpleGroup (Projective CartanMatrix.G₂ K)]
variable (p : ℕ) [Fact p.Prime] [CharP K p]

def postInner {G : Type*} [Group G] (d : G) (f : MulAut G) : MulAut G := (MulAut.conj d)*f

theorem postInner_apply {G : Type*} [Group G] (d : G) (f : MulAut G) (x : G) :
    postInner d f x=d*f x*d⁻¹ := rfl

theorem exists_positive_normalization (f : simpleStabilizer K p) :
    ∃ (c : Bool → Kˣ) (tau : Bool → RingAut K) (d : Projective CartanMatrix.G₂ K),
      (∀(neg a:Bool) (t:K),d*originalSimpleHom K neg a (Multiplicative.ofAdd t)*d⁻¹=
        originalSimpleHom K neg a (Multiplicative.ofAdd
          (((if neg then c a else (c a)⁻¹ : Kˣ):K)*t))) ∧
      (∀(neg a:Bool),(originalSimpleHom K neg a).range.map
        (postInner d (simpleStabilizerAction K p f)).toMonoidHom=(originalSimpleHom K neg a).range) ∧
      (∀(a:Bool) (t:K),postInner d (simpleStabilizerAction K p f)
        (originalSimpleHom K false a (Multiplicative.ofAdd t))=
          originalSimpleHom K false a (Multiplicative.ofAdd (tau a t))) := by
  classical
  obtain ⟨c,tau,htau⟩ := positive_parameters_semilinear K p f
  let z : Fin 2 → Kˣ := fun i => if i=0 then (c false)⁻¹ else (c true)⁻¹
  let x := (scalarEquiv Kˣ).symm z
  let d := originalProductTorus K x
  have hx : CFSGIntegerMatrixPowerHom.powerHom (G:=Kˣ) relativeCartan x=z :=
    (scalarEquiv Kˣ).apply_symm_apply z
  have hs (neg a : Bool) : parameterScalar K x neg a = if neg then c a else (c a)⁻¹ := by
    unfold parameterScalar
    rw [hx]
    cases neg <;> cases a <;> simp only [z,if_true]
    all_goals norm_num
  have hd (neg a:Bool) (t:K) : d*originalSimpleHom K neg a (Multiplicative.ofAdd t)*d⁻¹=
      originalSimpleHom K neg a (Multiplicative.ofAdd
        (((if neg then c a else (c a)⁻¹ : Kˣ):K)*t)) := by
    have he := originalProductTorus_simple_action K x neg a t
    rw [hs,mul_comm t] at he
    exact he
  refine ⟨c,tau,d,hd,?_,?_⟩
  · intro neg a
    change (originalSimpleHom K neg a).range.map
      (((MulAut.conj d)*simpleStabilizerAction K p f).toMonoidHom)=_
    have hm : (originalSimpleHom K neg a).range.map
        (((MulAut.conj d)*simpleStabilizerAction K p f).toMonoidHom)=
        ((originalSimpleHom K neg a).range.map (simpleStabilizerAction K p f).toMonoidHom).map
          (MulAut.conj d).toMonoidHom := by rw [Subgroup.map_map]; rfl
    rw [hm,simple_preserves_chart K p f neg a]
    exact originalProductTorus_simple_range K x neg a
  · intro a t
    rw [postInner_apply,htau]
    calc
      _=originalSimpleHom K false a (Multiplicative.ofAdd
        ((((c a)⁻¹:Kˣ):K)*((c a:K)*tau a t))) := hd false a _
      _=originalSimpleHom K false a (Multiplicative.ofAdd (tau a t)) := by
        rw [Units.val_inv_eq_inv_val,inv_mul_cancel_left₀ (c a).ne_zero]

end SymmetricSubgroupAsymptotics.CFSGGTwoD4GeckPositiveScalarNormalization
