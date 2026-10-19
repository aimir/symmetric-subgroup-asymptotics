import SymmetricSubgroupAsymptotics.LinearSemidirectSubgroupKernelChart
import SymmetricSubgroupAsymptotics.Non2LiftBound

/-! The original kernel chart of an arbitrary actual affine subgroup over
its surjective actual linear image, with its correlated translation-space
inclusion. This does not require a complement or a full translation module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
open LinearSemidirectCoprimeSocleBounds LinearSemidirectSubgroupKernelChart

variable {p : ℕ} [Fact p.Prime] {R V : Type} [Group R]
  [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V]
  (rho : R →* (V ≃ₗ[ZMod p] V)) (K : Subgroup (Model rho))

abbrev top : K →* Image rho K := (projection rho K).rangeRestrict

def kernelCast : kernel rho K ≃* (top rho K).ker where
  toFun x := ⟨x.val,Subtype.ext x.property⟩
  invFun x := ⟨x.val,congrArg Subtype.val x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem quotientEquiv_mk (g : K) :
    quotientEquiv rho K (QuotientGroup.mk' (kernel rho K) g)=top rho K g := rfl

@[simp] theorem quotientEquiv_symm_top (g : K) :
    (quotientEquiv rho K).symm (top rho K g)=QuotientGroup.mk' (kernel rho K) g := by
  rw [← quotientEquiv_mk rho K g,MulEquiv.symm_apply_apply]

abbrev kernelModule : Rep (ZMod p) (Image rho K) :=
  Rep.of ((show Representation (ZMod p) (K ⧸ kernel rho K) (translationSpace rho K) from
    (chart rho K).quotientRepresentation.ρ).comp (quotientEquiv rho K).symm.toMonoidHom)

def originalKernelChart : OriginalKernelModuleChart (top rho K) (kernelModule rho K) where
  equiv := (kernelEquiv rho K).symm.trans (kernelCast rho K)
  conjugate g a := by
    change ((kernelEquiv rho K).symm
      (Multiplicative.ofAdd ((chart rho K).quotientRepresentation.ρ
        ((quotientEquiv rho K).symm (top rho K g)) a)) : K)=
      g * ((kernelEquiv rho K).symm (Multiplicative.ofAdd a) : K) * g⁻¹
    rw [quotientEquiv_symm_top]
    let x : kernel rho K := (kernelEquiv rho K).symm (Multiplicative.ofAdd a)
    have hx : ((chart rho K).equiv x).toAdd=a :=
      congrArg Multiplicative.toAdd ((kernelEquiv rho K).apply_symm_apply _)
    have h := (chart rho K).quotientRepresentation_apply g x
    rw [hx] at h
    have hc := congrArg (fun v : translationSpace rho K =>
      ((kernelEquiv rho K).symm (Multiplicative.ofAdd v) : K)) h
    change ((kernelEquiv rho K).symm (Multiplicative.ofAdd
      ((chart rho K).quotientRepresentation.ρ
        (QuotientGroup.mk' (kernel rho K) g) a)) : K)=
      ((kernelEquiv rho K).symm
        ((kernelEquiv rho K) (MulAut.conjNormal g x)) : K) at hc
    rw [MulEquiv.symm_apply_apply] at hc
    exact hc

/-- The correlated kernel injects into the actual linear image's full
module, equivariantly for that same actual image. -/
def inclusion :
    Representation.IntertwiningMap (A := ZMod p)
      (V := translationSpace rho K) (W := V) (kernelModule rho K).ρ
      (LinearSemidirectSubgroupKernelChart.imageRepresentation rho K) where
  toLinearMap := (translationSpace rho K).subtype
  isIntertwining' l := by
    apply LinearMap.ext
    intro v
    obtain ⟨g,rfl⟩ := (projection rho K).rangeRestrict_surjective l
    change Subtype.val (p := fun v : V => v ∈ translationSpace rho K)
      ((chart rho K).quotientRepresentation.ρ
        ((quotientEquiv rho K).symm (top rho K g)) v)=
        rho (projection rho K g) (v : V)
    rw [quotientEquiv_symm_top]
    exact Representation.IntertwiningMap.isIntertwining _ _
      (LinearSemidirectSubgroupKernelChart.inclusion rho K) g v

theorem inclusion_injective : Function.Injective (inclusion rho K) := by
  intro x y h
  apply Subtype.ext
  change (x : V)=(y : V) at h
  exact h

end SymmetricSubgroupAsymptotics.LinearSemidirectActualImageKernelChart
