import SymmetricSubgroupAsymptotics.Non2LiftBound
import SymmetricSubgroupAsymptotics.ElementaryBinaryKernelOriginalChart
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G B : Type} [Group G] [Group B] (pi : G →* B)
    (R A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi R)
    (f : pi.ker →* Multiplicative A)
 def coordinateLinear : R →ₗ[ZMod 2] A :=
  ({ toFun := fun v => (f (E.equiv (Multiplicative.ofAdd v))).toAdd
     map_zero' := by simp
     map_add' := by
       intro v w
       change (f (E.equiv (Multiplicative.ofAdd v*Multiplicative.ofAdd w))).toAdd=_
       rw [map_mul,map_mul]
       rfl } : R →+ A).toZModLinearMap 2
 theorem coordinateLinear_injective (hf : Function.Injective f) :
    Function.Injective (E.coordinateLinear pi R A f) := by
  intro v w h
  apply Multiplicative.ofAdd.injective
  apply E.equiv.injective
  apply hf
  exact Multiplicative.toAdd.injective h
 def coordinateIntertwiner (r : B → G) (hr : ∀ b,pi (r b)=b)
    (hc : ∀ (b : B) (k : pi.ker),
      f (MulAut.conjNormal (r b) k)=Multiplicative.ofAdd (A.ρ b (f k).toAdd)) :
    Representation.IntertwiningMap R.ρ A.ρ where
  toLinearMap := E.coordinateLinear pi R A f
  isIntertwining' b := by
    apply LinearMap.ext
    intro v
    change (f (E.equiv (Multiplicative.ofAdd (R.ρ b v)))).toAdd=
      A.ρ b (f (E.equiv (Multiplicative.ofAdd v))).toAdd
    have he : E.equiv (Multiplicative.ofAdd (R.ρ b v))=
        MulAut.conjNormal (r b) (E.equiv (Multiplicative.ofAdd v)) := by
      apply Subtype.ext
      have h := E.conjugate (r b) v
      rw [hr] at h
      exact h
    rw [he,hc]
    rfl
end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
