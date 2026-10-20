import SymmetricSubgroupAsymptotics.ElementaryKernelIntersectionFiltration
import SymmetricSubgroupAsymptotics.IntertwiningProjectorRank

/-! The actual binary kernel intersection inherits cubic projector ranks
from the exact original retained-kernel chart, with its original acting
element. No replacement quotient or abstract capacity is introduced. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart

variable {Q B D : Type} [Group Q] [Group B] [Group D]
  {eta : Q →* D} {A : Rep (ZMod 2) D}
  (E : OriginalKernelModuleChart eta A) (pi : Q →* B)
  {K : Rep.{0} (ZMod 2) B} (F : OriginalKernelModuleChart pi K)
  [FiniteDimensional (ZMod 2) A] [FiniteDimensional (ZMod 2) K]

include F in
theorem kernelIntersection_active_rank_le (a : Q) :
    Module.finrank (ZMod 2) (LinearMap.range
      ((E.kernelIntersection pi).toRepresentation a+
        ((E.kernelIntersection pi).toRepresentation a)^2))≤
    Module.finrank (ZMod 2) (LinearMap.range (K.ρ (pi a)+(K.ρ (pi a))^2)) := by
  let j := E.kernelIntersectionIntertwiner pi F
  apply IntertwiningProjectorRank.rank_le j.toLinearMap
    (E.kernelIntersectionIntertwiner_injective pi F)
  intro v
  have hj : ∀ w, j ((E.kernelIntersection pi).toRepresentation a w)=K.ρ (pi a) (j w) := by
    intro w
    exact LinearMap.congr_fun (j.isIntertwining' a) w
  change j (_+_)=_+_
  rw [map_add,hj]
  change _+j ((E.kernelIntersection pi).toRepresentation a
      ((E.kernelIntersection pi).toRepresentation a v))=_+_
  rw [hj,hj]
  rfl

include F in
theorem kernelIntersection_fixed_projector_rank_le (a : Q) :
    Module.finrank (ZMod 2) (LinearMap.range
      (1+(E.kernelIntersection pi).toRepresentation a+
        ((E.kernelIntersection pi).toRepresentation a)^2))≤
    Module.finrank (ZMod 2) (LinearMap.range (1+K.ρ (pi a)+(K.ρ (pi a))^2)) := by
  let j := E.kernelIntersectionIntertwiner pi F
  apply IntertwiningProjectorRank.rank_le j.toLinearMap
    (E.kernelIntersectionIntertwiner_injective pi F)
  intro v
  have hj : ∀ w, j ((E.kernelIntersection pi).toRepresentation a w)=K.ρ (pi a) (j w) := by
    intro w
    exact LinearMap.congr_fun (j.isIntertwining' a) w
  change j ((_+_)+_)=(_+_)+_
  rw [map_add,map_add,hj]
  change (_+_)+j ((E.kernelIntersection pi).toRepresentation a
      ((E.kernelIntersection pi).toRepresentation a v))=(_+_)+_
  rw [hj,hj]
  rfl

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
