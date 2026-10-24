import SymmetricSubgroupAsymptotics.CFSGSerrePositiveLowestWeight

/-! A sparse original-source identity can be proved from a matrix image
once only its opposite lowering is in an already faithful subspace.
The whole rational representation is not assumed injective. This is the
height-induction step for proving a finite original root-family span. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSerreWeightImageCriterion
open CFSG.Models.Chevalley CFSGSerreSignedRootWeights CFSGSerrePositiveLowestWeight
variable {r:ℕ} (A:Matrix (Fin r) (Fin r) ℤ)
local notation "L" => RationalLie A
variable {M:Type*} [LieRing M] [LieAlgebra ℚ M]

theorem eq_zero_of_image_zero_of_lowering_mem
    (f:L→ₗ⁅ℚ⁆M) (W:Submodule ℚ L) (hinj:Set.InjOn f (W:Set L))
    (neg:Bool) (i:Fin r) (hii:A i i=2) (v:L) (mu:ℚ) (hmu:0<mu)
    (hw:⁅coroot A neg i,v⁆=mu • v) (hv:f v=0)
    (hl:⁅oppositeVector A neg i,v⁆∈W) : v=0 := by
  apply eq_zero_of_positive_weight_of_opposite_zero A neg i hii v mu hmu hw
  apply hinj hl W.zero_mem
  rw [LieHom.map_lie,hv,lie_zero,map_zero]

theorem eq_of_image_eq_of_lowerings_mem
    (f:L→ₗ⁅ℚ⁆M) (W:Submodule ℚ L) (hinj:Set.InjOn f (W:Set L))
    (neg:Bool) (i:Fin r) (hii:A i i=2) (x y:L) (mu:ℚ) (hmu:0<mu)
    (hx:⁅coroot A neg i,x⁆=mu • x) (hy:⁅coroot A neg i,y⁆=mu • y)
    (he:f x=f y) (hxl:⁅oppositeVector A neg i,x⁆∈W)
    (hyl:⁅oppositeVector A neg i,y⁆∈W) : x=y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_image_zero_of_lowering_mem A f W hinj neg i hii (x-y) mu hmu
  · rw [lie_sub,hx,hy,smul_sub]
  · rw [map_sub,he,sub_self]
  · rw [lie_sub]
    exact W.sub_mem hxl hyl

end SymmetricSubgroupAsymptotics.CFSGSerreWeightImageCriterion
