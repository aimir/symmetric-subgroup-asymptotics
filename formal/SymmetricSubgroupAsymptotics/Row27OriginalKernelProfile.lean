import SymmetricSubgroupAsymptotics.Row27OriginalKernelCertificate
import SymmetricSubgroupAsymptotics.BinaryThreeBlockSignShearUniform
import SymmetricSubgroupAsymptotics.ElementaryBinaryKernelOriginalChart
import SymmetricSubgroupAsymptotics.OriginalKernelModuleCoordinateEmbedding
import SymmetricSubgroupAsymptotics.OriginalKernelUniformRelativeHead
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.Row27OriginalKernelProfile
open Row27OriginalQuartetFrame
open BinaryPlaneThreeTranslations (Model)
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
private def rangeMap : frame.top.ker →* Row27BinaryPlaneKernelModel.action.range :=
  (Row27Top.subtype.comp frame.top.ker.subtype).codRestrict _
    Row27OriginalKernelCertificate.kernel_mem
private def modelEquiv : Model ≃* Row27BinaryPlaneKernelModel.action.range :=
  MonoidHom.ofInjective Row27BinaryPlaneKernelModel.action_injective
 def coordinates : frame.top.ker →* Model := modelEquiv.symm.toMonoidHom.comp rangeMap
 theorem coordinates_injective : Function.Injective coordinates := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have he := congrArg modelEquiv h
  have hv := congrArg (fun z : Row27BinaryPlaneKernelModel.action.range => z.val) he
  simpa [coordinates,rangeMap] using hv
 theorem coordinates_points (k : frame.top.ker) :
    Row27BinaryPlaneKernelModel.action (coordinates k)=(k.val : Equiv.Perm (Fin 12)) := by
  change (modelEquiv (modelEquiv.symm (rangeMap k))).val=_
  rw [modelEquiv.apply_symm_apply]
  rfl
 theorem square (k : frame.top.ker) : k^2=1 := by
  apply coordinates_injective
  rw [map_pow,map_one]
  have h : ∀ v : Model,v^2=1 := by decide +kernel
  exact h _
 theorem binary_group : IsPGroup 2 frame.top.ker := by
  have hM : IsPGroup 2 Model := by
    apply IsPGroup.of_card (n:=6)
    change Nat.card (Fin 3 → Fin 2 → ZMod 2)=2^6
    norm_num [Nat.card_eq_fintype_card]
  exact hM.of_injective coordinates coordinates_injective
 theorem commutative : IsMulCommutative frame.top.ker := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply coordinates_injective
  simp only [map_mul,mul_comm]
abbrev ActualR := ElementaryBinaryKernelOriginalChart.kernelModule frame.top top_surjective square
local instance : Finite ActualR := by
  change Finite (Additive frame.top.ker)
  infer_instance
local instance : FiniteDimensional (ZMod 2) ActualR := Module.Finite.of_finite
 def actualChart : OriginalKernelModuleChart frame.top ActualR :=
  ElementaryBinaryKernelOriginalChart.originalChart frame.top top_surjective square
abbrev AmbientR : Rep (ZMod 2) (Equiv.Perm (Fin 3)) := Rep.of BinaryThreeBlockSignShearUniform.rho
private theorem section_points : ∀ (p : Equiv.Perm (Fin 3)) (v : Model),
    Row27BinaryPlaneKernelModel.action (Multiplicative.ofAdd (AmbientR.ρ p v.toAdd))=
      (Row27OriginalKernelCertificate.liftSection p : Equiv.Perm (Fin 12))*
      Row27BinaryPlaneKernelModel.action v*
      (Row27OriginalKernelCertificate.liftSection p : Equiv.Perm (Fin 12))⁻¹ := by
  decide +kernel
private theorem coordinate_conjugate (p : Equiv.Perm (Fin 3)) (k : frame.top.ker) :
    coordinates (MulAut.conjNormal (Row27OriginalKernelCertificate.liftSection p) k)=
      Multiplicative.ofAdd (AmbientR.ρ p (coordinates k).toAdd) := by
  apply Row27BinaryPlaneKernelModel.action_injective
  rw [coordinates_points,section_points,coordinates_points]
  rfl
 def intertwiner : Representation.IntertwiningMap ActualR.ρ AmbientR.ρ :=
  actualChart.coordinateIntertwiner frame.top ActualR AmbientR coordinates
    Row27OriginalKernelCertificate.liftSection Row27OriginalKernelCertificate.section_top
    coordinate_conjugate
 theorem uniform_two : UniformSubrepresentationGeneratorBound ActualR.ρ 2 :=
  BinaryThreeBlockSignShearUniform.uniform_two.of_injective intertwiner
    (actualChart.coordinateLinear_injective frame.top ActualR AmbientR coordinates coordinates_injective)
 theorem relative_rank (L : Subgroup Row27Top) [L.Normal] (hL : L≤frame.top.ker) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 L)≤2 :=
  actualChart.relative_head_le_of_uniform frame.top ActualR top_surjective 2 uniform_two L hL
end SymmetricSubgroupAsymptotics.Row27OriginalKernelProfile
