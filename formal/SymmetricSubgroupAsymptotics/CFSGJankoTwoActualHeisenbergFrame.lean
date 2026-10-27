import SymmetricSubgroupAsymptotics.CFSGJankoTwoSelectedMatrixIdentities
import Mathlib.Algebra.Group.Units.Hom

/-! Actual Heisenberg27/Singer frame in the ORIGINAL five-relator J2 carrier. Simplicity is inherited from that same carrier only. The concrete matrix homomorphism is nontrivial and hence injective; no target model identity, target simplicity, whole-group order, h-order or extra index/generation premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGJankoTwoActualHeisenbergFrame
open CFSGJankoTwoSelectedPositiveWords CFSGJankoTwoSelectedMatrixIdentities
abbrev Original := CFSG.Models.Presentations.J2.Model
private def oldA : Original := PresentedGroup.of (0 : Fin 2)
private def oldB : Original := PresentedGroup.of (1 : Fin 2)

def rho : Original →* Image :=
  JankoTwoStandardPairPresentationEquivalence.representation unitA unitB
    unitA_square unitB_cube product_seventh commutator_twelfth last_relator

theorem rho_first : rho oldA=unitA :=
  JankoTwoStandardPairPresentationEquivalence.representation_of_zero unitA unitB
    unitA_square unitB_cube product_seventh commutator_twelfth last_relator

theorem rho_second : rho oldB=unitB :=
  JankoTwoStandardPairPresentationEquivalence.representation_of_one unitA unitB
    unitA_square unitB_cube product_seventh commutator_twelfth last_relator

theorem rho_injective [IsSimpleGroup Original] : Function.Injective rho :=
  JankoTwoStandardPairPresentationEquivalence.representation_injective unitA unitB
    unitA_square unitB_cube product_seventh commutator_twelfth last_relator unitA_ne_one

private theorem rho_x : rho (node021 oldA oldB)=nativeFrame.x := by
  change rho (node021 oldA oldB)=(node021 unitA unitB)
  simpa only [rho_first,rho_second] using (map_node021 rho oldA oldB)

private theorem rho_y : rho (node027 oldA oldB)=nativeFrame.y := by
  change rho (node027 oldA oldB)=(node027 unitA unitB)
  simpa only [rho_first,rho_second] using (map_node027 rho oldA oldB)

private theorem rho_z : rho (node035 oldA oldB)=nativeFrame.z := by
  change rho (node035 oldA oldB)=(node035 unitA unitB)
  simpa only [rho_first,rho_second] using (map_node035 rho oldA oldB)

private theorem rho_h : rho (node029 oldA oldB)=nativeFrame.h := by
  change rho (node029 oldA oldB)=(node029 unitA unitB)
  simpa only [rho_first,rho_second] using (map_node029 rho oldA oldB)

def frame [IsSimpleGroup Original] : TernaryHeisenbergSingerGeneratorFrame.Frame Original where
  x := (node021 oldA oldB)
  y := (node027 oldA oldB)
  z := (node035 oldA oldB)
  h := (node029 oldA oldB)
  x_cube := by
    apply rho_injective
    rw [map_pow,map_one,rho_x]
    exact nativeFrame.x_cube
  y_cube := by
    apply rho_injective
    rw [map_pow,map_one,rho_y]
    exact nativeFrame.y_cube
  z_cube := by
    apply rho_injective
    rw [map_pow,map_one,rho_z]
    exact nativeFrame.z_cube
  commute_xz := by
    change (node021 oldA oldB)*(node035 oldA oldB)=(node035 oldA oldB)*(node021 oldA oldB)
    apply rho_injective
    simp only [map_mul,rho_x,rho_z]
    exact nativeFrame.commute_xz.eq
  commute_yz := by
    change (node027 oldA oldB)*(node035 oldA oldB)=(node035 oldA oldB)*(node027 oldA oldB)
    apply rho_injective
    simp only [map_mul,rho_y,rho_z]
    exact nativeFrame.commute_yz.eq
  collect := by
    apply rho_injective
    simp only [map_mul,rho_y,rho_x,rho_z]
    exact nativeFrame.collect
  central_ne_one := by
    intro he
    apply nativeFrame.central_ne_one
    exact rho_z.symm.trans ((congrArg rho he).trans (map_one rho))
  singer_x := by
    apply rho_injective
    simp only [map_mul,map_inv,map_pow,rho_h,rho_x,rho_y,rho_z]
    exact nativeFrame.singer_x
  singer_y := by
    apply rho_injective
    simp only [map_mul,map_inv,map_pow,rho_h,rho_x,rho_y,rho_z]
    exact nativeFrame.singer_y
  singer_z := by
    apply rho_injective
    simp only [map_mul,map_inv,map_pow,rho_h,rho_x,rho_y,rho_z]
    exact nativeFrame.singer_z

end SymmetricSubgroupAsymptotics.CFSGJankoTwoActualHeisenbergFrame
