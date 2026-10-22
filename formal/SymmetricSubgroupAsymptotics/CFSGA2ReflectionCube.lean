import SymmetricSubgroupAsymptotics.CFSGNormTwoLatticeReflections
import Mathlib.Tactic.Module

/-! The A2 reflection cube on the original bilinear lattice. The proof
uses the four actual Cartan pairings, not a Weyl-group presentation. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGA2ReflectionCube
open CFSGNormTwoLatticeReflections
variable {V : Type*} [AddCommGroup V] (B : LinearMap.BilinForm ℤ V)

private theorem pair_formula (a b x : V) (hba : B b a= -1) :
    reflection B a (reflection B b x)=x-(B x a+B x b) • a-B x b • b := by
  simp only [reflection,map_sub,LinearMap.sub_apply,B.smul_left,hba,
    mul_neg_one,sub_neg_eq_add]
  module

theorem reflection_cube (a b : V) (haa : B a a=2) (hbb : B b b=2)
    (hab : B a b= -1) (hba : B b a= -1) (x : V) :
    reflection B a (reflection B b (reflection B a (reflection B b
      (reflection B a (reflection B b x)))))=x := by
  let t : V→V := fun y=>reflection B a (reflection B b y)
  have ht (y : V) : t y=y-(B y a+B y b) • a-B y b • b := pair_formula B a b y hba
  have hta : B (t x) a= -(B x a)-B x b := by
    rw [ht]
    simp only [map_sub,LinearMap.sub_apply,B.smul_left,haa,hba]
    ring
  have htb : B (t x) b=B x a := by
    rw [ht]
    simp only [map_sub,LinearMap.sub_apply,B.smul_left,hab,hbb]
    ring
  have ht2 : t (t x)=x-B x a • a-(B x a+B x b) • b := by
    rw [ht,hta,htb,ht]
    module
  have ht2a : B (t (t x)) a=B x b := by
    rw [ht2]
    simp only [map_sub,LinearMap.sub_apply,B.smul_left,haa,hba]
    ring
  have ht2b : B (t (t x)) b= -(B x a)-B x b := by
    rw [ht2]
    simp only [map_sub,LinearMap.sub_apply,B.smul_left,hab,hbb]
    ring
  change t (t (t x))=x
  rw [ht,ht2a,ht2b,ht2]
  module

end SymmetricSubgroupAsymptotics.CFSGA2ReflectionCube
