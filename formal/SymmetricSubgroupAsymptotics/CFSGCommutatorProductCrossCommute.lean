import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-! A commutator of two paired products splits into the two literal
commutators when the two blocks commute across one another. -/
set_option autoImplicit false
set_option Elab.async false
open scoped commutatorElement
namespace SymmetricSubgroupAsymptotics.CFSGCommutatorProductCrossCommute

theorem commutator_mul_mul {G : Type*} [Group G] (a b c d : G)
    (hab : Commute a b) (had : Commute a d) (hbc : Commute b c) (hcd : Commute c d) :
    ⁅a*b,c*d⁆=⁅a,c⁆*⁅b,d⁆ := by
  have hiab : (a*b)⁻¹=a⁻¹*b⁻¹ := by rw [mul_inv_rev,hab.inv_inv.eq]
  have hicd : (c*d)⁻¹=c⁻¹*d⁻¹ := by rw [mul_inv_rev,hcd.inv_inv.eq]
  have hba : Commute b (a⁻¹*c⁻¹) := hab.symm.inv_right.mul_right hbc.inv_right
  have hda : Commute d (a⁻¹*c⁻¹) := had.symm.inv_right.mul_right hcd.symm.inv_right
  have hm : Commute (b*d) (a⁻¹*c⁻¹) := hba.mul_left hda
  simp only [commutatorElement_def]
  calc
    _ = ((a*b)*(c*d))*((a*b)⁻¹*(c*d)⁻¹) := by group
    _ = ((a*c)*(b*d))*((a⁻¹*c⁻¹)*(b⁻¹*d⁻¹)) := by
      rw [hiab,hicd,hbc.mul_mul_mul_comm a d,hbc.inv_inv.mul_mul_mul_comm a⁻¹ d⁻¹]
    _ = ((a*c)*(a⁻¹*c⁻¹))*((b*d)*(b⁻¹*d⁻¹)) :=
      hm.mul_mul_mul_comm (a*c) (b⁻¹*d⁻¹)
    _ = _ := by group

theorem conjugate_product_of_cross_commute {G : Type*} [Group G] (w v x y : G)
    (hwv : Commute w v) (hvx : Commute v x) (hwy : Commute w y) :
    (w*x*w⁻¹)*(v*y*v⁻¹)=(w*v)*(x*y)*(w*v)⁻¹ := by
  have hfixx : v*x*v⁻¹=x := by rw [hvx.eq];group
  have hfixy : w*y*w⁻¹=y := by rw [hwy.eq];group
  have hx : (w*v)*x*(w*v)⁻¹=w*x*w⁻¹ := by
    calc
      _ = w*(v*x*v⁻¹)*w⁻¹ := by group
      _ = _ := by rw [hfixx]
  have hy : (w*v)*y*(w*v)⁻¹=v*y*v⁻¹ := by
    rw [hwv.eq]
    calc
      _ = v*(w*y*w⁻¹)*v⁻¹ := by group
      _ = _ := by rw [hfixy]
  calc
    _ = ((w*v)*x*(w*v)⁻¹)*((w*v)*y*(w*v)⁻¹) := by rw [hx,hy]
    _ = _ := by group

end SymmetricSubgroupAsymptotics.CFSGCommutatorProductCrossCommute
