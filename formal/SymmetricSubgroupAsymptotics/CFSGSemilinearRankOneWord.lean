import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.TypeTags.Hom

/-! Group-only interfaces for projected rank-one words. They keep the
abstract word algebra separate from large original-model quotient types. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSemilinearRankOneWord

theorem map_rank_one_word {H G : Type*} [Group H] [Group G] (pi : H→*G) (x y : H) :
    pi (x*y⁻¹*x)=pi x*(pi y)⁻¹*pi x := by rw [map_mul,map_mul,map_inv]

theorem map_three {H G : Type*} [Group H] [Group G] (pi : H→*G) (x y z : H) :
    pi (x*y*z)=pi x*pi y*pi z := by rw [map_mul,map_mul]

theorem image_rank_one_word {K G : Type*} [Field K] [Group G]
    (u v : Multiplicative K→*G) (f : G→*G) (tau : RingAut K) (t : Kˣ)
    (hpos : ∀a,f (u (Multiplicative.ofAdd a))=u (Multiplicative.ofAdd ((t : K)*tau a)))
    (hneg : ∀a,f (v (Multiplicative.ofAdd a))=v (Multiplicative.ofAdd ((t : K)⁻¹*tau a))) :
    f (u (Multiplicative.ofAdd 1)*(v (Multiplicative.ofAdd 1))⁻¹*u (Multiplicative.ofAdd 1))=
      u (Multiplicative.ofAdd (t : K))*v (Multiplicative.ofAdd (-(t : K)⁻¹))*u (Multiplicative.ofAdd (t : K)) := by
  have hp : f (u (Multiplicative.ofAdd 1))=u (Multiplicative.ofAdd (t : K)) := by
    simpa only [map_one,mul_one] using hpos 1
  have hn : f (v (Multiplicative.ofAdd 1))=v (Multiplicative.ofAdd ((t : K)⁻¹)) := by
    simpa only [map_one,mul_one] using hneg 1
  rw [map_mul,map_mul,map_inv,hp,hn]
  have hi : (v (Multiplicative.ofAdd ((t : K)⁻¹)))⁻¹=v (Multiplicative.ofAdd (-(t : K)⁻¹)) :=
    (map_inv v (Multiplicative.ofAdd ((t : K)⁻¹))).symm
  rw [hi]

theorem image_eq_torus_mul {H G : Type*} [Group H] [Group G]
    (pi : H→*G) (f : G→*G) (S W : H) (he : f (pi W)=pi S) :
    f (pi W)=pi (S*W⁻¹)*pi W := by
  rw [he,map_mul,map_inv,mul_assoc,inv_mul_cancel,mul_one]

end SymmetricSubgroupAsymptotics.CFSGSemilinearRankOneWord
