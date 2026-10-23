import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-! Literal opposite-Sylow pair geometry for actual group automorphisms.
The statements keep both original subgroups and the original involution. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGRankOnePairAutomorphisms
variable {G : Type*} [Group G]

theorem map_pair_normalizer (U V : Subgroup G) (f : MulAut G)
    (hU : U.map f.toMonoidHom=U) (hV : V.map f.toMonoidHom=V) :
    (Subgroup.normalizer (U:Set G) ⊓ Subgroup.normalizer (V:Set G)).map f.toMonoidHom=
      Subgroup.normalizer (U:Set G) ⊓ Subgroup.normalizer (V:Set G) := by
  rw [Subgroup.map_inf _ _ _ f.injective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective,
    Subgroup.map_normalizer_eq_of_bijective _ f.bijective,hU,hV]

theorem weyl_displacement_mem_pair_normalizer {p : ℕ} (P : Sylow p G) (w : G)
    (hSquare : w*w=1) (f : MulAut G) (hfP : f • P=P) (hfO : f • (w • P)=w • P) :
    f w*w⁻¹∈Subgroup.normalizer (P:Set G) ⊓
      Subgroup.normalizer ((P:Subgroup G).map (MulAut.conj w).toMonoidHom:Set G) := by
  have hw : w⁻¹=w := inv_eq_of_mul_eq_one_right hSquare
  have hfw : (f w)⁻¹=f w := by rw [←map_inv,hw]
  have hcomm : f*MulAut.conj w=MulAut.conj (f w)*f := by
    apply MulEquiv.ext
    intro x
    change f (w*x*w⁻¹)=f w*f x*(f w)⁻¹
    simp only [map_mul,map_inv]
  have hs : (f w) • P=w • P := by
    calc
      (f w) • P=(MulAut.conj (f w)) • (f • P) := by rw [hfP]; rfl
      _=(f*MulAut.conj w) • P := by rw [hcomm,mul_smul]
      _=f • (w • P) := mul_smul f (MulAut.conj w) P
      _=w • P := hfO
  have hback : (f w) • (w • P)=P := by
    have hh := inv_smul_smul (f w) P
    rw [hfw,hs] at hh
    exact hh
  have htP : (f w*w⁻¹) • P=P := by rw [mul_smul,hw,hback]
  have htO : (f w*w⁻¹) • (w • P)=w • P := by rw [mul_smul,inv_smul_smul,hs]
  exact ⟨Sylow.smul_eq_iff_mem_normalizer.mp htP,Sylow.smul_eq_iff_mem_normalizer.mp htO⟩


end SymmetricSubgroupAsymptotics.CFSGRankOnePairAutomorphisms
