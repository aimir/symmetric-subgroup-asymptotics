import Mathlib.GroupTheory.Sylow

/-! An automorphism preserving an actual opposite Sylow pair has Weyl
displacement in the normalizer of that same ordered pair. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Pointwise
namespace SymmetricSubgroupAsymptotics.CFSGRankOneWeylDisplacement
variable {G : Type*} [Group G] {p : ℕ}

theorem mem_pair_normalizer (P : Sylow p G) (w : G) (hw : w⁻¹=w)
    (f : MulAut G) (hfP : f • P=P) (hfO : f • (w • P)=w • P) :
    f w*w⁻¹∈Subgroup.normalizer (P : Set G) ⊓
      Subgroup.normalizer ((w • P : Sylow p G) : Set G) := by
  have hfw : (f w)⁻¹=f w := by rw [←map_inv,hw]
  have hcomm : f*MulAut.conj w=MulAut.conj (f w)*f := by
    apply MulEquiv.ext
    intro x
    change f (w*x*w⁻¹)=f w*f x*(f w)⁻¹
    simp only [map_mul,map_inv]
  have hs : (f w) • P=w • P := by
    calc
      (f w) • P=(MulAut.conj (f w)) • (f • P) := by rw [hfP]; rfl
      _ = (f*MulAut.conj w) • P := by rw [hcomm,mul_smul]
      _ = f • (w • P) := mul_smul f (MulAut.conj w) P
      _ = w • P := hfO
  have hback : (f w) • (w • P)=P := by
    have hh := inv_smul_smul (f w) P
    rw [hfw,hs] at hh
    exact hh
  have htP : (f w*w⁻¹) • P=P := by rw [mul_smul,hw,hback]
  have htO : (f w*w⁻¹) • (w • P)=w • P := by
    rw [mul_smul,inv_smul_smul,hs]
  exact ⟨Sylow.smul_eq_iff_mem_normalizer.mp htP,
    Sylow.smul_eq_iff_mem_normalizer.mp htO⟩

end SymmetricSubgroupAsymptotics.CFSGRankOneWeylDisplacement
