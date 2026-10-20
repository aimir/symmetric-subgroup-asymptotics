import SymmetricSubgroupAsymptotics.OriginalKernelElementaryChart
import Mathlib.GroupTheory.PGroup

/-! An original elementary-binary kernel cannot account for a surviving
cubic factor. Nonbinary original quotients therefore retain a cubic
factor in their actual residual linear top. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
variable {G B : Type} [Group G] [Group B]
  (pi : G →* B) (A : Rep.{0} (ZMod 2) B) (E : OriginalKernelModuleChart pi A)

include E in
theorem kernel_isPGroup_two : IsPGroup 2 pi.ker := by
  intro x
  obtain ⟨v,rfl⟩ := E.equiv.surjective x
  refine ⟨1,?_⟩
  apply Subtype.ext
  exact E.element_sq v.toAdd

include E in
theorem isPGroup_two_of_base (hB : IsPGroup 2 B) : IsPGroup 2 G := by
  intro x
  obtain ⟨n,hn⟩ := hB (pi x)
  have hk : x^(2^n)∈pi.ker := by change pi (x^(2^n))=1; rw [map_pow,hn]
  obtain ⟨m,hm⟩ := E.kernel_isPGroup_two pi A ⟨x^(2^n),hk⟩
  refine ⟨n+m,?_⟩
  have hh := congrArg Subtype.val hm
  simpa only [Subgroup.coe_pow,Subgroup.coe_one,← pow_mul,← pow_add] using hh

include E in
theorem three_dvd_base_of_nonbinary [Finite B] (k : ℕ)
    (hcard : Nat.card B∣2^k*3) (hG : ¬ IsPGroup 2 G) : 3∣Nat.card B := by
  by_contra h3
  have hc : Nat.Coprime (Nat.card B) 3 := (Nat.prime_three.coprime_iff_not_dvd.mpr h3).symm
  have hd : Nat.card B∣2^k := hc.dvd_mul_right.mp hcard
  have hB : IsPGroup 2 B := by
    intro x
    refine ⟨k,?_⟩
    obtain ⟨m,hm⟩ := hd
    rw [hm,pow_mul,pow_card_eq_one',one_pow]
  exact hG (E.isPGroup_two_of_base pi A hB)

end SymmetricSubgroupAsymptotics.OriginalKernelModuleChart
