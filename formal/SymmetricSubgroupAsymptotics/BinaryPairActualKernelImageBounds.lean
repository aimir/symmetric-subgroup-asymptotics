import SymmetricSubgroupAsymptotics.BinaryPairLargeSectionCharacter
import SymmetricSubgroupAsymptotics.BinaryPairKernelCard
import SymmetricSubgroupAsymptotics.NormalKernelIntersectionCard
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadSurjectiveKernel

/-! Bounds on the actual correlated pair-kernel image in the SAME normal
quotient. A nonzero top image is paid by the existing large-section
faithfulness theorem; a large zero-top denominator is paid by exact order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
local instance actualKernelImageBoundsPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

theorem zeroCutBase_kernel_eq_actual_kernel_image (N : Subgroup U) [N.Normal] :
    (F.zeroCutBase N).ker=F.top.ker.map (QuotientGroup.mk' N) := by
  ext x
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective N x
  rw [MonoidHom.mem_ker,F.zeroCutBase_apply]
  change (u : U ⧸ (F.top.ker⊔N))=1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change u∈F.top.ker⊔N ↔ u∈(F.top.ker.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N)
  rw [Subgroup.comap_map_eq,QuotientGroup.ker_mk']

theorem actual_kernel_image_card_eq_section (N : Subgroup U) [N.Normal] :
    Nat.card (F.top.ker.map (QuotientGroup.mk' N))=
      Nat.card (F.kernelSpace ⧸ F.normalSpace N) := by
  rw [←F.zeroCutBase_kernel_eq_actual_kernel_image N]
  exact (Nat.card_congr (F.sectionKernelEquiv N).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem moving_normal_kernel_image_card_le_half
    [MulAction.IsPretransitive U X] (hU : IsPGroup 2 U)
    (x : Fin w) (N : Subgroup U) [N.Normal] (hN : ¬N≤F.top.ker) :
    Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤2^(w/2) := by
  letI : MulAction.IsPretransitive F.top.range (Fin w) := F.top_pretransitive
  have hd : Module.finrank (ZMod 2) (F.kernelSpace ⧸ F.normalSpace N)≤w/2 := by
    by_contra hh
    apply hN
    apply F.normal_le_top_ker_of_large N hU x
    norm_num only [Nat.card_fin]
    omega
  rw [F.actual_kernel_image_card_eq_section N]
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F.kernelSpace ⧸ F.normalSpace N)
  rw [Nat.card_zmod] at hc
  rw [hc]
  exact Nat.pow_le_pow_right (by decide : 0<2) hd

theorem large_kernel_normal_image_card_le
    (N : Subgroup U) [N.Normal] (hN : N≤F.top.ker)
    (a b c : ℕ) (ha : a≤Nat.card N) (hK : Nat.card F.kernelSpace≤b)
    (hnum : b≤a*c) : Nat.card (F.top.ker.map (QuotientGroup.mk' N))≤c := by
  have hcard := subgroup_card_eq_map_mul_kernel_intersection (QuotientGroup.mk' N) F.top.ker
  rw [QuotientGroup.ker_mk',inf_eq_right.mpr hN] at hcard
  have hk : Nat.card F.top.ker=Nat.card F.kernelSpace :=
    (Nat.card_congr F.kernelChart.toEquiv).trans (Nat.card_congr Multiplicative.toAdd)
  have hp : 0<Nat.card N := Nat.card_pos
  rw [hk] at hcard
  have hm : Nat.card (F.top.ker.map (QuotientGroup.mk' N))*Nat.card N≤c*Nat.card N := by
    calc
      _ = Nat.card F.kernelSpace := hcard.symm
      _ ≤ b := hK
      _ ≤ a*c := hnum
      _ ≤ Nat.card N*c := Nat.mul_le_mul_right c ha
      _ = c*Nat.card N := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hm hp
end SymmetricSubgroupAsymptotics.BinaryPairFrame
