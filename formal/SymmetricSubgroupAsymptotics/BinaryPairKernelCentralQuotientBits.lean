import SymmetricSubgroupAsymptotics.BinaryPairArbitraryNormalCenter

/-! A central quotient element already in the original pair kernel gives
an actual fixed vector modulo the same normal intersection. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} {w : ℕ} {U : Subgroup (Equiv.Perm X)} (F : BinaryPairFrame U (Fin w))

theorem kernel_central_quotient_bits_displacement
    (N : Subgroup U) [N.Normal] (z : F.top.ker)
    (hz : QuotientGroup.mk' N (z : U)∈Subgroup.center (U ⧸ N)) (t : F.top.range) :
    F.coordinateTopAction t (F.bits z)-F.bits z∈F.ambientAxis N := by
  obtain ⟨u,rfl⟩ := F.top.rangeRestrict_surjective t
  let q := QuotientGroup.mk' N
  have hc := Subgroup.mem_center_iff.mp hz (q u)
  change q u*q (z : U)=q (z : U)*q u at hc
  have he : q ((z : U)⁻¹*(u*(z : U)*u⁻¹))=1 := by
    simp only [map_mul,map_inv]
    rw [hc]
    simp [mul_assoc]
  have hm : ((z⁻¹*MulAut.conjNormal u z : F.top.ker) : U)∈N :=
    (QuotientGroup.eq_one_iff _).mp he
  have hv := (F.bits_mem_ambientAxis N (z⁻¹*MulAut.conjNormal u z)).mpr hm
  rwa [F.bits_commutator] at hv

end SymmetricSubgroupAsymptotics.BinaryPairFrame
