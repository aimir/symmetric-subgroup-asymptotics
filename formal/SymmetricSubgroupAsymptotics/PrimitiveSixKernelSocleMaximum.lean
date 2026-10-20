import SymmetricSubgroupAsymptotics.NonabelianSoclePartCenterless
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeNineSocleGenerators

/-! Socle types share a maximum across an actual commutative kernel and
an abelian-normal-free quotient. The quotient may have even order and
nonabelian simple factors; no coprime or splitting hypothesis is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSixKernelSocleMaximum

variable {G : Type} [Group G] [Finite G]

/-- The kernel-contained abelian socle and the injected nonabelian socle
use the same tuple coordinates. Bounds are on actual ambient normal
subgroups of the kernel and quotient, not on a replacement extension. -/
theorem socle_le_max (E : Subgroup G) [E.Normal] (hE : IsMulCommutative E)
    (t a : ℕ)
    (hkernel : ∀ H : Subgroup G, H.Normal → H ≤ E → MarkedC4.normalGen H ≤ t)
    (hnoabelian : ∀ L : Subgroup (G ⧸ E), L.Normal → IsMulCommutative L → L=⊥)
    (htop : ∀ L : Subgroup (G ⧸ E), L.Normal → MarkedC4.normalGen L ≤ a) :
    SocleNormalGeneratorBound G (max t a) := by
  let A := minimalNormalSoclePart G (fun M => IsMulCommutative M)
  let B := minimalNormalSoclePart G (fun M => ¬ IsMulCommutative M)
  have hAE : A ≤ E := by
    apply minimalNormalSoclePart_le_of
    intro M hM hc
    letI := hM.1
    let q := QuotientGroup.mk' E
    let L := M.map q
    have hL : L.Normal := hM.1.map q (QuotientGroup.mk'_surjective E)
    have hcL : IsMulCommutative L := by
      apply IsMulCommutative.of_comm
      rintro ⟨x,hx⟩ ⟨y,hy⟩
      rcases hx with ⟨g,hg,rfl⟩
      rcases hy with ⟨h,hh,rfl⟩
      apply Subtype.ext
      change q g * q h=q h * q g
      rw [← map_mul,← map_mul]
      exact congrArg q (congrArg Subtype.val (hc.is_comm.comm (⟨g,hg⟩ : M) ⟨h,hh⟩))
    have hz : M.map q=⊥ := hnoabelian L hL hcL
    have hm := (Subgroup.map_eq_bot_iff (H := M)).mp hz
    simpa only [q,QuotientGroup.ker_mk'] using hm
  have hBinf : B ⊓ E=⊥ := by
    simpa only [B,true_and] using
      nonabelianMinimalNormalSoclePart_inf_commutativeNormal_eq_bot
        (fun _ : Subgroup G => True) E hE
  have hA : MarkedC4.normalGen A ≤ t := hkernel A inferInstance hAE
  have hB : MarkedC4.normalGen B ≤ a := by
    have h := MarkedC4.normalGen_normal_le_inter_add_image B E
    rw [hBinf,MarkedC4.normalGen_bot,zero_add] at h
    exact h.trans (htop _ ((inferInstance : B.Normal).map _ (QuotientGroup.mk'_surjective E)))
  have hsplit : B ⊔ A=finiteGroupSocle G := by
    simpa only [B,A,not_not] using
      minimalNormalSoclePart_sup_compl_eq_finiteGroupSocle G (fun M => ¬ IsMulCommutative M)
  have hcommon : NoCommonNormalQuotient B A := by
    simpa only [B,A,true_and] using
      noCommonNormalQuotient_nonabelian_commutativeSocleParts G (fun _ => True)
  apply (socleNormalGeneratorBound_iff_normalGen_le G (max t a)).mpr
  rw [← hsplit]
  exact (normalGen_sup_le_max_of_noCommonNormalQuotient B A hcommon).trans (max_le (hB.trans (le_max_right t a)) (hA.trans (le_max_left t a)))

end SymmetricSubgroupAsymptotics.PrimitiveSixKernelSocleMaximum
