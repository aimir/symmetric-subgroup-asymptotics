import SymmetricSubgroupAsymptotics.BinaryPairArbitraryNormalCenter
import SymmetricSubgroupAsymptotics.QuotientSubgroupProjectionCard

/-! A proper normal-image centralizer is measured in the SAME original
pair coordinates. Only an actual kernel layer and an actual selected top
lift must lie in D; no zero-offset or split-extension assumption is used
for this bound. The original normal N may have a nonzero top image. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame
variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

private theorem properF_displacement_axis
    (D N : Subgroup U) [N.Normal]
    (u : U) (hu : QuotientGroup.mk' N u ∈
      Subgroup.centralizer (D.map (QuotientGroup.mk' N) : Set (U ⧸ N)))
    (k : F.top.ker) (hk : (k : U) ∈ D) :
    F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k)-F.bits k ∈ F.ambientAxis N := by
  let q := QuotientGroup.mk' N
  have hc := Subgroup.mem_centralizer_iff.mp hu (q (k : U)) ⟨k,hk,rfl⟩
  change q (k : U)*q u=q u*q (k : U) at hc
  have he : q ((k : U)⁻¹*(u*(k : U)*u⁻¹))=1 := by
    simp only [map_mul,map_inv]
    rw [← hc]
    simp [mul_assoc]
  have hm : ((k⁻¹*MulAut.conjNormal u k : F.top.ker) : U) ∈ N :=
    (QuotientGroup.eq_one_iff _).mp he
  have hv := (F.bits_mem_ambientAxis N (k⁻¹*MulAut.conjNormal u k)).mpr hm
  rwa [F.bits_commutator] at hv

/-- Both factors retain the exact original axis. The first counts only
actual kernel vectors fixed by the selected top modulo that axis; the
second counts the actual top action on the retained kernel layer. -/
theorem properF_quotient_centralizer_card_mul_le
    (D N : Subgroup U) [N.Normal]
    (B : Submodule (ZMod 2) (Fin w → ZMod 2)) (hB : B ≤ F.kernelSpace)
    (hBD : F.coordinateSubgroup B ≤ D) (z : U) (hz : z ∈ D) :
    Nat.card N * Nat.card (Subgroup.centralizer
      (D.map (QuotientGroup.mk' N) : Set (U ⧸ N))) ≤
      Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
        F.coordinateTopAction (F.top.rangeRestrict z) v-v ∈ F.ambientAxis N} *
      Nat.card {t : F.top.range // ∀ v, v ∈ B →
        F.coordinateTopAction t v-v ∈ F.ambientAxis N} := by
  let S := Subgroup.centralizer (D.map (QuotientGroup.mk' N) : Set (U ⧸ N))
  let K := S.comap (QuotientGroup.mk' N) ⊓ F.top.ker
  let T : F.top.range → Prop := fun t => ∀ v, v ∈ B →
    F.coordinateTopAction t v-v ∈ F.ambientAxis N
  have htop (u : U) (hu : QuotientGroup.mk' N u ∈ S) :
      T (F.top.rangeRestrict u) := by
    intro v hv
    obtain ⟨k,hk⟩ := hB hv
    change F.bits k.toMul=v at hk
    rw [← hk]
    apply F.properF_displacement_axis D N u hu k.toMul
    apply hBD
    exact (F.kernel_mem_coordinateSubgroup B k.toMul).mpr (hk.symm ▸ hv)
  have hb := QuotientSubgroupProjectionCard.card_mul_le N S F.top.rangeRestrict K T
    (fun u hu hc => ⟨hc,congrArg Subtype.val hu⟩) htop
  have hfixed (k : K) :
      F.coordinateTopAction (F.top.rangeRestrict z)
        (F.bits (⟨k.val,k.property.2⟩ : F.top.ker))-
        F.bits (⟨k.val,k.property.2⟩ : F.top.ker) ∈ F.ambientAxis N := by
    let q := QuotientGroup.mk' N
    let a : F.top.ker := ⟨k.val,k.property.2⟩
    have hc := Subgroup.mem_centralizer_iff.mp k.property.1 (q z) ⟨z,hz,rfl⟩
    change q z*q (a : U)=q (a : U)*q z at hc
    have he : q ((a : U)⁻¹*(z*(a : U)*z⁻¹))=1 := by
      simp only [map_mul,map_inv]
      rw [hc]
      simp [mul_assoc]
    have hm : ((a⁻¹*MulAut.conjNormal z a : F.top.ker) : U) ∈ N :=
      (QuotientGroup.eq_one_iff _).mp he
    have hv := (F.bits_mem_ambientAxis N (a⁻¹*MulAut.conjNormal z a)).mpr hm
    rwa [F.bits_commutator] at hv
  let f : K → {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
      F.coordinateTopAction (F.top.rangeRestrict z) v-v ∈ F.ambientAxis N} := fun k =>
    let a : F.top.ker := ⟨k.val,k.property.2⟩
    ⟨F.bits a,⟨⟨Additive.ofMul a,rfl⟩,hfixed k⟩⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have he : (⟨x.val,x.property.2⟩ : F.top.ker) = ⟨y.val,y.property.2⟩ := by
      apply F.bitsHom_injective
      exact congrArg Multiplicative.ofAdd (congrArg Subtype.val h)
    exact congrArg (fun k : F.top.ker => k.val) he
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective f hf))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
