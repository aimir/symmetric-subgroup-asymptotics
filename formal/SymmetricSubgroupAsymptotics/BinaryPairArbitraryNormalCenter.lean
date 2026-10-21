import SymmetricSubgroupAsymptotics.BinaryPairQuotientCenterProjection

/-! The joint quotient-centre capacity retains an ARBITRARY original
normal, including nonzero top image. Its exact kernel intersection, not
the whole normal, is used for every displacement and fixed-vector test. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryPairFrame

variable {X : Type} [Finite X] {w : ℕ} {U : Subgroup (Equiv.Perm X)}
    (F : BinaryPairFrame U (Fin w))

omit [Finite X] in
theorem central_quotient_displacement_axis (N : Subgroup U) [N.Normal]
    (u : U) (hu : QuotientGroup.mk' N u ∈ Subgroup.center (U ⧸ N))
    (k : F.top.ker) :
    F.coordinateTopAction (F.top.rangeRestrict u) (F.bits k) - F.bits k ∈
      F.ambientAxis N := by
  let q := QuotientGroup.mk' N
  have hc := (Subgroup.mem_center_iff.mp hu) (q (k : U))
  change q (k : U) * q u = q u * q (k : U) at hc
  have hh : q ((k : U)⁻¹ * (u * (k : U) * u⁻¹)) = 1 := by
    simp only [map_mul, map_inv]
    rw [← hc]
    simp [mul_assoc]
  have hm : ((k⁻¹ * MulAut.conjNormal u k : F.top.ker) : U) ∈ N :=
    (QuotientGroup.eq_one_iff _).mp hh
  have hv := (F.bits_mem_ambientAxis N (k⁻¹ * MulAut.conjNormal u k)).mpr hm
  rwa [F.bits_commutator] at hv

theorem fixedSubgroup_eq_coordinate_axis (N : Subgroup U) [N.Normal] :
    binaryPairFixedSubgroup F.top.ker N =
      binaryPairFixedSubgroup F.top.ker
        (F.coordinateSubgroup (F.axisSubrepresentation N).toSubmodule) := by
  ext x
  rw [binaryPairFixedSubgroup_mem_iff _ _ (fun u : U => u) (by simp),
    binaryPairFixedSubgroup_mem_iff _ _ (fun u : U => u) (by simp)]
  apply and_congr_right
  intro hx
  apply forall_congr'
  intro u
  have hc : x⁻¹ * (u * x * u⁻¹) ∈ F.top.ker := by
    change F.top (x⁻¹ * (u * x * u⁻¹)) = 1
    have hx' : F.top x = 1 := hx
    simp [map_mul, map_inv, hx']
  let k : F.top.ker := ⟨x⁻¹ * (u * x * u⁻¹), hc⟩
  change (k : U) ∈ N ↔ (k : U) ∈ F.coordinateSubgroup (F.ambientAxis N)
  rw [F.kernel_mem_coordinateSubgroup, F.bits_mem_ambientAxis]

theorem arbitrary_normal_center_card_mul_le (N : Subgroup U) [N.Normal] :
    Nat.card N * Nat.card (Subgroup.center (U ⧸ N)) ≤
      Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
        ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} *
      Nat.card {t : F.top.range // ∀ v, v ∈ F.kernelSpace →
        F.coordinateTopAction t v - v ∈ F.ambientAxis N} := by
  let A := F.axisSubrepresentation N
  let K := binaryPairFixedSubgroup F.top.ker N
  let T : F.top.range → Prop := fun t => ∀ v, v ∈ F.kernelSpace →
    F.coordinateTopAction t v - v ∈ F.ambientAxis N
  have hb := QuotientCenterProjectionCard.card_mul_le N F.top.rangeRestrict K T
    (fun g hg hc => ⟨congrArg Subtype.val hg, hc⟩)
    (by
      intro g hg v hv
      obtain ⟨k, hk⟩ := hv
      change F.bits k.toMul = v at hk
      rw [← hk]
      exact F.central_quotient_displacement_axis N g hg k.toMul)
  let k : K → {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
      ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} := fun x =>
    let u : F.top.ker := ⟨x.val, x.property.1⟩
    ⟨F.bits u, ⟨⟨Additive.ofMul u, rfl⟩,
      (F.kernel_mem_coordinate_fixed A u).mp (F.fixedSubgroup_eq_coordinate_axis N ▸ x.property)⟩⟩
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    have he : (⟨x.val, x.property.1⟩ : F.top.ker) = ⟨y.val, y.property.1⟩ := by
      apply F.bitsHom_injective
      exact congrArg Multiplicative.ofAdd (congrArg Subtype.val h)
    exact congrArg (fun z : F.top.ker => (z : U)) he
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective k hk))

/-- When the SAME denominator has zero top image, every quotient-central
top is an actual central top. This joint restriction is substantially
stronger than multiplying unrelated worst-case factors. -/
theorem kernel_normal_center_card_mul_le (N : Subgroup U) [N.Normal]
    (hN : N ≤ F.top.ker) :
    Nat.card N * Nat.card (Subgroup.center (U ⧸ N)) ≤
      Nat.card {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
        ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} *
      Nat.card {t : F.top.range // t ∈ Subgroup.center F.top.range ∧
        ∀ v, v ∈ F.kernelSpace → F.coordinateTopAction t v - v ∈ F.ambientAxis N} := by
  let A := F.axisSubrepresentation N
  let K := binaryPairFixedSubgroup F.top.ker N
  let T : F.top.range → Prop := fun t => t ∈ Subgroup.center F.top.range ∧
    ∀ v, v ∈ F.kernelSpace → F.coordinateTopAction t v - v ∈ F.ambientAxis N
  let q : U ⧸ N →* F.top.range := QuotientGroup.lift N F.top.rangeRestrict (by
    simpa only [MonoidHom.ker_rangeRestrict] using hN)
  have ht (u : U) (hu : QuotientGroup.mk' N u ∈ Subgroup.center (U ⧸ N)) :
      T (F.top.rangeRestrict u) := by
    constructor
    · apply Subgroup.mem_center_iff.mpr
      intro t
      obtain ⟨g, rfl⟩ := F.top.rangeRestrict_surjective t
      have hh := congrArg q ((Subgroup.mem_center_iff.mp hu) (QuotientGroup.mk' N g))
      simpa only [map_mul] using hh
    · intro v hv
      obtain ⟨k, hk⟩ := hv
      change F.bits k.toMul = v at hk
      rw [← hk]
      exact F.central_quotient_displacement_axis N u hu k.toMul
  have hb := QuotientCenterProjectionCard.card_mul_le N F.top.rangeRestrict K T
    (fun g hg hc => ⟨congrArg Subtype.val hg, hc⟩) ht
  let k : K → {v : Fin w → ZMod 2 // v ∈ F.kernelSpace ∧
      ∀ t : F.top.range, F.coordinateTopAction t v - v ∈ F.ambientAxis N} := fun x =>
    let u : F.top.ker := ⟨x.val, x.property.1⟩
    ⟨F.bits u, ⟨⟨Additive.ofMul u, rfl⟩,
      (F.kernel_mem_coordinate_fixed A u).mp (F.fixedSubgroup_eq_coordinate_axis N ▸ x.property)⟩⟩
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    have he : (⟨x.val, x.property.1⟩ : F.top.ker) = ⟨y.val, y.property.1⟩ := by
      apply F.bitsHom_injective
      exact congrArg Multiplicative.ofAdd (congrArg Subtype.val h)
    exact congrArg (fun z : F.top.ker => (z : U)) he
  exact hb.trans (Nat.mul_le_mul_right _ (Nat.card_le_card_of_injective k hk))

end SymmetricSubgroupAsymptotics.BinaryPairFrame
