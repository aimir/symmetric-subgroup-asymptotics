import SymmetricSubgroupAsymptotics.SocleNormalSubgroupGeneratorInheritance
import SymmetricSubgroupAsymptotics.PrimePrimarySocleTypeSharing
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! Actual normal complements inside the finite-group socle give literal
primary projections. Every minimal normal factor of a different prime
(or nonabelian type) is killed by the primary projection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.ZmudSoclePrimaryProjections

variable {G : Type} [Group G]

private theorem quotient_injective (E H : Subgroup G) [H.Normal]
    (hdis : E ⊓ H = ⊥) :
    Function.Injective ((QuotientGroup.mk' H).comp E.subtype) := by
  intro a b hab
  apply Subtype.ext
  apply mul_inv_eq_one.mp
  have hxH : a.1 * b.1⁻¹ ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' H (a.1 * b.1⁻¹) = 1
    rw [map_mul, map_inv]
    exact mul_inv_eq_one.mpr hab
  have hx : a.1 * b.1⁻¹ ∈ E ⊓ H :=
    ⟨E.mul_mem a.2 (E.inv_mem b.2), hxH⟩
  rw [hdis] at hx
  exact Subgroup.mem_bot.mp hx

/-- Projection onto the first actual subgroup in an internal normal
product. -/
def projection (E H : Subgroup G) [H.Normal] (hdis : E ⊓ H = ⊥) :
    ↥(E ⊔ H) →* E := by
  let q := QuotientGroup.mk' H
  let f := q.comp E.subtype
  let e : E ≃* f.range := MonoidHom.ofInjective (quotient_injective E H hdis)
  let k : ↥(E ⊔ H) →* f.range := {
    toFun s := ⟨q s.1, by
      obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp s.2
      refine ⟨⟨a, ha⟩, ?_⟩
      change q a = q s.1
      rw [← hab, map_mul]
      have hbq : q b = 1 := (QuotientGroup.eq_one_iff _).mpr hb
      rw [hbq, mul_one]⟩
    map_one' := by apply Subtype.ext; exact map_one q
    map_mul' a b := by apply Subtype.ext; exact map_mul q a.1 b.1 }
  exact e.symm.toMonoidHom.comp k

/-- The projection fixes the literal first factor. -/
theorem projection_left (E H : Subgroup G) [H.Normal]
    (hdis : E ⊓ H = ⊥) (a : E) :
    projection E H hdis ⟨a.1, Subgroup.mem_sup_left a.2⟩ = a := by
  apply (MonoidHom.ofInjective (quotient_injective E H hdis)).injective
  change (MonoidHom.ofInjective (quotient_injective E H hdis))
    ((MonoidHom.ofInjective (quotient_injective E H hdis)).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- The complementary factor is killed. -/
theorem projection_right (E H : Subgroup G) [H.Normal]
    (hdis : E ⊓ H = ⊥) (b : H) :
    projection E H hdis ⟨b.1, Subgroup.mem_sup_right b.2⟩ = 1 := by
  apply (MonoidHom.ofInjective (quotient_injective E H hdis)).injective
  change (MonoidHom.ofInjective (quotient_injective E H hdis))
    ((MonoidHom.ofInjective (quotient_injective E H hdis)).symm _) = _
  rw [MulEquiv.apply_symm_apply, map_one]
  apply Subtype.ext
  exact (QuotientGroup.eq_one_iff _).mpr b.2

/-- A complementary ambient-normal subgroup to a primary socle part
contains every minimal normal factor of a different type. -/
theorem minimalNormal_le_complement
    [Finite G] (p : ℕ) [Fact p.Prime]
    (E H : Subgroup G) [E.Normal] [H.Normal]
    (hE : IsPGroup p E) (hjoin : E ⊔ H = finiteGroupSocle G)
    (M : Subgroup G) (hM : IsMinimalNormalSubgroup M)
    (hnot : ¬ IsPGroup p M) : M ≤ H := by
  letI : M.Normal := hM.1
  let q := QuotientGroup.mk' H
  have hmap : (E ⊔ H).map q = E.map q := by
    rw [Subgroup.map_sup]
    have hzero : H.map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := H)).mpr
      rw [QuotientGroup.ker_mk']
    rw [hzero, sup_bot_eq]
  have hMle : M ≤ E ⊔ H := by
    rw [hjoin]
    intro m hm
    exact Subgroup.subset_normalClosure ⟨M, hM, hm⟩
  have hMp : IsPGroup p (M.map q) := by
    apply (hE.map q).to_le
    rw [← hmap]
    exact Subgroup.map_mono hMle
  by_contra hnotle
  have hinf : M ⊓ H = ⊥ := by
    by_contra hne
    have heq := hM.2.2 (M ⊓ H) inferInstance hne inf_le_left
    exact hnotle (by rw [← heq]; exact inf_le_right)
  have hinj : Function.Injective (q.subgroupMap M) := by
    intro a b hab
    exact quotient_injective M H hinf (congrArg Subtype.val hab)
  exact hnot (hMp.of_injective (q.subgroupMap M) hinj)

/-- A primary character extends to the entire actual socle, trivially on
every minimal normal subgroup of a different type. -/
theorem exists_primary_character_extension
    [Finite G] (p : ℕ) [Fact p.Prime]
    (E : Subgroup G) [E.Normal] (hE : IsPGroup p E)
    (hEsocle : E ≤ finiteGroupSocle G) (chi : E →* ℂ) :
    ∃ psi : finiteGroupSocle G →* ℂ,
      (∀ a : E, psi ⟨a.1, hEsocle a.2⟩ = chi a) ∧
      ∀ (M : Subgroup G) (hM : IsMinimalNormalSubgroup M), ¬ IsPGroup p M →
        ∀ m : M, psi ⟨m.1, Subgroup.subset_normalClosure ⟨M, hM, m.2⟩⟩ = 1 := by
  obtain ⟨H, hH, _, hdis, hjoin⟩ := exists_normal_socle_complement E hEsocle
  letI : H.Normal := hH
  let e : finiteGroupSocle G ≃* ↥(E ⊔ H) := MulEquiv.subgroupCongr hjoin.symm
  let psi : finiteGroupSocle G →* ℂ :=
    chi.comp ((projection E H hdis).comp e.toMonoidHom)
  refine ⟨psi, ?_, ?_⟩
  · intro a
    exact congrArg chi (projection_left E H hdis a)
  · intro M hM hnot m
    have hMH := minimalNormal_le_complement p E H hE hjoin M hM hnot
    have he := projection_right E H hdis (⟨m.1, hMH m.2⟩ : H)
    change chi (projection E H hdis
      ⟨m.1, Subgroup.mem_sup_right (hMH m.2)⟩) = 1
    rw [he, map_one]

end SymmetricSubgroupAsymptotics.ZmudSoclePrimaryProjections
