import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Index

/-! In the SAME transitive finite action, the normalizer of a Sylow
subgroup is transitive on its actual fixed-point set. The cardinality of
that set therefore divides the actual normalizer/Sylow relative index.
No alternative action or subgroup catalogue is introduced. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.SylowFixedPointNormalizerOrbit
open MulAction
variable {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [IsPretransitive G X] (p : ℕ) [Fact p.Prime]

theorem normalizer_orbit_eq_fixedPoints
    (P : Sylow p G) (x : X) (hx : x∈fixedPoints P X) :
    orbit (Subgroup.normalizer (P : Set G)) x=fixedPoints P X := by
  ext y
  constructor
  · rintro ⟨n,rfl⟩
    apply mem_fixedPoints.mpr
    intro a
    have hconj : n.val⁻¹*a.val*n.val∈(P : Subgroup G) :=
      (Subgroup.mem_normalizer_iff''.mp n.property a.val).mp a.property
    have hfix := (mem_fixedPoints.mp hx) ⟨n.val⁻¹*a.val*n.val,hconj⟩
    have hh := congrArg (fun z : X => n.val • z) hfix
    simpa only [subgroup_smul_def,mul_smul,smul_inv_smul] using hh
  · intro hy
    obtain ⟨g,hg⟩ := exists_smul_eq G y x
    let K := stabilizer G x
    have hP : (P : Subgroup G)≤K := by
      intro a ha
      exact (mem_fixedPoints.mp hx) ⟨a,ha⟩
    have hgP : ((g • P : Sylow p G) : Subgroup G)≤K := by
      rintro _ ⟨a,ha,rfl⟩
      change (g*a*g⁻¹) • x=x
      rw [←hg]
      simp only [mul_smul,inv_smul_smul]
      have hay : a • y=y := (mem_fixedPoints.mp hy) ⟨a,ha⟩
      rw [hay]
    obtain ⟨h,hh⟩ := exists_smul_eq K ((g • P).subtype hgP) (P.subtype hP)
    simp_rw [Sylow.smul_subtype,Subgroup.smul_def,smul_smul] at hh
    have hn : h.val*g∈Subgroup.normalizer (P : Set G) :=
      Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh)
    have hny : (h.val*g) • y=x := by
      rw [mul_smul,hg]
      exact h.property
    have hreach : (h.val*g)⁻¹ • x=y := by rw [←hny]; exact inv_smul_smul _ _
    exact ⟨⟨(h.val*g)⁻¹,(Subgroup.normalizer (P : Set G)).inv_mem hn⟩,hreach⟩

theorem fixed_card_dvd_normalizer_relIndex [Finite X]
    (P : Sylow p G) (x : X) (hx : x∈fixedPoints P X) :
    Nat.card (fixedPoints P X) ∣
      (P : Subgroup G).relIndex (Subgroup.normalizer (P : Set G)) := by
  let N := Subgroup.normalizer (P : Set G)
  have hsub : (P : Subgroup G).subgroupOf N≤stabilizer N x := by
    intro a ha
    exact (mem_fixedPoints.mp hx) ⟨a.val,ha⟩
  have hd := Subgroup.index_dvd_of_le hsub
  rw [MulAction.index_stabilizer,normalizer_orbit_eq_fixedPoints p P x hx] at hd
  exact hd

end SymmetricSubgroupAsymptotics.SylowFixedPointNormalizerOrbit
