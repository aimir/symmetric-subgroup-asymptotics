import SymmetricSubgroupAsymptotics.Non2PreE7C2Wreath
import SymmetricSubgroupAsymptotics.NormalCoverGeneratorTransfer
import SymmetricSubgroupAsymptotics.CyclicQuotientSocles
import Mathlib.GroupTheory.Subgroup.Simple
import Mathlib.GroupTheory.Subgroup.Center

/-!
# Normal covers in a two-point wreath product

If a centerless local group has a nontrivial subgroup contained in each
nontrivial normal subgroup, its two coordinate copies lie in every
nontrivial normal subgroup of the wreath product. For a centerless simple
local group, the cyclic block quotient therefore gives normal-generator
bound one, also in every original quotient socle.

No normal-subgroup enumeration or splitting of a given normal subgroup
is used: commutators with one coordinate isolate the local normal subgroup.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace C2Wreath

open SemidirectProduct

variable {A : Type} [Group A] [Nontrivial A]

def firstFactor : A →* W A :=
  (inl : A × A →* W A).comp (MonoidHom.inl A A)

theorem centralizing_base_eq_one (hcenter : Subgroup.center A = ⊥)
    (g : W A) (hg : ∀ v : A × A, g * inl v = inl v * g) : g = 1 := by
  rcases cases g.right with hr | hr
  · have h1 : g.left.1 ∈ Subgroup.center A := by
      apply Subgroup.mem_center_iff.mpr
      intro a
      have h := congrArg (fun z : W A ↦ z.left.1) (hg (a, 1))
      simpa only [mul_left', hr, swapAut_one, left_inl, right_inl,
        Prod.fst_mul] using h.symm
    have h2 : g.left.2 ∈ Subgroup.center A := by
      apply Subgroup.mem_center_iff.mpr
      intro a
      have h := congrArg (fun z : W A ↦ z.left.2) (hg (1, a))
      simpa only [mul_left', hr, swapAut_one, left_inl, right_inl,
        Prod.snd_mul] using h.symm
    have e1 : g.left.1 = 1 := Subgroup.mem_bot.mp (hcenter ▸ h1)
    have e2 : g.left.2 = 1 := Subgroup.mem_bot.mp (hcenter ▸ h2)
    exact SemidirectProduct.ext (Prod.ext e1 e2) hr
  · obtain ⟨a, ha⟩ := exists_ne (1 : A)
    have h := congrArg (fun z : W A ↦ z.left.1) (hg (a, 1))
    have he : g.left.1 = a * g.left.1 := by
      simpa only [mul_left', hr, swapAut_gen, swapAut_one, left_inl,
        right_inl, Prod.fst_mul, mul_one] using h
    exact (ha (mul_right_cancel (show a * g.left.1 = 1 * g.left.1 by
      simpa only [one_mul] using he.symm))).elim

theorem normal_inter_base_ne_bot (hcenter : Subgroup.center A = ⊥)
    (N : Subgroup (W A)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    N ⊓ (rightHom : W A →* Multiplicative (ZMod 2)).ker ≠ ⊥ := by
  let B := (rightHom : W A →* Multiplicative (ZMod 2)).ker
  intro hb
  apply hNb
  apply le_antisymm _ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply centralizing_base_eq_one hcenter g
  intro v
  have hv : (inl v : W A) ∈ B := by
    change rightHom (inl v) = 1
    exact rightHom_inl v
  have hc : g * inl v * g⁻¹ * (inl v)⁻¹ ∈ N ⊓ B := by
    refine ⟨?_, B.mul_mem ((inferInstance : B.Normal).conj_mem _ hv g) (B.inv_mem hv)⟩
    have hi := hN.conj_mem g⁻¹ (N.inv_mem hg) (inl v)
    simpa only [mul_assoc] using N.mul_mem hg hi
  have he : g * inl v * g⁻¹ * (inl v)⁻¹ = 1 := Subgroup.mem_bot.mp (hb ▸ hc)
  calc
    g * inl v = (g * inl v * g⁻¹ * (inl v)⁻¹) * (inl v * g) := by group
    _ = inl v * g := by rw [he, one_mul]

theorem first_inter_ne_bot (hcenter : Subgroup.center A = ⊥)
    (N : Subgroup (W A)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    N.comap firstFactor ≠ ⊥ := by
  let B := (rightHom : W A →* Multiplicative (ZMod 2)).ker
  obtain ⟨g, hg, hg1⟩ := (N ⊓ B).bot_or_exists_ne_one.resolve_left
    (normal_inter_base_ne_bot hcenter N hN hNb)
  have hr : g.right = 1 := hg.2
  have hginl : (inl g.left : W A) = g := by
    apply SemidirectProduct.ext
    · rfl
    · exact hr.symm
  have hpair : g.left.1 ≠ 1 ∨ g.left.2 ≠ 1 := by
    by_contra h
    push_neg at h
    exact hg1 (SemidirectProduct.ext (Prod.ext h.1 h.2) hr)
  have hex : ∃ v : A × A, (inl v : W A) ∈ N ∧ v.1 ≠ 1 := by
    rcases hpair with hfirst | hsecond
    · exact ⟨g.left, hginl ▸ hg.1, hfirst⟩
    · refine ⟨(g.left.2, g.left.1), ?_, hsecond⟩
      have hc := hN.conj_mem (inl g.left) (hginl ▸ hg.1) (inr gen)
      simpa only [← map_inv, ← inl_aut, swapAut_gen] using hc
  obtain ⟨v, hv, hv1⟩ := hex
  intro hbot
  have hz : v.1 ∈ Subgroup.center A := by
    apply Subgroup.mem_center_iff.mpr
    intro a
    have heq : firstFactor (v.1 * a * v.1⁻¹ * a⁻¹) =
        (inl v : W A) * firstFactor a * (inl v)⁻¹ * (firstFactor a)⁻¹ := by
      change inl (v.1 * a * v.1⁻¹ * a⁻¹, 1) =
        (inl v : W A) * inl (a, 1) * (inl v)⁻¹ * (inl (a, 1))⁻¹
      simp only [← map_inv, ← map_mul]
      congr 1
      apply Prod.ext
      · rfl
      · simp
    have hc : firstFactor (v.1 * a * v.1⁻¹ * a⁻¹) ∈ N := by
      rw [heq]
      have hi := hN.conj_mem (inl v)⁻¹ (N.inv_mem hv) (firstFactor a)
      simpa only [mul_assoc] using N.mul_mem hv hi
    have he : v.1 * a * v.1⁻¹ * a⁻¹ = 1 :=
      Subgroup.mem_bot.mp (hbot ▸ (show _ ∈ N.comap firstFactor from hc))
    calc
      a * v.1 = 1 * (a * v.1) := (one_mul _).symm
      _ = (v.1 * a * v.1⁻¹ * a⁻¹) * (a * v.1) := by rw [he]
      _ = v.1 * a := by group
  exact hv1 (Subgroup.mem_bot.mp (hcenter ▸ hz))

theorem product_normal_cover (hcenter : Subgroup.center A = ⊥)
    (D : Subgroup A)
    (hD : ∀ K : Subgroup A, K.Normal → K ≠ ⊥ → D ≤ K)
    (N : Subgroup (W A)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    (D.prod D).map (inl : A × A →* W A) ≤ N := by
  have hK : D ≤ N.comap firstFactor := hD _ (hN.comap firstFactor)
    (first_inter_ne_bot hcenter N hN hNb)
  rintro _ ⟨⟨a, b⟩, hab, rfl⟩
  have ha : (inl (a, 1) : W A) ∈ N := hK hab.1
  have hb : (inl (b, 1) : W A) ∈ N := hK hab.2
  have hb' : (inl (1, b) : W A) ∈ N := by
    have hc := hN.conj_mem (inl (b, 1)) hb (inr gen)
    simpa only [← map_inv, ← inl_aut, swapAut_gen] using hc
  simpa only [← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using N.mul_mem ha hb'

theorem simple_kernel_normal_cover [IsSimpleGroup A]
    (hcenter : Subgroup.center A = ⊥)
    (N : Subgroup (W A)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    (rightHom : W A →* Multiplicative (ZMod 2)).ker ≤ N := by
  have h := product_normal_cover hcenter (⊤ : Subgroup A)
    (fun K hK hKb ↦ by rw [hK.eq_bot_or_eq_top.resolve_left hKb]) N hN hNb
  rw [← range_inl_eq_ker_rightHom]
  rintro _ ⟨v, rfl⟩
  exact h ⟨v, ⟨Subgroup.mem_top _, Subgroup.mem_top _⟩, rfl⟩

theorem normal_generating_singletons_of_simple [IsSimpleGroup A]
    (hcenter : Subgroup.center A = ⊥) :
    ∀ N : Subgroup (W A), N.Normal →
      ∃ x : Fin 1 → W A, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  apply normal_generating_tuples_of_kernel_normal_cover
    (rightHom : W A →* Multiplicative (ZMod 2)) rightHom_surjective
    (inl (a, 1)) (rightHom_inl _) ?_ (simple_kernel_normal_cover hcenter)
    (by decide) normal_generating_singletons_of_isCyclic
  intro h
  exact ha (congrArg (fun g : W A ↦ g.left.1) h)

theorem quotientSocle_one_of_simple [IsSimpleGroup A]
    (hcenter : Subgroup.center A = ⊥) (N : Subgroup (W A)) [N.Normal] :
    SocleNormalGeneratorBound (W A ⧸ N) 1 :=
  quotientSocleNormalGeneratorBound_of_normal_generating_tuples
    (normal_generating_singletons_of_simple hcenter) N

end C2Wreath
end SymmetricSubgroupAsymptotics

end
