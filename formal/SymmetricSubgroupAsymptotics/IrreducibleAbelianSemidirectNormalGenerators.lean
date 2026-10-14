import SymmetricSubgroupAsymptotics.SemidirectAbelianCentralizer
import SymmetricSubgroupAsymptotics.NormalCoverGeneratorTransfer

/-! A faithful irreducible action on an abelian group retains a positive
uniform normal-generator bound from its complement. This version uses
subgroups of the actual translation coordinates, with no chosen basis. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace IrreducibleAbelianSemidirect

open SemidirectProduct

variable {V H : Type} [CommGroup V] [Group H]
variable (φ : H →* MulAut V)

def Irreducible : Prop :=
  ∀ S : Subgroup V, (∀ h v, v ∈ S → φ h v ∈ S) → S = ⊥ ∨ S = ⊤

def translations : Subgroup (V ⋊[φ] H) := (inl : V →* V ⋊[φ] H).range

instance translations_normal : (translations φ).Normal := by
  rw [translations, range_inl_eq_ker_rightHom]
  infer_instance

theorem selfCentralizing (hφ : Function.Injective φ) (g : V ⋊[φ] H)
    (hg : ∀ v ∈ translations φ, g * v = v * g) : g ∈ translations φ := by
  have hc : g ∈ Subgroup.centralizer (translations φ : Set (V ⋊[φ] H)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact (hg v hv).symm
  have ha : φ g.right = 1 :=
    (SemidirectAbelianCentralizer.mem_centralizer_iff φ g).mp hc
  have hr : g.right = 1 := hφ (ha.trans φ.map_one.symm)
  rw [translations, range_inl_eq_ker_rightHom, MonoidHom.mem_ker]
  exact hr

theorem translation_inter_ne_bot (hφ : Function.Injective φ)
    (N : Subgroup (V ⋊[φ] H)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    N ⊓ translations φ ≠ ⊥ := by
  intro hbot
  apply hNb
  have hNT : N ≤ translations φ := by
    intro x hx
    apply selfCentralizing φ hφ x
    intro v hv
    have hc : x * v * x⁻¹ * v⁻¹ ∈ N ⊓ translations φ := by
      refine ⟨?_, (translations φ).mul_mem
        ((translations_normal φ).conj_mem v hv x) ((translations φ).inv_mem hv)⟩
      have hi := hN.conj_mem x⁻¹ (N.inv_mem hx) v
      simpa only [mul_assoc] using N.mul_mem hx hi
    have he : x * v * x⁻¹ * v⁻¹ = 1 := Subgroup.mem_bot.mp (hbot ▸ hc)
    calc
      x * v = (x * v * x⁻¹ * v⁻¹) * (v * x) := by group
      _ = v * x := by rw [he, one_mul]
  apply le_antisymm _ bot_le
  intro x hx
  exact hbot ▸ (show x ∈ N ⊓ translations φ from ⟨hx, hNT hx⟩)

theorem normal_cover (hφ : Function.Injective φ) (hirr : Irreducible φ)
    (N : Subgroup (V ⋊[φ] H)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    (rightHom : V ⋊[φ] H →* H).ker ≤ N := by
  let S : Subgroup V := N.comap (inl : V →* V ⋊[φ] H)
  have hSinv : ∀ h v, v ∈ S → φ h v ∈ S := by
    intro h v hv
    change (inl (φ h v) : V ⋊[φ] H) ∈ N
    rw [inl_aut]
    have hc := hN.conj_mem (inl v) hv (inr h)
    simpa only [map_inv] using hc
  have hSne : S ≠ ⊥ := by
    obtain ⟨g, hg, hg1⟩ := (N ⊓ translations φ).bot_or_exists_ne_one.resolve_left
      (translation_inter_ne_bot φ hφ N hN hNb)
    obtain ⟨v, hv⟩ := hg.2
    have hvS : v ∈ S := by
      change (inl v : V ⋊[φ] H) ∈ N
      rw [hv]
      exact hg.1
    intro hb
    have hv1 : v = 1 := Subgroup.mem_bot.mp (hb ▸ hvS)
    apply hg1
    rw [← hv, hv1, map_one]
  have hStop : S = ⊤ := (hirr S hSinv).resolve_left hSne
  rw [← range_inl_eq_ker_rightHom]
  rintro g ⟨v, rfl⟩
  have hv : v ∈ S := by rw [hStop]; exact Subgroup.mem_top _
  exact hv

theorem normal_generating_tuples [Nontrivial V]
    (hφ : Function.Injective φ) (hirr : Irreducible φ)
    {t : ℕ} (ht : 0 < t)
    (hH : ∀ N : Subgroup H, N.Normal →
      ∃ x : Fin t → H, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (V ⋊[φ] H), N.Normal →
      ∃ x : Fin t → V ⋊[φ] H, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have hd : (inl v : V ⋊[φ] H) ∈ (rightHom : V ⋊[φ] H →* H).ker := by
    rw [MonoidHom.mem_ker, rightHom_inl]
  have hd1 : (inl v : V ⋊[φ] H) ≠ 1 := by
    intro h
    exact hv (inl_injective (h.trans (map_one inl).symm))
  exact normal_generating_tuples_of_kernel_normal_cover
    (rightHom : V ⋊[φ] H →* H) rightHom_surjective (inl v) hd hd1
    (normal_cover φ hφ hirr) ht hH

end IrreducibleAbelianSemidirect
end SymmetricSubgroupAsymptotics

end
