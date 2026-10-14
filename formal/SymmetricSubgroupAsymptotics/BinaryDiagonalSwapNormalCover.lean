import SymmetricSubgroupAsymptotics.BinaryDiagonalSwapCoordinates
import SymmetricSubgroupAsymptotics.NormalCoverGeneratorTransfer

/-!
# The unique minimal diagonal translation subgroup

For a faithful irreducible action on an elementary binary group, the
diagonal translations in the two-block swap model lie in every nontrivial
normal subgroup. The quotient is the local affine group times C2, so its
positive uniform normal-generator bound lifts without an extra position.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace BinaryDiagonalSwap

open SemidirectProduct

variable {V R : Type} [CommGroup V] [Group R]
variable (φ : R →* MulAut V)

/-- Irreducibility in the multiplicative translation coordinates. -/
def Irreducible : Prop :=
  ∀ S : Subgroup V, (∀ r v, v ∈ S → φ r v ∈ S) → S = ⊥ ∨ S = ⊤

def diagonal : V →* Model φ :=
  (inl : V × V →* Model φ).comp ((MonoidHom.id V).prod (MonoidHom.id V))

theorem diagonal_apply (v : V) : diagonal φ v = inl (v, v) := rfl

theorem diagonal_injective : Function.Injective (diagonal φ) := by
  intro u v h
  exact congrArg (fun g : Model φ ↦ g.left.1) h

private theorem translation_inter_ne_bot [Nontrivial V]
    (hφ : Function.Injective φ) (N : Subgroup (Model φ))
    (hN : N.Normal) (hNb : N ≠ ⊥) : N ⊓ translations φ ≠ ⊥ := by
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

theorem normal_cover [Nontrivial V] (hφ : Function.Injective φ)
    (hbinary : ∀ v : V, v * v = 1) (hirr : Irreducible φ)
    (N : Subgroup (Model φ)) (hN : N.Normal) (hNb : N ≠ ⊥) :
    (projection φ).ker ≤ N := by
  let S : Subgroup V := N.comap (diagonal φ)
  have hSinv : ∀ r v, v ∈ S → φ r v ∈ S := by
    intro r v hv
    change inl (v, v) ∈ N at hv
    have h := hN.conj_mem (inl (v, v)) hv (inr (r, 1))
    rw [conj_inl, right_inr, action_one] at h
    exact h
  have hSne : S ≠ ⊥ := by
    obtain ⟨g, hg, hg1⟩ := (N ⊓ translations φ).bot_or_exists_ne_one.resolve_left
      (translation_inter_ne_bot φ hφ N hN hNb)
    obtain ⟨v, hv⟩ := hg.2
    have hvN : (inl (v.1, v.2) : Model φ) ∈ N := hv.symm ▸ hg.1
    have hv1 : v ≠ 1 := by
      intro h
      apply hg1
      rw [← hv, h, map_one]
    by_cases heq : v.1 = v.2
    · have hdiag : v.1 ∈ S := by
        change (inl (v.1, v.1) : Model φ) ∈ N
        simpa only [heq] using hvN
      have hnontriv : v.1 ≠ 1 := by
        intro h
        exact hv1 (Prod.ext h (heq.symm.trans h))
      intro hb
      exact hnontriv (Subgroup.mem_bot.mp (hb ▸ hdiag))
    · have hswap : (inl (v.2, v.1) : Model φ) ∈ N := by
        have h := hN.conj_mem (inl v) hvN (inr (1, C2Wreath.gen))
        rw [conj_inl, right_inr, action_swap, map_one] at h
        exact h
      have hdiag : v.1 * v.2 ∈ S := by
        have h := N.mul_mem hvN hswap
        rw [← map_mul] at h
        change (inl (v.1 * v.2, v.2 * v.1) : Model φ) ∈ N at h
        change (inl (v.1 * v.2, v.1 * v.2) : Model φ) ∈ N
        simpa only [mul_comm v.2 v.1] using h
      have hnontriv : v.1 * v.2 ≠ 1 := by
        intro h
        apply heq
        calc
          v.1 = (v.1 * v.2) * v.2 := by rw [mul_assoc, hbinary, mul_one]
          _ = v.2 := by rw [h, one_mul]
      intro hb
      exact hnontriv (Subgroup.mem_bot.mp (hb ▸ hdiag))
  have hStop : S = ⊤ := (hirr S hSinv).resolve_left hSne
  intro g hg
  obtain ⟨hprod, hr⟩ := (mem_projection_ker φ g).mp hg
  have heq : g.left.1 = g.left.2 := by
    calc
      g.left.1 = (g.left.1 * g.left.2) * g.left.2 := by
        rw [mul_assoc, hbinary, mul_one]
      _ = g.left.2 := by rw [hprod, one_mul]
  have hgdiag : g = diagonal φ g.left.1 :=
    SemidirectProduct.ext (Prod.ext rfl heq.symm) hr
  rw [hgdiag]
  have hv : g.left.1 ∈ S := by rw [hStop]; exact Subgroup.mem_top _
  exact hv

theorem normal_generating_tuples [Nontrivial V] (hφ : Function.Injective φ)
    (hbinary : ∀ v : V, v * v = 1) (hirr : Irreducible φ)
    {t : ℕ} (ht : 0 < t)
    (hQ : ∀ N : Subgroup (Local φ × Binary), N.Normal →
      ∃ x : Fin t → Local φ × Binary, Subgroup.normalClosure (Set.range x) = N) :
    ∀ N : Subgroup (Model φ), N.Normal →
      ∃ x : Fin t → Model φ, Subgroup.normalClosure (Set.range x) = N := by
  obtain ⟨v, hv⟩ := exists_ne (1 : V)
  have hd : diagonal φ v ∈ (projection φ).ker :=
    (mem_projection_ker φ _).mpr ⟨hbinary v, rfl⟩
  have hd1 : diagonal φ v ≠ 1 := by
    intro h
    exact hv (diagonal_injective φ (h.trans (diagonal φ).map_one.symm))
  exact normal_generating_tuples_of_kernel_normal_cover
    (projection φ) (projection_surjective φ) (diagonal φ v) hd hd1
    (normal_cover φ hφ hbinary hirr) ht hQ

end BinaryDiagonalSwap
end SymmetricSubgroupAsymptotics

end
