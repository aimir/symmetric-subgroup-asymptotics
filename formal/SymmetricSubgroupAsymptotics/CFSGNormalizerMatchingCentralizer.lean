import SymmetricSubgroupAsymptotics.CFSGNormalizerTranspositionCapture

/-! A subgroup with transposition classes of size at most two centralizes
the intrinsic matching of any contained symmetric Sylow two-subgroup.
Both partner transport and the unmatched case use actual captured swaps. -/
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.CFSGNormalizerMatchingCentralizer
open Equiv CFSGNormalizerTranspositionClasses CFSGSymmetricSylowCanonicalMatching

variable {X : Type*} [Finite X] [DecidableEq X]

theorem hasPartner_image (N : Subgroup (Perm X))
    (hsize : ∀ x, (pointClass N x).ncard ≤ 2) (Q : Sylow 2 (Perm X))
    (hQN : (Q : Subgroup (Perm X)) ≤ N) (g : Perm X) (hg : g ∈ N)
    {x : X} (hx : HasPartner Q x) : HasPartner Q (g x) := by
  obtain ⟨y, hne, hxy⟩ := hx
  have hm := N.mul_mem (N.mul_mem hg (hQN hxy)) (N.inv_mem hg)
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right] at hm
  refine ⟨g y, fun he => hne (g.injective he), ?_⟩
  exact CFSGNormalizerTranspositionCapture.swap_mem_sylow_of_small_classes N hsize Q hQN _ _ hm

theorem preserves_partner (N : Subgroup (Perm X))
    (hsize : ∀ x, (pointClass N x).ncard ≤ 2) (Q : Sylow 2 (Perm X))
    (hQN : (Q : Subgroup (Perm X)) ≤ N) (g : Perm X) (hg : g ∈ N) (x : X) :
    g (partner Q x) = partner Q (g x) := by
  by_cases hx : HasPartner Q x
  · obtain ⟨hne, hm⟩ := partner_spec Q hx
    obtain ⟨hne', hm'⟩ := partner_spec Q (hasPartner_image N hsize Q hQN g hg hx)
    have hconj := N.mul_mem (N.mul_mem hg (hQN hm)) (N.inv_mem hg)
    rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right] at hconj
    have hQ := CFSGNormalizerTranspositionCapture.swap_mem_sylow_of_small_classes
      N hsize Q hQN _ _ hconj
    exact CFSGTwoGroupTranspositionMatching.swap_partner_unique Q Q.isPGroup'
      (fun he => hne (g.injective he).symm) (Ne.symm hne') hQ hm'
  · have hgx : ¬HasPartner Q (g x) := by
      intro h
      have hh := hasPartner_image N hsize Q hQN g⁻¹ (N.inv_mem hg) h
      change HasPartner Q (g.symm (g x)) at hh
      exact hx (by simpa only [g.symm_apply_apply] using hh)
    rw [partner_of_not Q hx, partner_of_not Q hgx]

theorem le_matching_centralizer (N : Subgroup (Perm X))
    (hsize : ∀ x, (pointClass N x).ncard ≤ 2) (Q : Sylow 2 (Perm X))
    (hQN : (Q : Subgroup (Perm X)) ≤ N) :
    N ≤ Subgroup.centralizer ({matching Q} : Set (Perm X)) := by
  intro g hg
  apply Subgroup.mem_centralizer_iff.mpr
  intro t ht
  have ht' : t = matching Q := Set.mem_singleton_iff.mp ht
  subst t
  apply Perm.ext
  intro x
  change partner Q (g x) = g (partner Q x)
  exact (preserves_partner N hsize Q hQN g hg x).symm

end SymmetricSubgroupAsymptotics.CFSGNormalizerMatchingCentralizer
