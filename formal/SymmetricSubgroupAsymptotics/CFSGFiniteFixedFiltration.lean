import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Data.Int.Cast.Lemmas
import Lean.Elab.Tactic.Omega

/-! Fixed elements are covered by finitely many genuine fixed height
representatives. No surjectivity of a fixed-point functor is assumed:
the per-layer representatives are explicit hypotheses of this reusable
finite induction and must be constructed in each application. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFixedFiltration
variable {G : Type*} [Group G]

theorem fixed_mem_of_step (F : MulAut G) (S : Subgroup G)
    (Tail : ℕ → Subgroup G) (B : ℕ) (hfirst : Tail 0 = ⊤) (hlast : Tail B = ⊥)
    (step : ∀ h, h < B → ∀ u : G, u ∈ Tail h → F u = u →
      ∃ a : G, a ∈ S ∧ ∃ v : G, v ∈ Tail (h+1) ∧ F v = v ∧ u = a*v)
    (u : G) (hu : F u = u) : u ∈ S := by
  have hall : ∀ m n : ℕ, m+n=B → ∀ v : G, v∈Tail n → F v=v → v∈S := by
    intro m
    induction m with
    | zero =>
      intro n hn v hv _
      have hnB : n=B := by omega
      rw [hnB,hlast,Subgroup.mem_bot] at hv
      rw [hv]
      exact S.one_mem
    | succ m ih =>
      intro n hn v hv hFv
      obtain ⟨a,ha,w,hw,hFw,he⟩ := step n (by omega) v hv hFv
      rw [he]
      exact S.mul_mem ha (ih (n+1) (by omega) w hw hFw)
  exact hall B 0 (by omega) u (by rw [hfirst]; exact Subgroup.mem_top u) hu

theorem fixed_mem_of_quotient_representatives (F : MulAut G) (S : Subgroup G)
    (Tail : ℕ → Subgroup G) [∀ h, (Tail h).Normal]
    (B : ℕ) (hfirst : Tail 0 = ⊤) (hlast : Tail B = ⊥)
    (representative : ∀ h, h < B → ∀ u : G, u ∈ Tail h → F u = u →
      ∃ a : G, a ∈ S ∧ F a=a ∧
        QuotientGroup.mk' (Tail (h+1)) a = QuotientGroup.mk' (Tail (h+1)) u)
    (u : G) (hu : F u=u) : u ∈ S := by
  apply fixed_mem_of_step F S Tail B hfirst hlast ?_ u hu
  intro h hB v hv hFv
  obtain ⟨a,ha,hFa,he⟩ := representative h hB v hv hFv
  refine ⟨a,ha,a⁻¹*v,?_,?_,(mul_inv_cancel_left a v).symm⟩
  · have hk : a⁻¹*v ∈ (QuotientGroup.mk' (Tail (h+1))).ker := by
      change QuotientGroup.mk' (Tail (h+1)) (a⁻¹*v)=1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    rwa [QuotientGroup.ker_mk'] at hk
  · rw [map_mul,map_inv,hFa,hFv]

theorem fixed_mem_of_positive_step (F : MulAut G) (S : Subgroup G)
    (Tail : ℤ → Subgroup G) (B : ℕ) (hfirst : Tail 1 = ⊤)
    (hlast : Tail ((B : ℤ)+1) = ⊥)
    (step : ∀ h : ℤ, 0 < h → ∀ u : G, u ∈ Tail h → F u=u →
      ∃ a : G, a∈S ∧ ∃ v : G, v∈Tail (h+1) ∧ F v=v ∧ u=a*v)
    (u : G) (hu : F u=u) : u∈S := by
  apply fixed_mem_of_step F S (fun h : ℕ => Tail ((h : ℤ)+1)) B ?_ hlast ?_ u hu
  · simpa only [Nat.cast_zero,zero_add] using hfirst
  · intro h _ v hv hFv
    obtain ⟨a,ha,w,hw,hFw,he⟩ := step ((h : ℤ)+1) (by omega) v hv hFv
    refine ⟨a,ha,w,?_,hFw,he⟩
    simpa only [Nat.cast_add,Nat.cast_one] using hw

end SymmetricSubgroupAsymptotics.CFSGFiniteFixedFiltration
