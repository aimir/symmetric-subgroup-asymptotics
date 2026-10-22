import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Logic.Relation

/-! Common field automorphisms propagate along a connected graph of
injectively parametrized root groups. This lemma only performs the
propagation; the adjacent-pair incidence must come from actual groups. -/
set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CFSGConnectedRootParameterField
variable {K G I : Type*} [Field K]

theorem semilinear_field_unique (u : K → G) (hu : Function.Injective u)
    (F : K → G) (σ τ : K ≃+* K) (c d : K) (hc : c ≠ 0)
    (hσ : ∀ a, F a = u (c * σ a)) (hτ : ∀ a, F a = u (d * τ a)) : σ = τ := by
  have hcd : c = d := by
    have h := hu ((hσ 1).symm.trans (hτ 1))
    simpa only [map_one, mul_one] using h
  ext a
  apply mul_left_cancel₀ hc
  have h := hu ((hσ a).symm.trans (hτ a))
  simpa only [← hcd] using h

theorem common_field_of_connected (R : I → I → Prop)
    (u : I → K → G) (hu : ∀ i, Function.Injective (u i)) (F : I → K → G)
    (hpair : ∀ i j, R i j → i ≠ j →
      ∃ (σ : K ≃+* K) (c d : K), c ≠ 0 ∧ d ≠ 0 ∧ ∀ a,
        F i a = u i (c * σ a) ∧ F j a = u j (d * σ a))
    (i₀ j₀ : I) (hij : R i₀ j₀) (hne : i₀ ≠ j₀)
    (hconn : ∀ j, Relation.ReflTransGen R i₀ j) :
    ∃ (σ : K ≃+* K) (c : I → K), ∀ i,
      c i ≠ 0 ∧ ∀ a, F i a = u i (c i * σ a) := by
  classical
  obtain ⟨σ, c₀, d₀, hc₀, _, h₀⟩ := hpair i₀ j₀ hij hne
  have hall (j : I) : ∃ c : K, c ≠ 0 ∧ ∀ a, F j a = u j (c * σ a) := by
    have hpath := hconn j
    induction hpath with
    | refl => exact ⟨c₀, hc₀, fun a => (h₀ a).1⟩
    | @tail b c _ hbc ih =>
      by_cases heq : b = c
      · subst c
        exact ih
      obtain ⟨τ, d, e, hd, he, hτ⟩ := hpair b c hbc heq
      obtain ⟨cb, hcb, hb⟩ := ih
      have hστ : σ = τ := semilinear_field_unique (u b) (hu b) (F b)
        σ τ cb d hcb hb (fun a => (hτ a).1)
      subst τ
      exact ⟨e, he, fun a => (hτ a).2⟩
  choose c hc using hall
  exact ⟨σ, c, hc⟩

end SymmetricSubgroupAsymptotics.CFSGConnectedRootParameterField
