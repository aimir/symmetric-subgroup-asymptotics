import SymmetricSubgroupAsymptotics.LinearCentralizerTripleEvaluation
import Mathlib.Tactic.FinCases

/-! Two independent operator strings save two basis evaluations in any
dimension. The operator may be the automorphism or its difference from
the identity; only literal commutation is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LinearCentralizerTwoStringEvaluation

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_le_of_basis_strings [Finite V] [Finite I]
    (b : Module.Basis I K V) (e : V ≃ₗ[K] V) (T : V →ₗ[K] V)
    (idx : Fin 4 → I) (hinj : Function.Injective idx)
    (h01 : T (b (idx 0)) = b (idx 1)) (h23 : T (b (idx 2)) = b (idx 3))
    (hcomm : ∀ a : V ≃ₗ[K] V, Commute e a → ∀ x, a (T x) = T (a x)) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) ^ 2 * Nat.card V ^ (Nat.card I - 4) := by
  let J := {l : I // l ≠ idx 0 ∧ l ≠ idx 1 ∧ l ≠ idx 2 ∧ l ≠ idx 3}
  let U := {v : V // v ≠ 0}
  let chart : {a : V ≃ₗ[K] V // Commute e a} → (U × U) × (J → V) := fun a =>
    ((⟨a.val (b (idx 0)), fun hz => b.ne_zero (idx 0)
        (a.val.injective (hz.trans (map_zero a.val).symm))⟩,
      ⟨a.val (b (idx 2)), fun hz => b.ne_zero (idx 2)
        (a.val.injective (hz.trans (map_zero a.val).symm))⟩),
      fun l => a.val (b l.val))
  have hchart : Function.Injective chart := by
    intro a a' haa
    have h0 : a.val (b (idx 0)) = a'.val (b (idx 0)) :=
      congrArg (fun z : (U × U) × (J → V) => z.1.1.val) haa
    have h2 : a.val (b (idx 2)) = a'.val (b (idx 2)) :=
      congrArg (fun z : (U × U) × (J → V) => z.1.2.val) haa
    have h1 : a.val (b (idx 1)) = a'.val (b (idx 1)) := by
      rw [← h01, hcomm a.val a.property, hcomm a'.val a'.property, h0]
    have h3 : a.val (b (idx 3)) = a'.val (b (idx 3)) := by
      rw [← h23, hcomm a.val a.property, hcomm a'.val a'.property, h2]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro l
    change a.val (b l) = a'.val (b l)
    by_cases hl0 : l = idx 0
    · simpa only [hl0] using h0
    by_cases hl1 : l = idx 1
    · simpa only [hl1] using h1
    by_cases hl2 : l = idx 2
    · simpa only [hl2] using h2
    by_cases hl3 : l = idx 3
    · simpa only [hl3] using h3
    exact congrArg (fun z : (U × U) × (J → V) => z.2 ⟨l, hl0, hl1, hl2, hl3⟩) haa
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype V := Fintype.ofFinite V
  have hU : Nat.card U = Nat.card V - 1 := by
    simp only [U, Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl]
  have hJ : Nat.card J = Nat.card I - 4 := by
    let f : J ≃ ↥(({idx 0, idx 1, idx 2, idx 3} : Finset I)ᶜ) := {
      toFun := fun l => ⟨l.val, by simpa using l.property⟩
      invFun := fun l => ⟨l.val, by simpa using l.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have ht : ({idx 0, idx 1, idx 2, idx 3} : Finset I).card = 4 := by
      simp [hinj.ne (by decide : (0 : Fin 4) ≠ 1), hinj.ne (by decide : (0 : Fin 4) ≠ 2),
        hinj.ne (by decide : (0 : Fin 4) ≠ 3), hinj.ne (by decide : (1 : Fin 4) ≠ 2),
        hinj.ne (by decide : (1 : Fin 4) ≠ 3), hinj.ne (by decide : (2 : Fin 4) ≠ 3)]
    rw [Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_coe,
      Finset.card_compl, ht, Nat.card_eq_fintype_card]
  calc
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ Nat.card ((U × U) × (J → V)) :=
      Nat.card_le_card_of_injective chart hchart
    _ = (Nat.card V - 1) ^ 2 * Nat.card V ^ (Nat.card I - 4) := by
      rw [Nat.card_prod, Nat.card_prod, Nat.card_fun, hU, hJ, pow_two]

theorem card_le_of_independent_strings [Finite V]
    (e : V ≃ₗ[K] V) (T : V →ₗ[K] V) (v u : V)
    (hfour : LinearIndependent K ![v, T v, u, T u])
    (hcomm : ∀ a : V ≃ₗ[K] V, Commute e a → ∀ x, a (T x) = T (a x)) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) ^ 2 * Nat.card V ^ (Module.finrank K V - 4) := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let hs := hfour.linearIndepOn_id
  let B := hs.extend (Set.subset_univ _)
  let b : Module.Basis B K V := Module.Basis.extend hs
  let idx : Fin 4 → B := fun r => ⟨![v, T v, u, T u] r, hs.subset_extend _ ⟨r, rfl⟩⟩
  have hinj : Function.Injective idx := by
    intro r s h
    exact hfour.injective (congrArg Subtype.val h)
  have h0 : b (idx 0) = v := Module.Basis.extend_apply_self hs (idx 0)
  have h1 : b (idx 1) = T v := Module.Basis.extend_apply_self hs (idx 1)
  have h2 : b (idx 2) = u := Module.Basis.extend_apply_self hs (idx 2)
  have h3 : b (idx 3) = T u := Module.Basis.extend_apply_self hs (idx 3)
  have hc := card_le_of_basis_strings b e T idx hinj (by rw [h0, h1]) (by rw [h2, h3]) hcomm
  letI : Fintype B := Fintype.ofFinite B
  have hd : Module.finrank K V = Nat.card B := by
    simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_card_basis b
  simpa only [hd] using hc

end SymmetricSubgroupAsymptotics.LinearCentralizerTwoStringEvaluation
