import Mathlib.LinearAlgebra.Center
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! A nonscalar invertible linear map has a sparse centralizer chart: its
commuting automorphisms are determined by a nonzero value on one vector
and arbitrary values on all but two basis vectors. No canonical form or
matrix census is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LinearCentralizerSparseEvaluation

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_le_of_basis_pair [Finite V] [Finite I]
    (b : Module.Basis I K V) (e : V ≃ₗ[K] V) (i j : I)
    (hij : i ≠ j) (he : e (b i) = b j) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) * Nat.card V ^ (Nat.card I - 2) := by
  let J := {k : I // k ≠ i ∧ k ≠ j}
  let chart : {a : V ≃ₗ[K] V // Commute e a} →
      {v : V // v ≠ 0} × (J → V) := fun a =>
    (⟨a.val (b i), fun hz => b.ne_zero i
      (a.val.injective (hz.trans (map_zero a.val).symm))⟩,
      fun k => a.val (b k.val))
  have hchart : Function.Injective chart := by
    intro a a' haa
    have hi : a.val (b i) = a'.val (b i) :=
      congrArg (fun z : {v : V // v ≠ 0} × (J → V) => z.1.val) haa
    have hj (t : {a : V ≃ₗ[K] V // Commute e a}) :
        t.val (b j) = e (t.val (b i)) := by
      have hc := congrArg (fun f : V ≃ₗ[K] V => f (b i)) t.property
      change e (t.val (b i)) = t.val (e (b i)) at hc
      exact (congrArg t.val he).symm.trans hc.symm
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro k
    change a.val (b k) = a'.val (b k)
    by_cases hki : k = i
    · simpa only [hki] using hi
    by_cases hkj : k = j
    · subst k
      exact (hj a).trans ((congrArg e hi).trans (hj a').symm)
    · exact congrArg (fun z : {v : V // v ≠ 0} × (J → V) =>
        z.2 ⟨k, hki, hkj⟩) haa
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype I := Fintype.ofFinite I
  have hnonzero : Nat.card {v : V // v ≠ 0} = Nat.card V - 1 := by
    simp only [Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl]
  have hJ : Nat.card J = Nat.card I - 2 := by
    let a : J ≃ ↥(({i, j} : Finset I)ᶜ) := {
      toFun := fun k => ⟨k.val, by simpa using k.property⟩
      invFun := fun k => ⟨k.val, by simpa using k.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Nat.card_congr a, Nat.card_eq_fintype_card, Fintype.card_coe,
      Finset.card_compl, Finset.card_pair hij, Nat.card_eq_fintype_card]
  calc
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
        Nat.card ({v : V // v ≠ 0} × (J → V)) :=
      Nat.card_le_card_of_injective chart hchart
    _ = (Nat.card V - 1) * Nat.card V ^ (Nat.card I - 2) := by
      rw [Nat.card_prod, Nat.card_fun, hnonzero, hJ]

theorem card_le_of_independent_pair [Finite V]
    (e : V ≃ₗ[K] V) (v : V) (hv : LinearIndependent K ![v, e v]) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) * Nat.card V ^ (Module.finrank K V - 2) := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let hs := hv.linearIndepOn_id
  let B := hs.extend (Set.subset_univ _)
  let b : Module.Basis B K V := Module.Basis.extend hs
  let i : B := ⟨v, hs.subset_extend _ ⟨0, by simp⟩⟩
  let j : B := ⟨e v, hs.subset_extend _ ⟨1, by simp⟩⟩
  have hij : i ≠ j := by
    intro h
    have hve : v = e v := congrArg Subtype.val h
    exact (by decide : (0 : Fin 2) ≠ 1) (hv.injective (by simpa using hve))
  have hi : b i = v := Module.Basis.extend_apply_self hs i
  have hj : b j = e v := Module.Basis.extend_apply_self hs j
  have hc := card_le_of_basis_pair b e i j hij (by rw [hi, hj])
  letI : Fintype B := Fintype.ofFinite B
  have hd : Module.finrank K V = Nat.card B := by
    simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_card_basis b
  simpa only [hd] using hc

theorem card_le_of_nonscalar [Finite V] (e : V ≃ₗ[K] V)
    (he : ¬ ∃c : K, e.toLinearMap = c • (1 : V →ₗ[K] V)) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) * Nat.card V ^ (Module.finrank K V - 2) := by
  have hv : ∃v : V, LinearIndependent K ![v, e v] := by
    by_contra h
    apply he
    exact LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
      (f := e.toLinearMap) (by simpa only [not_exists] using h)
  obtain ⟨v, hv⟩ := hv
  exact card_le_of_independent_pair e v hv

end SymmetricSubgroupAsymptotics.LinearCentralizerSparseEvaluation
