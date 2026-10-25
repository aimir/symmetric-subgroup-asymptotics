import SymmetricSubgroupAsymptotics.IndependentSpanComplementCardinality
import SymmetricSubgroupAsymptotics.LinearCentralizerTripleEvaluation
import Mathlib.Tactic.FinCases

/-! A centralizing automorphism sends each remaining basis vector outside
the span of the three orbit images. The chart retains this independence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.LinearCentralizerTripleSharpEvaluation

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_le_of_basis_triple [Finite V] [Finite I]
    (b : Module.Basis I K V) (e : V ≃ₗ[K] V) (i j k : I)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (he1 : e (b i) = b j) (he2 : e (b j) = b k) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) * (Nat.card V - Nat.card K ^ 3) ^ (Nat.card I - 3) := by
  let J := {l : I // l ≠ i ∧ l ≠ j ∧ l ≠ k}
  let U := {v : V // LinearIndependent K ![v, e v, e (e v)]}
  let s : U → Fin 3 → V := fun u => ![u.val, e u.val, e (e u.val)]
  let idx : Fin 3 → I := ![i, j, k]
  have hidx : Function.Injective idx := by
    intro r t h
    fin_cases r <;> fin_cases t <;> simp_all [idx]
  have hnext (a : {a : V ≃ₗ[K] V // Commute e a}) (v : V) :
      a.val (e v) = e (a.val v) :=
    (congrArg (fun f : V ≃ₗ[K] V => f v) a.property).symm
  have hframe (a : {a : V ≃ₗ[K] V // Commute e a}) :
      (fun r : Fin 3 => (b.map a.val) (idx r)) =
        ![a.val (b i), e (a.val (b i)), e (e (a.val (b i)))] := by
    funext r
    fin_cases r
    · rfl
    · change a.val (b j) = e (a.val (b i))
      rw [← he1, hnext]
    · change a.val (b k) = e (e (a.val (b i)))
      rw [← he2, hnext, ← he1, hnext]
  have hfirst (a : {a : V ≃ₗ[K] V // Commute e a}) :
      LinearIndependent K ![a.val (b i), e (a.val (b i)), e (e (a.val (b i)))] := by
    rw [← hframe a]
    exact (b.map a.val).linearIndependent.comp idx hidx
  have hout (a : {a : V ≃ₗ[K] V // Commute e a}) (l : J) :
      a.val (b l.val) ∉ Submodule.span K
        (Set.range ![a.val (b i), e (a.val (b i)), e (e (a.val (b i)))]) := by
    have hl : l.val ∉ Set.range idx := by
      rintro ⟨r, hr⟩
      fin_cases r
      · exact l.property.1 hr.symm
      · exact l.property.2.1 hr.symm
      · exact l.property.2.2 hr.symm
    have hh := (b.map a.val).linearIndependent.notMem_span_image hl
    have hh' : a.val (b l.val) ∉ Submodule.span K
        (Set.range (fun r : Fin 3 => (b.map a.val) (idx r))) := by
      simpa only [← Set.range_comp, Function.comp_def, Module.Basis.map_apply] using hh
    rw [hframe a] at hh'
    exact hh'
  let chart : {a : V ≃ₗ[K] V // Commute e a} →
      ((u : U) × (J → {v : V // v ∉ Submodule.span K (Set.range (s u))})) :=
    fun a => ⟨⟨a.val (b i), hfirst a⟩, fun l => ⟨a.val (b l.val), hout a l⟩⟩
  have hchart : Function.Injective chart := by
    intro a a' haa
    have hi : a.val (b i) = a'.val (b i) :=
      congrArg (fun z : ((u : U) ×
        (J → {v : V // v ∉ Submodule.span K (Set.range (s u))})) => z.1.val) haa
    have hj : a.val (b j) = a'.val (b j) := by
      rw [← he1, hnext, hnext, hi]
    have hk : a.val (b k) = a'.val (b k) := by
      rw [← he2, hnext, hnext, hj]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro l
    change a.val (b l) = a'.val (b l)
    by_cases hli : l = i
    · simpa only [hli] using hi
    by_cases hlj : l = j
    · simpa only [hlj] using hj
    by_cases hlk : l = k
    · simpa only [hlk] using hk
    exact congrArg (fun z : ((u : U) ×
      (J → {v : V // v ∉ Submodule.span K (Set.range (s u))})) =>
        (z.2 ⟨l, hli, hlj, hlk⟩).val) haa
  letI : Fintype I := Fintype.ofFinite I
  letI : Fintype U := Fintype.ofFinite U
  have hJ : Nat.card J = Nat.card I - 3 := by
    let f : J ≃ ↥(({i, j, k} : Finset I)ᶜ) := {
      toFun := fun l => ⟨l.val, by simpa using l.property⟩
      invFun := fun l => ⟨l.val, by simpa using l.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have ht : ({i, j, k} : Finset I).card = 3 := by simp [hij, hik, hjk]
    rw [Nat.card_congr f, Nat.card_eq_fintype_card, Fintype.card_coe,
      Finset.card_compl, ht, Nat.card_eq_fintype_card]
  have hU : Nat.card U ≤ Nat.card V - 1 := by
    let f : U → {v : V // v ≠ 0} := fun u => ⟨u.val, u.property.ne_zero 0⟩
    have hf : Function.Injective f := by
      intro u v h
      apply Subtype.ext
      exact congrArg (fun z : {v : V // v ≠ 0} => z.val) h
    have hc : Nat.card {v : V // v ≠ 0} = Nat.card V - 1 := by
      letI : Fintype V := Fintype.ofFinite V
      simp only [Nat.card_eq_fintype_card]
      simp [Fintype.card_subtype_compl]
    exact (Nat.card_le_card_of_injective f hf).trans_eq hc
  have hcard : Nat.card ((u : U) ×
      (J → {v : V // v ∉ Submodule.span K (Set.range (s u))})) =
        Nat.card U * (Nat.card V - Nat.card K ^ 3) ^ (Nat.card I - 3) := by
    have hc (u : U) := IndependentSpanComplementCardinality.card_complement_span
      (s u) u.property
    rw [Nat.card_sigma]
    simp_rw [Nat.card_fun, hc, hJ]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Nat.card_eq_fintype_card, Nat.cast_id]
  exact (Nat.card_le_card_of_injective chart hchart).trans
    (hcard.le.trans (Nat.mul_le_mul_right _ hU))

theorem card_le_of_independent_triple [Finite V]
    (e : V ≃ₗ[K] V) (v : V) (hv : LinearIndependent K ![v, e v, e (e v)]) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) * (Nat.card V - Nat.card K ^ 3) ^ (Module.finrank K V - 3) := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let hs := hv.linearIndepOn_id
  let B := hs.extend (Set.subset_univ _)
  let b : Module.Basis B K V := Module.Basis.extend hs
  let a : Fin 3 → B := fun r => ⟨![v, e v, e (e v)] r, hs.subset_extend _ ⟨r, rfl⟩⟩
  have hinj : Function.Injective a := by
    intro r s h
    exact hv.injective (congrArg Subtype.val h)
  have hi : b (a 0) = v := Module.Basis.extend_apply_self hs (a 0)
  have hj : b (a 1) = e v := Module.Basis.extend_apply_self hs (a 1)
  have hk : b (a 2) = e (e v) := Module.Basis.extend_apply_self hs (a 2)
  have hc := card_le_of_basis_triple b e (a 0) (a 1) (a 2)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (by rw [hi, hj]) (by rw [hj, hk])
  letI : Fintype B := Fintype.ofFinite B
  have hd : Module.finrank K V = Nat.card B := by
    simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_card_basis b
  simpa only [hd] using hc

end SymmetricSubgroupAsymptotics.LinearCentralizerTripleSharpEvaluation
