import SymmetricSubgroupAsymptotics.LinearCentralizerSparseEvaluation
import Mathlib.Tactic.FinCases

/-! Two actual two-vector orbits forming a basis give a two-value
centralizer chart. In dimension four over F2 the resulting bound is
225, with no field-extension or Jordan-form census. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LinearCentralizerTwoPairEvaluation
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

theorem card_le_of_basis_pairs (b : Module.Basis (Fin 4) K V) (e : V ≃ₗ[K] V)
    (he01 : e (b 0)=b 1) (he23 : e (b 2)=b 3) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ (Nat.card V-1)^2 := by
  let chart : {a : V ≃ₗ[K] V // Commute e a} →
      {v : V // v≠0} × {v : V // v≠0} := fun a =>
    (⟨a.val (b 0),fun hz => b.ne_zero 0
      (a.val.injective (hz.trans (map_zero a.val).symm))⟩,
     ⟨a.val (b 2),fun hz => b.ne_zero 2
      (a.val.injective (hz.trans (map_zero a.val).symm))⟩)
  have hchart : Function.Injective chart := by
    intro a a' haa
    have h0 : a.val (b 0)=a'.val (b 0) :=
      congrArg (fun z : {v : V // v≠0} × {v : V // v≠0} => z.1.val) haa
    have h2 : a.val (b 2)=a'.val (b 2) :=
      congrArg (fun z : {v : V // v≠0} × {v : V // v≠0} => z.2.val) haa
    have hnext (a : {a : V ≃ₗ[K] V // Commute e a}) (v : V) :
        a.val (e v)=e (a.val v) :=
      (congrArg (fun f : V ≃ₗ[K] V => f v) a.property).symm
    have h1 : a.val (b 1)=a'.val (b 1) := by
      rw [←he01,hnext a (b 0),hnext a' (b 0),h0]
    have h3 : a.val (b 3)=a'.val (b 3) := by
      rw [←he23,hnext a (b 2),hnext a' (b 2),h2]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change a.val (b i)=a'.val (b i)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hc : Nat.card {v : V // v≠0}=Nat.card V-1 := by
    letI : Fintype V := Fintype.ofFinite V
    simp only [Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl]
  calc
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
        Nat.card ({v : V // v≠0} × {v : V // v≠0}) :=
      Nat.card_le_card_of_injective chart hchart
    _ = (Nat.card V-1)^2 := by rw [Nat.card_prod,hc,pow_two]

theorem card_le_of_basis_difference_pairs (b : Module.Basis (Fin 4) K V) (e : V ≃ₗ[K] V)
    (he01 : e (b 0)=b 0+b 1) (he23 : e (b 2)=b 2+b 3) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤ (Nat.card V-1)^2 := by
  let chart : {a : V ≃ₗ[K] V // Commute e a} →
      {v : V // v≠0} × {v : V // v≠0} := fun a =>
    (⟨a.val (b 0),fun hz => b.ne_zero 0
      (a.val.injective (hz.trans (map_zero a.val).symm))⟩,
     ⟨a.val (b 2),fun hz => b.ne_zero 2
      (a.val.injective (hz.trans (map_zero a.val).symm))⟩)
  have hchart : Function.Injective chart := by
    intro a a' haa
    have h0 : a.val (b 0)=a'.val (b 0) :=
      congrArg (fun z : {v : V // v≠0} × {v : V // v≠0} => z.1.val) haa
    have h2 : a.val (b 2)=a'.val (b 2) :=
      congrArg (fun z : {v : V // v≠0} × {v : V // v≠0} => z.2.val) haa
    have hnext (a : {a : V ≃ₗ[K] V // Commute e a}) (v : V) :
        a.val (e v)=e (a.val v) :=
      (congrArg (fun f : V ≃ₗ[K] V => f v) a.property).symm
    have hfirst (a : {a : V ≃ₗ[K] V // Commute e a}) :
        a.val (b 1)=e (a.val (b 0))-a.val (b 0) := by
      have h := hnext a (b 0)
      rw [he01,map_add] at h
      exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans h)
    have hsecond (a : {a : V ≃ₗ[K] V // Commute e a}) :
        a.val (b 3)=e (a.val (b 2))-a.val (b 2) := by
      have h := hnext a (b 2)
      rw [he23,map_add] at h
      exact (eq_sub_iff_add_eq).mpr ((add_comm _ _).trans h)
    have h1 : a.val (b 1)=a'.val (b 1) := by rw [hfirst,hfirst,h0]
    have h3 : a.val (b 3)=a'.val (b 3) := by rw [hsecond,hsecond,h2]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change a.val (b i)=a'.val (b i)
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hc : Nat.card {v : V // v≠0}=Nat.card V-1 := by
    letI : Fintype V := Fintype.ofFinite V
    simp only [Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl]
  calc
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
        Nat.card ({v : V // v≠0} × {v : V // v≠0}) :=
      Nat.card_le_card_of_injective chart hchart
    _ = (Nat.card V-1)^2 := by rw [Nat.card_prod,hc,pow_two]

end SymmetricSubgroupAsymptotics.LinearCentralizerTwoPairEvaluation
