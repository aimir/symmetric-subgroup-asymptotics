import SymmetricSubgroupAsymptotics.IndependentSpanComplementCardinality
import SymmetricSubgroupAsymptotics.LinearCentralizerTwoPairEvaluation

/-! Two actual independent two-vector strings constrain the second free
image to the complement of the first image plane. This counts sparse
centralizer charts without enumerating linear groups. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LinearCentralizerTwoPairSharpEvaluation

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Finite V]

private theorem two_value_bound {C : Type*} (b : Module.Basis (Fin 4) K V)
    (T : V →ₗ[K] V) (hT0 : T (b 0) = b 1) (hT2 : T (b 2) = b 3)
    (a : C → V ≃ₗ[K] V) (ha : Function.Injective a)
    (hcomm : ∀ c x, a c (T x) = T (a c x)) :
    Nat.card C ≤ (Nat.card V - 1) * (Nat.card V - Nat.card K ^ 2) := by
  let U := {v : V // LinearIndependent K ![v, T v]}
  let s : U → Fin 2 → V := fun u => ![u.val, T u.val]
  have hs (u : U) : LinearIndependent K (s u) := u.property
  have hframe (c : C) : LinearIndependent K (fun i : Fin 2 =>
      a c (b (Fin.castAdd 2 i))) :=
    (b.map (a c)).linearIndependent.comp _ (Fin.castAdd_injective 2 2)
  have hfirst (c : C) : LinearIndependent K ![a c (b 0), T (a c (b 0))] := by
    have heq : (fun i : Fin 2 => a c (b (Fin.castAdd 2 i))) =
        ![a c (b 0), T (a c (b 0))] := by
      funext i
      fin_cases i
      · rfl
      · exact (congrArg (a c) hT0).symm.trans (hcomm c (b 0))
    rw [← heq]
    exact hframe c
  have hout (c : C) : a c (b 2) ∉
      Submodule.span K (Set.range ![a c (b 0), T (a c (b 0))]) := by
    have hindex : (2 : Fin 4) ∉ Set.range (Fin.castAdd 2 : Fin 2 → Fin 4) := by
      rintro ⟨i, hi⟩
      fin_cases i <;> simp at hi
    have hh := (b.map (a c)).linearIndependent.notMem_span_image hindex
    have heq : (fun i : Fin 2 => (b.map (a c)) (Fin.castAdd 2 i)) =
        ![a c (b 0), T (a c (b 0))] := by
      funext i
      fin_cases i
      · rfl
      · exact (congrArg (a c) hT0).symm.trans (hcomm c (b 0))
    have hh' : a c (b 2) ∉ Submodule.span K
        (Set.range (fun i : Fin 2 => (b.map (a c)) (Fin.castAdd 2 i))) := by
      simpa only [← Set.range_comp, Function.comp_def, Module.Basis.map_apply] using hh
    rw [heq] at hh'
    exact hh'
  let chart : C → ((u : U) × {v : V // v ∉ Submodule.span K (Set.range (s u))}) :=
    fun c => ⟨⟨a c (b 0), hfirst c⟩, ⟨a c (b 2), hout c⟩⟩
  have hchart : Function.Injective chart := by
    intro c d hcd
    have h0 : a c (b 0) = a d (b 0) :=
      congrArg (fun z : ((u : U) × {v : V // v ∉ Submodule.span K (Set.range (s u))}) =>
        z.1.val) hcd
    have h2 : a c (b 2) = a d (b 2) :=
      congrArg (fun z : ((u : U) × {v : V // v ∉ Submodule.span K (Set.range (s u))}) =>
        z.2.val) hcd
    apply ha
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    change a c (b i) = a d (b i)
    fin_cases i
    · exact h0
    · change a c (b 1) = a d (b 1)
      rw [← hT0, hcomm, hcomm, h0]
    · exact h2
    · change a c (b 3) = a d (b 3)
      rw [← hT2, hcomm, hcomm, h2]
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
  calc
    Nat.card C ≤ Nat.card ((u : U) × {v : V // v ∉ Submodule.span K (Set.range (s u))}) :=
      Nat.card_le_card_of_injective chart hchart
    _ = Nat.card U * (Nat.card V - Nat.card K ^ 2) :=
      IndependentSpanComplementCardinality.card_sigma_complement_span s hs
    _ ≤ (Nat.card V - 1) * (Nat.card V - Nat.card K ^ 2) := Nat.mul_le_mul_right _ hU

theorem card_le_of_basis_pairs (b : Module.Basis (Fin 4) K V) (e : V ≃ₗ[K] V)
    (he01 : e (b 0) = b 1) (he23 : e (b 2) = b 3) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) * (Nat.card V - Nat.card K ^ 2) := by
  apply two_value_bound b e.toLinearMap he01 he23 Subtype.val Subtype.val_injective
  intro a x
  exact (congrArg (fun f : V ≃ₗ[K] V => f x) a.property).symm

theorem card_le_of_basis_difference_pairs (b : Module.Basis (Fin 4) K V)
    (e : V ≃ₗ[K] V) (he01 : e (b 0) = b 0 + b 1)
    (he23 : e (b 2) = b 2 + b 3) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V - 1) * (Nat.card V - Nat.card K ^ 2) := by
  let T : V →ₗ[K] V := e.toLinearMap - LinearMap.id
  have h0 : T (b 0) = b 1 := by change e (b 0) - b 0 = b 1; rw [he01]; abel
  have h2 : T (b 2) = b 3 := by change e (b 2) - b 2 = b 3; rw [he23]; abel
  apply two_value_bound b T h0 h2 Subtype.val Subtype.val_injective
  intro a x
  change a.val (e x - x) = e (a.val x) - a.val x
  rw [map_sub]
  exact congrArg (fun y : V => y - a.val x)
    (congrArg (fun f : V ≃ₗ[K] V => f x) a.property).symm

end SymmetricSubgroupAsymptotics.LinearCentralizerTwoPairSharpEvaluation
