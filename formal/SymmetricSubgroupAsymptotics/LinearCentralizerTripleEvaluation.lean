import SymmetricSubgroupAsymptotics.LinearCentralizerSparseEvaluation

/-! Three independent successive orbit vectors save two complete
columns in the actual automorphism centralizer chart. This needs no
minimal polynomial or rational canonical form. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.LinearCentralizerTripleEvaluation
variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem card_le_of_basis_triple [Finite V] [Finite I]
    (b : Module.Basis I K V) (e : V ≃ₗ[K] V) (i j k : I)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (he1 : e (b i)=b j) (he2 : e (b j)=b k) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V-1)*Nat.card V^(Nat.card I-3) := by
  let J := {l : I // l≠i ∧ l≠j ∧ l≠k}
  let chart : {a : V ≃ₗ[K] V // Commute e a} →
      {v : V // v≠0} × (J→V) := fun a =>
    (⟨a.val (b i),fun hz => b.ne_zero i
      (a.val.injective (hz.trans (map_zero a.val).symm))⟩,
      fun l => a.val (b l.val))
  have hchart : Function.Injective chart := by
    intro a a' haa
    have hi : a.val (b i)=a'.val (b i) :=
      congrArg (fun z : {v : V // v≠0} × (J→V) => z.1.val) haa
    have hnext (a : {a : V ≃ₗ[K] V // Commute e a}) (v : V) :
        a.val (e v)=e (a.val v) := by
      exact (congrArg (fun f : V ≃ₗ[K] V => f v) a.property).symm
    have hj (a : {a : V ≃ₗ[K] V // Commute e a}) :
        a.val (b j)=e (a.val (b i)) := by rw [←he1]; exact hnext a (b i)
    have hk (a : {a : V ≃ₗ[K] V // Commute e a}) :
        a.val (b k)=e (e (a.val (b i))) := by
      rw [←he2,hnext a (b j),hj a]
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro l
    change a.val (b l)=a'.val (b l)
    by_cases hli : l=i
    · simpa only [hli] using hi
    by_cases hlj : l=j
    · subst l
      exact (hj a).trans ((congrArg e hi).trans (hj a').symm)
    by_cases hlk : l=k
    · subst l
      exact (hk a).trans ((congrArg (fun v => e (e v)) hi).trans (hk a').symm)
    · exact congrArg (fun z : {v : V // v≠0} × (J→V) =>
        z.2 ⟨l,hli,hlj,hlk⟩) haa
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype I := Fintype.ofFinite I
  have hnonzero : Nat.card {v : V // v≠0}=Nat.card V-1 := by
    simp only [Nat.card_eq_fintype_card]
    simp [Fintype.card_subtype_compl]
  have hJ : Nat.card J=Nat.card I-3 := by
    let a : J ≃ ↥(({i,j,k} : Finset I)ᶜ) := {
      toFun := fun l => ⟨l.val,by simpa using l.property⟩
      invFun := fun l => ⟨l.val,by simpa using l.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    have ht : ({i,j,k} : Finset I).card=3 := by simp [hij,hik,hjk]
    rw [Nat.card_congr a,Nat.card_eq_fintype_card,Fintype.card_coe,
      Finset.card_compl,ht,Nat.card_eq_fintype_card]
  calc
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
        Nat.card ({v : V // v≠0} × (J→V)) :=
      Nat.card_le_card_of_injective chart hchart
    _ = (Nat.card V-1)*Nat.card V^(Nat.card I-3) := by
      rw [Nat.card_prod,Nat.card_fun,hnonzero,hJ]

theorem card_le_of_independent_triple [Finite V]
    (e : V ≃ₗ[K] V) (v : V) (hv : LinearIndependent K ![v,e v,e (e v)]) :
    Nat.card {a : V ≃ₗ[K] V // Commute e a} ≤
      (Nat.card V-1)*Nat.card V^(Module.finrank K V-3) := by
  letI : FiniteDimensional K V := Module.Finite.of_finite
  let hs := hv.linearIndepOn_id
  let B := hs.extend (Set.subset_univ _)
  let b : Module.Basis B K V := Module.Basis.extend hs
  let a : Fin 3→B := fun r => ⟨![v,e v,e (e v)] r,hs.subset_extend _ ⟨r,rfl⟩⟩
  have hinj : Function.Injective a := by
    intro r s h
    exact hv.injective (congrArg Subtype.val h)
  have hi : b (a 0)=v := Module.Basis.extend_apply_self hs (a 0)
  have hj : b (a 1)=e v := Module.Basis.extend_apply_self hs (a 1)
  have hk : b (a 2)=e (e v) := Module.Basis.extend_apply_self hs (a 2)
  have hc := card_le_of_basis_triple b e (a 0) (a 1) (a 2)
    (hinj.ne (by decide)) (hinj.ne (by decide)) (hinj.ne (by decide))
    (by rw [hi,hj]) (by rw [hj,hk])
  letI : Fintype B := Fintype.ofFinite B
  have hd : Module.finrank K V=Nat.card B := by
    simpa only [Nat.card_eq_fintype_card] using Module.finrank_eq_card_basis b
  simpa only [hd] using hc

end SymmetricSubgroupAsymptotics.LinearCentralizerTripleEvaluation
