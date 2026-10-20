import SymmetricSubgroupAsymptotics.SchurIsotypicGenerators
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.BigOperators.Fin

/-! Genuine generators add along the kernel filtration of a finite
jointly injective family of original module coordinates. No splitting is
assumed, even when the coefficient ring is not semisimple. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.ModuleGeneratedBy

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

theorem of_submodule_quotient (K : Submodule R M) {m n : ℕ}
    (hK : ModuleGeneratedBy R K m) (hQ : ModuleGeneratedBy R (M⧸K) n) :
    ModuleGeneratedBy R M (m+n) := by
  obtain ⟨u,hu⟩ := hK
  obtain ⟨q,hq⟩ := hQ
  let lift : M⧸K → M := Function.surjInv K.mkQ_surjective
  have hlift (w : M⧸K) : K.mkQ (lift w)=w := Function.rightInverse_surjInv K.mkQ_surjective w
  let v : Fin (m+n) → M := Fin.addCases (fun j => (u j : M)) (fun j => lift (q j))
  let P : Submodule R M := Submodule.span R (Set.range v)
  have huP (j : Fin m) : (u j : M)∈P := by
    apply Submodule.subset_span
    exact ⟨Fin.castAdd n j,by simp only [v,Fin.addCases_left]⟩
  have hqP (j : Fin n) : lift (q j)∈P := by
    apply Submodule.subset_span
    exact ⟨Fin.natAdd m j,by simp only [v,Fin.addCases_right]⟩
  have hKP : K≤P := by
    have hle : Submodule.span R (Set.range u)≤P.comap K.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j,rfl⟩
      exact huP j
    rw [hu] at hle
    intro x hx
    exact hle (show (⟨x,hx⟩ : K)∈⊤ from Submodule.mem_top)
  have hmap : P.map K.mkQ=⊤ := by
    apply top_unique
    rw [←hq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨lift (q j),hqP j,hlift (q j)⟩
  refine ⟨v,top_unique ?_⟩
  intro x _
  have hx : K.mkQ x∈P.map K.mkQ := by rw [hmap]; exact Submodule.mem_top
  obtain ⟨y,hy,hxy⟩ := hx
  have hd : x-y∈K := by
    apply (Submodule.Quotient.mk_eq_zero K).mp
    change K.mkQ (x-y)=0
    rw [map_sub,hxy,sub_self]
  have hm := P.add_mem (hKP hd) hy
  simpa only [sub_add_cancel] using hm

/-- Coordinate bounds apply to arbitrary submodules of each actual
coordinate, so they can be used at each kernel-filtration step. -/
theorem of_coordinate_bounds (n : ℕ) (V : Fin n → Type)
    [∀ i,AddCommGroup (V i)] [∀ i,Module R (V i)]
    (b : Fin n → ℕ) (hb : ∀ i (S : Submodule R (V i)),ModuleGeneratedBy R S (b i))
    (f : ∀ i,M →ₗ[R] V i) (hf : Function.Injective (fun x i => f i x)) :
    ModuleGeneratedBy R M (∑ i,b i) := by
  induction n generalizing M with
  | zero =>
    rw [Fin.sum_univ_zero]
    have hM : Subsingleton M := ⟨fun x y => hf (funext (fun i => Fin.elim0 i))⟩
    refine ⟨fun i => Fin.elim0 i,top_unique ?_⟩
    intro x _
    rw [hM.elim x 0]
    exact Submodule.zero_mem _
  | succ n ih =>
    let K := LinearMap.ker (f 0)
    let tail : ∀ i : Fin n,K →ₗ[R] V i.succ := fun i => (f i.succ).comp K.subtype
    have ht : Function.Injective (fun x i => tail i x) := by
      intro x y h
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact x.property.trans y.property.symm
      · exact congrFun h j
    have hk := ih (fun i : Fin n => V i.succ) (fun i => b i.succ)
      (fun i => hb i.succ) tail ht
    have hq : ModuleGeneratedBy R (M⧸K) (b 0) :=
      congr (f 0).quotKerEquivRange.symm (hb 0 (LinearMap.range (f 0)))
    have h := of_submodule_quotient K hk hq
    simpa only [Fin.sum_univ_succ,Nat.add_comm] using h

/-- Reindexing a finite family preserves the original maps and modules. -/
theorem of_finite_coordinate_bounds {I : Type} [Fintype I]
    (V : I → Type) [∀ i,AddCommGroup (V i)] [∀ i,Module R (V i)]
    (b : I → ℕ) (hb : ∀ i (S : Submodule R (V i)),ModuleGeneratedBy R S (b i))
    (f : ∀ i,M →ₗ[R] V i) (hf : Function.Injective (fun x i => f i x)) :
    ModuleGeneratedBy R M (∑ i,b i) := by
  let e := (Fintype.equivFin I).symm
  have hi : Function.Injective (fun x j => f (e j) x) := by
    intro x y h
    apply hf
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun h j
  have h := of_coordinate_bounds (Fintype.card I) (fun j => V (e j))
    (fun j => b (e j)) (fun j => hb (e j)) (fun j => f (e j)) hi
  simpa only [e.sum_comp] using h

end SymmetricSubgroupAsymptotics.ModuleGeneratedBy
