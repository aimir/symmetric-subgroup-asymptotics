import SymmetricSubgroupAsymptotics.SchurFiniteLength
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.BigOperators.Fin

/-! An actual submodule of a finite product inherits head bounds from
actual submodules of its coordinates. The proof filters by the kernels
of the original coordinate maps; it does not assume semisimplicity or
extension of characters from a submodule. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace SymmetricSubgroupAsymptotics
universe u
variable {k R A : Type u} [Field k] [Ring R] [Algebra k R]
    [AddCommGroup A] [Module R A] [Module k A] [IsScalarTower k R A]

def moduleHomDomainEquiv {M N : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M≃ₗ[R]N) : (M→ₗ[R]A)≃ₗ[k](N→ₗ[R]A) where
  toFun f := f.comp e.symm.toLinearMap
  invFun f := f.comp e.toLinearMap
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Bounds for all literal coordinate submodules apply to any jointly
injective finite family of original module maps. -/
theorem moduleHom_finrank_le_coordinate_bounds [FiniteDimensional k A] (n : ℕ)
    (V : Fin n→Type u) [∀ i,AddCommGroup (V i)] [∀ i,Module R (V i)]
    [∀ i,Module k (V i)] [∀ i,IsScalarTower k R (V i)]
    (b : Fin n→ℕ)
    (hb : ∀ i (S : Submodule R (V i)),Module.finrank k (S→ₗ[R]A)≤b i)
    (M : Type u) [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] [FiniteDimensional k M]
    (f : ∀ i,M→ₗ[R]V i) (hf : Function.Injective (fun m i=>f i m)) :
    Module.finrank k (M→ₗ[R]A)≤∑ i,b i := by
  induction n generalizing M with
  | zero =>
    have hM : Subsingleton M := ⟨fun x y=>hf (funext (fun i=>Fin.elim0 i))⟩
    letI := hM
    letI : Subsingleton (M→ₗ[R]A) := ⟨fun f g=>by
      ext x
      rw [Subsingleton.elim x 0,map_zero,map_zero]⟩
    simp [Module.finrank_zero_of_subsingleton]
  | succ n ih =>
    let K := LinearMap.ker (f 0)
    letI : FiniteDimensional k K := FiniteDimensional.of_injective
      (K.subtype.restrictScalars k) K.subtype_injective
    let tail : ∀ i:Fin n,K→ₗ[R]V i.succ := fun i=>(f i.succ).comp K.subtype
    have htail : Function.Injective (fun m i=>tail i m) := by
      intro x y h
      apply Subtype.ext
      apply hf
      funext i
      refine Fin.cases ?_ (fun j=>?_) i
      · exact x.property.trans y.property.symm
      · exact congrFun h j
    have hrec := ih (fun i:Fin n=>V i.succ) (fun i=>b i.succ)
      (fun i=>hb i.succ) K tail htail
    have hfirst := hb 0 (LinearMap.range (f 0))
    have hquot := (moduleHomDomainEquiv (k := k) (A := A)
      (f 0).quotKerEquivRange).finrank_eq
    have hsplit := schurHom_finrank_le_submodule_quotient (k := k) (A := A) K
    change Module.finrank k ((M⧸K)→ₗ[R]A)=_ at hquot
    rw [hquot] at hsplit
    rw [Fin.sum_univ_succ]
    exact hsplit.trans ((Nat.add_le_add hrec hfirst).trans_eq (Nat.add_comm _ _))

theorem moduleHom_finrank_le_finite_coordinate_bounds [FiniteDimensional k A]
    {ι : Type u} [Fintype ι]
    (V : ι→Type u) [∀ i,AddCommGroup (V i)] [∀ i,Module R (V i)]
    [∀ i,Module k (V i)] [∀ i,IsScalarTower k R (V i)]
    (b : ι→ℕ)
    (hb : ∀ i (S : Submodule R (V i)),Module.finrank k (S→ₗ[R]A)≤b i)
    (M : Type u) [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M] [FiniteDimensional k M]
    (f : ∀ i,M→ₗ[R]V i) (hf : Function.Injective (fun m i=>f i m)) :
    Module.finrank k (M→ₗ[R]A)≤∑ i,b i := by
  let e := (Fintype.equivFin ι).symm
  have hi : Function.Injective (fun m j=>f (e j) m) := by
    intro x y he
    apply hf
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    exact congrFun he j
  have h := moduleHom_finrank_le_coordinate_bounds (k := k) (R := R) (A := A)
    (Fintype.card ι) (fun j=>V (e j)) (fun j=>b (e j)) (fun j=>hb (e j))
    M (fun j=>f (e j)) hi
  simpa only [e.sum_comp] using h

end SymmetricSubgroupAsymptotics
