import SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness

/-! Transport a checked polynomial recurrence through an actual point
bijection. The target operator is checked on coordinate vectors, while
the recurrence and inverse coefficients are shared by all realizations. -/

set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness

variable {k : Type} [Field k] {d r h : ℕ}
  {T : Module.End k (Fin d → k)} (C : LiteralPolynomialSpanWitness T r h)

def reindexCoordinates (e : Equiv.Perm (Fin d))
    (T' : Module.End k (Fin d → k))
    (he : ∀ v, T' (fun x ↦ v (e.symm x)) = fun x ↦ T v (e.symm x)) :
    LiteralPolynomialSpanWitness T' r h where
  vectors j m x := C.vectors j m (e.symm x)
  step j m := by
    rw [he]
    funext x
    exact congrFun (C.step j m) (e.symm x)
  selected := C.selected
  coefficient i j := C.coefficient (e.symm i) j
  point_eq i x := by
    change (∑ j, C.coefficient (e.symm i) j *
      C.vectors (C.selected j).1 (C.selected j).2 (e.symm x)) =
        (Pi.single i 1 : Fin d → k) x
    rw [C.point_eq]
    have heq : e.symm x = e.symm i ↔ x = i := e.symm.injective.eq_iff
    simp only [Pi.single_apply, heq]

include C in
/-- One coordinate-basis check transports the actual cyclic/module
certificate, retaining the target acting group and its algebra element. -/
theorem uniform_of_reindexed_basis {G : Type} [Group G]
    (rho : Representation k G (Fin d → k)) (a : k[G])
    (T' : Module.End k (Fin d → k)) (hT : T' = rho.asAlgebraHom a)
    (e : Equiv.Perm (Fin d))
    (he : ∀ i x : Fin d,
      T' (fun y ↦ (Pi.single i 1 : Fin d → k) (e.symm y)) x =
        T (Pi.single i 1) (e.symm x)) :
    UniformSubrepresentationGeneratorBound rho r := by
  let L : (Fin d → k) →ₗ[k] (Fin d → k) :=
    { toFun := fun v x ↦ v (e.symm x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hL : T'.comp L = L.comp T := by
    apply (Pi.basisFun k (Fin d)).ext
    intro i
    rw [Pi.basisFun_apply]
    exact funext (he i)
  exact (C.reindexCoordinates e T' (fun v ↦ LinearMap.congr_fun hL v)).uniform rho a hT

end SymmetricSubgroupAsymptotics.LiteralPolynomialSpanWitness

end
