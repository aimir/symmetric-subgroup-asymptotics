import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Reconstruction of a field automorphism from an actual additive
permutation normalizing all literal nonzero scalar multiplications. The
normalizing permutation is uniquely a scalar times a ring automorphism.
The proof works over every field and assumes no simple-group recognition. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
variable (K : Type*) [Field K]

/-- Literal multiplication on the underlying additive group. -/
def scalarHom : Kˣ→*AddAut K where
  toFun u :=
    { u.mulLeft with
      map_add' := fun x y => mul_add (u : K) x y }
  map_one' := by ext x;exact one_mul x
  map_mul' u v := by ext x;exact mul_assoc (u : K) (v : K) x

@[simp] theorem scalarHom_apply (u : Kˣ) (x : K) : scalarHom K u x=(u : K)*x := rfl

/-- The subgroup being normalized consists of these actual scalar maps. -/
def scalarSubgroup : Subgroup (AddAut K) := (scalarHom K).range

theorem scalarHom_injective : Function.Injective (scalarHom K) := by
  intro u v h
  apply Units.ext
  have he := congrArg (fun f : AddAut K => f 1) h
  simpa only [scalarHom_apply,mul_one] using he

variable {K}

theorem scalar_relation (A : AddAut K)
    (hA : A∈Subgroup.normalizer (scalarSubgroup K : Set (AddAut K))) (a x : K) :
    A (a*x)*A 1=A a*A x := by
  by_cases ha : a=0
  · subst a
    simp only [zero_mul,map_zero]
  · let u : Kˣ := Units.mk0 a ha
    have hu : scalarHom K u∈scalarSubgroup K := ⟨u,rfl⟩
    have hc := (Subgroup.mem_normalizer_iff.mp hA (scalarHom K u)).mp hu
    obtain ⟨v,hv⟩ := hc
    have hact : ∀ y : K,A (a*y)=(v : K)*A y := by
      intro y
      have he := congrArg (fun f : AddAut K => f (A y)) hv
      change (v : K)*A y=A (a*A.symm (A y)) at he
      rw [A.symm_apply_apply] at he
      exact he.symm
    calc
      A (a*x)*A 1=((v : K)*A x)*A 1 := by rw [hact]
      _=((v : K)*A 1)*A x := by ring
      _=A a*A x := by rw [←hact 1,mul_one]

theorem additive_one_ne_zero (A : AddAut K) : A 1≠0 := by
  intro he
  have hh : A 1=A 0 := he.trans (map_zero A).symm
  exact one_ne_zero (A.injective hh)

/-- The reconstructed automorphism is the normalized original map,
without choosing an abstract field of the same cardinality. -/
def normalizedRingAut (A : AddAut K) (hA : A∈Subgroup.normalizer (scalarSubgroup K : Set (AddAut K))) : K ≃+* K :=
  { Equiv.ofBijective (fun x : K => A x/A 1) (by
      constructor
      · intro x y hxy
        apply A.injective
        have he := congrArg (fun z : K => z*A 1) hxy
        simpa only [div_mul_cancel₀ _ (additive_one_ne_zero A)] using he
      · intro y
        refine ⟨A.symm (y*A 1),?_⟩
        change A (A.symm (y*A 1))/A 1=y
        rw [A.apply_symm_apply,mul_div_cancel_right₀ y (additive_one_ne_zero A)]) with
    map_mul' := by
      intro x y
      have he := scalar_relation A hA x y
      change A (x*y)/A 1=(A x/A 1)*(A y/A 1)
      apply (div_eq_iff (additive_one_ne_zero A)).mpr
      calc
        A (x*y)=(A x*A y)/A 1 := (eq_div_iff (additive_one_ne_zero A)).mpr he
        _=(A x/A 1)*(A y/A 1)*A 1 := by
          field_simp [additive_one_ne_zero A]
    map_add' := by
      intro x y
      change A (x+y)/A 1=A x/A 1+A y/A 1
      rw [map_add,add_div] }

@[simp] theorem normalizedRingAut_apply (A : AddAut K)
    (hA : A∈Subgroup.normalizer (scalarSubgroup K : Set (AddAut K))) (x : K) :
    normalizedRingAut A hA x=A x/A 1 := rfl

theorem scalar_times_normalizedRingAut (A : AddAut K)
    (hA : A∈Subgroup.normalizer (scalarSubgroup K : Set (AddAut K))) (x : K) :
    A x=A 1*normalizedRingAut A hA x := by
  rw [normalizedRingAut_apply,mul_comm,div_mul_cancel₀ _ (additive_one_ne_zero A)]

theorem exists_unique_scalar_ringAut (A : AddAut K)
    (hA : A∈Subgroup.normalizer (scalarSubgroup K : Set (AddAut K))) :
    ∃! p : Kˣ×(K ≃+* K),∀ x : K,A x=(p.1 : K)*p.2 x := by
  let u : Kˣ := Units.mk0 (A 1) (additive_one_ne_zero A)
  refine ⟨(u,normalizedRingAut A hA),?_,?_⟩
  · exact scalar_times_normalizedRingAut A hA
  · intro p hp
    have hu : p.1=u := by
      apply Units.ext
      have he := hp 1
      simpa only [map_one,mul_one,u,Units.val_mk0] using he.symm
    apply Prod.ext hu
    ext x
    have he := hp x
    rw [hu] at he
    have hn := scalar_times_normalizedRingAut A hA x
    exact mul_left_cancel₀ (Units.ne_zero u) (he.symm.trans hn)

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
