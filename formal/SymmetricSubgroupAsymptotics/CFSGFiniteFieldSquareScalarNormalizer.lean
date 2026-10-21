import SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
import SymmetricSubgroupAsymptotics.CFSGFiniteFieldSquareSpan
import Mathlib.Tactic.Group

/-! Actual additive permutations normalizing the square scalar subgroup
already normalize all scalar multiplications over a finite field. This
includes odd characteristic: additive spanning by squares reconstructs
the whole field, without assuming that every nonzero scalar is a square. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
variable (K : Type*) [Field K]

def squareScalarHom : Kˣ→*AddAut K := (scalarHom K).comp (powMonoidHom 2)

def squareScalarSubgroup : Subgroup (AddAut K) := (squareScalarHom K).range

@[simp] theorem squareScalarHom_apply (u : Kˣ) (x : K) :
    squareScalarHom K u x=(u : K)^2*x := rfl

variable {K}

def scalarLinearitySubgroup (A : AddAut K) : AddSubgroup K where
  carrier := {a | ∀ x : K,A (a*x)*A 1=A a*A x}
  zero_mem' := by intro x;simp only [zero_mul,map_zero]
  add_mem' := by
    intro a b ha hb x
    simp only [add_mul,map_add]
    rw [ha x,hb x]
  neg_mem' := by
    intro a ha x
    simpa only [neg_mul,map_neg] using congrArg (fun y : K => -y) (ha x)

theorem square_mem_scalarLinearity (A : AddAut K)
    (hA : A∈Subgroup.normalizer (squareScalarSubgroup K : Set (AddAut K))) (a : K) :
    a^2∈scalarLinearitySubgroup A := by
  by_cases ha : a=0
  · subst a
    simpa only [zero_pow (by decide : 2≠0)] using (scalarLinearitySubgroup A).zero_mem
  · let u : Kˣ := Units.mk0 a ha
    have hu : squareScalarHom K u∈squareScalarSubgroup K := ⟨u,rfl⟩
    have hc := (Subgroup.mem_normalizer_iff.mp hA (squareScalarHom K u)).mp hu
    obtain ⟨v,hv⟩ := hc
    have hact : ∀ x : K,A (a^2*x)=(v : K)^2*A x := by
      intro x
      have he := congrArg (fun f : AddAut K => f (A x)) hv
      change (v : K)^2*A x=A (a^2*A.symm (A x)) at he
      rw [A.symm_apply_apply] at he
      exact he.symm
    intro x
    calc
      A (a^2*x)*A 1=((v : K)^2*A x)*A 1 := by rw [hact]
      _=((v : K)^2*A 1)*A x := by ring
      _=A (a^2)*A x := by rw [←hact 1,mul_one]

variable [Finite K]

theorem scalar_relation_of_square_normalizer (A : AddAut K)
    (hA : A∈Subgroup.normalizer (squareScalarSubgroup K : Set (AddAut K))) (a x : K) :
    A (a*x)*A 1=A a*A x := by
  have ht : scalarLinearitySubgroup A=⊤ :=
    CFSGFiniteFieldSquareSpan.eq_top_of_scaled_squares _ 1 one_ne_zero (by
      intro t
      simpa only [one_mul] using square_mem_scalarLinearity A hA t)
  have ha : a∈scalarLinearitySubgroup A := by rw [ht];trivial
  exact ha x

theorem conjugate_scalar_mem_of_square_normalizer (A : AddAut K)
    (hA : A∈Subgroup.normalizer (squareScalarSubgroup K : Set (AddAut K))) (u : Kˣ) :
    A*scalarHom K u*A⁻¹∈scalarSubgroup K := by
  have ha : A (u : K)≠0 := by
    intro he
    apply Units.ne_zero u
    exact A.injective (he.trans (map_zero A).symm)
  let v : Kˣ := Units.mk0 (A (u : K)/A 1) (div_ne_zero ha (additive_one_ne_zero A))
  refine ⟨v,?_⟩
  apply AddEquiv.ext
  intro x
  change (A (u : K)/A 1)*x=A ((u : K)*A.symm x)
  have he := scalar_relation_of_square_normalizer A hA (u : K) (A.symm x)
  rw [A.apply_symm_apply] at he
  calc
    (A (u : K)/A 1)*x=(A (u : K)*x)/A 1 := by ring
    _=A ((u : K)*A.symm x) := ((eq_div_iff (additive_one_ne_zero A)).mpr he).symm

theorem mem_scalar_normalizer_of_square (A : AddAut K)
    (hA : A∈Subgroup.normalizer (squareScalarSubgroup K : Set (AddAut K))) :
    A∈Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)) := by
  have hforward : ∀ (B : AddAut K),
      B∈Subgroup.normalizer (squareScalarSubgroup K : Set (AddAut K))→
      ∀ C : AddAut K,C∈scalarSubgroup K→B*C*B⁻¹∈scalarSubgroup K := by
    rintro B hB C ⟨u,rfl⟩
    exact conjugate_scalar_mem_of_square_normalizer B hB u
  apply Subgroup.mem_normalizer_iff.mpr
  intro C
  constructor
  · exact hforward A hA C
  · intro hC
    have he := hforward A⁻¹ ((Subgroup.normalizer _).inv_mem hA) _ hC
    have hc : A⁻¹*(A*C*A⁻¹)*(A⁻¹)⁻¹=C := by group
    rwa [hc] at he

theorem square_scalar_normalizer_le_scalar_normalizer :
    Subgroup.normalizer (squareScalarSubgroup K : Set (AddAut K))≤
      Subgroup.normalizer (scalarSubgroup K : Set (AddAut K)) :=
  fun A hA => mem_scalar_normalizer_of_square A hA

end SymmetricSubgroupAsymptotics.CFSGFiniteFieldScalarNormalizer
