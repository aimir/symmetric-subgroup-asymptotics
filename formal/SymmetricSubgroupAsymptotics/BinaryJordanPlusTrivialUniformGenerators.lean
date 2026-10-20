import SymmetricSubgroupAsymptotics.BinaryFourAugmentationActions
import SymmetricSubgroupAsymptotics.LinearSemidirectCoprimeSocleBounds
import SymmetricSubgroupAsymptotics.RepresentationScalarBasisGenerators
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! Uniform two-generation of the actual three-dimensional trivial-type
part of the S3 envelope: a length-two binary Jordan block plus one scalar.
Proper submodules use scalar dimension; the whole module has two explicit
reflection-orbit generators. -/

set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.BinaryJordanPlusTrivialUniformGenerators

open BinaryFourBlockAugmentation
abbrev Binary := Multiplicative (ZMod 2)
abbrev Space := Fin 3 → Scalar

def reflection : Space ≃ₗ[Scalar] Space where
  toFun x := ![x 1, x 0, x 2]
  invFun x := ![x 1, x 0, x 2]
  left_inv := by intro x; ext i; fin_cases i <;> rfl
  right_inv := by intro x; ext i; fin_cases i <;> rfl
  map_add' := by intro x y; ext i; fin_cases i <;> rfl
  map_smul' := by intro a x; ext i; fin_cases i <;> rfl

theorem reflection_square : reflection ^ 2 = 1 := by
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> rfl

def linear : Binary →* (Space ≃ₗ[Scalar] Space) := powersHom 2 reflection reflection_square

def rho : Representation Scalar Binary Space :=
  LinearSemidirectCoprimeSocleBounds.linearRepresentation linear

def generator : Fin 2 → Space := ![![1, 0, 0], ![0, 0, 1]]

theorem generated : RepresentationGeneratedBy rho 2 := by
  let v : Fin 2 → rho.asModule := fun i => rho.asModuleEquiv.symm (generator i)
  let P : Submodule Scalar[Binary] rho.asModule := Submodule.span _ (Set.range v)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hv (i : Fin 2) : generator i ∈ S := by
    change v i ∈ P
    exact Submodule.subset_span ⟨i, rfl⟩
  have hswap : reflection (generator 0) ∈ S := by
    have h := S.apply_mem_toSubmodule (Multiplicative.ofAdd 1) (hv 0)
    exact h
  have hdecomp (x : Space) : x =
      x 0 • generator 0 + x 1 • reflection (generator 0) + x 2 • generator 1 := by
    ext i
    fin_cases i <;> simp [generator, reflection]
  refine ⟨v, top_unique ?_⟩
  intro x _
  change rho.asModuleEquiv x ∈ S
  let y : Space := rho.asModuleEquiv x
  have hm : y 0 • generator 0 + y 1 • reflection (generator 0) + y 2 • generator 1 ∈ S :=
    S.toSubmodule.add_mem
      (S.toSubmodule.add_mem (S.toSubmodule.smul_mem _ (hv 0))
        (S.toSubmodule.smul_mem _ hswap)) (S.toSubmodule.smul_mem _ (hv 1))
  change y ∈ S
  rw [hdecomp y]
  exact hm

theorem uniform : UniformSubrepresentationGeneratorBound rho 2 := by
  intro E
  by_cases htop : E = ⊤
  · let inclusion : E.toRepresentation.IntertwiningMap rho := {
      toLinearMap := E.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
    have hsurj : Function.Surjective inclusion := by
      intro x
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [htop]
      trivial
    let e := inclusion.ofBijective ⟨E.toSubmodule.subtype_injective, hsurj⟩
    exact representationGeneratedBy_of_surjective rho E.toRepresentation
      e.symm.toIntertwiningMap e.symm.surjective generated
  · have hproper : E.toSubmodule ≠ ⊤ := by
      intro h
      exact htop (Subrepresentation.toSubmodule_injective h)
    have hlt := Submodule.finrank_lt hproper
    have hdim : _root_.Module.finrank Scalar Space = 3 := by
      rw [_root_.Module.finrank_pi]
      simp
    have hsmall : _root_.Module.finrank Scalar E.toSubmodule ≤ 2 := by
      rw [hdim] at hlt
      omega
    exact representationGeneratedBy_of_scalar_finrank_le E.toRepresentation hsmall

end SymmetricSubgroupAsymptotics.BinaryJordanPlusTrivialUniformGenerators

end
