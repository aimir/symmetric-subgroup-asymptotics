import SymmetricSubgroupAsymptotics.BinaryPlaneWreathIrreducible
import SymmetricSubgroupAsymptotics.PermutationalWreathLinearRepresentation
import SymmetricSubgroupAsymptotics.FunctionBlockOrbitUniform

/-! Two generators for every invariant translation subspace of an actual
cyclic-block binary-plane wreath subgroup. Local holonomy is unrestricted. -/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathUniform
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible

variable {R I : Type} [Group R] [MulAction R I] [Fintype I] [DecidableEq I]

def localRepresentation : Representation (ZMod 2) Linear Plane where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

abbrev representation (C : Subgroup (W (R := R) (I := I))) :=
  (PermutationalWreathProduct.functionRepresentation
    (Q := R) (I := I) localRepresentation).comp C.subtype

/-- An actual cyclic block lift bounds all invariant subspaces by the
local dimension two, even for correlated local images. -/
theorem uniform (C : Subgroup (W (R := R) (I := I)))
    (g : C) (i₀ : I)
    (hcycle : ∀ i : I, ∃ n : ℕ, (g : W (R := R) (I := I)).right ^ n • i₀ = i) :
    UniformSubrepresentationGeneratorBound (representation C) 2 := by
  let b : C →* Equiv.Perm I :=
    (MulAction.toPermHom R I).comp
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp
        C.subtype)
  apply FunctionBlockOrbitUniform.uniform_of_apply (representation C) g i₀
    (Pi.basisFun (ZMod 2) (Fin 2)) b
    (fun h i ↦ (h : W (R := R) (I := I)).left i) ?_ ?_
  · intro h v i
    rfl
  · intro i
    obtain ⟨n,hn⟩ := hcycle i
    refine ⟨n,?_⟩
    have hbpow : (b g)^n =
        MulAction.toPermHom R I ((g : W (R := R) (I := I)).right ^ n) :=
      ((MulAction.toPermHom R I).map_pow _ n).symm
    rw [hbpow]
    exact hn

/-- Surjectivity supplies the actual lift; a pure block complement is not
assumed. -/
theorem uniform_of_surjective (C : Subgroup (W (R := R) (I := I)))
    (hsurj : Function.Surjective
      ((PermutationalWreathProduct.rightHom : W (R := R) (I := I) →* R).comp
        C.subtype))
    (c : R) (i₀ : I) (hcycle : ∀ i : I, ∃ n : ℕ, c^n • i₀ = i) :
    UniformSubrepresentationGeneratorBound (representation C) 2 := by
  obtain ⟨g,hg⟩ := hsurj c
  apply uniform C g i₀
  intro i
  obtain ⟨n,hn⟩ := hcycle i
  refine ⟨n,?_⟩
  change (g : W (R := R) (I := I)).right = c at hg
  rw [hg]
  exact hn

end SymmetricSubgroupAsymptotics.BinaryPlaneCyclicWreathUniform
