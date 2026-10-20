import SymmetricSubgroupAsymptotics.ProductBlockFrameKernelCoordinates
import SymmetricSubgroupAsymptotics.PermutationPolynomialOrbitGenerators

/-! An actual cyclic lift through four quartet blocks gives a uniform
four-generator bound on the original binary point-permutation module.
The local permutations and their holonomy are unrestricted. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.QuartetBlockCyclicNaturalUniform

variable {X : Type} [Fintype X] [DecidableEq X]
  {T : Subgroup (Equiv.Perm X)} (C : ProductBlockFrame T (Fin 4) (Fin 4))

 theorem uniform (g : T)
    (hcycle : ∀ i : Fin 4,∃ m : ℕ,((C.top g)^m) (0 : Fin 4)=i) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) T X) 4 := by
  apply permutationFunctionRepresentation_uniform_of_polynomial_orbitCover
    g (fun j : Fin 4 => C.frame (0,j))
  intro x
  let p := C.frame.symm x
  obtain ⟨m,hm⟩ := hcycle p.1
  let y := ((g^m)⁻¹ : T) • x
  let b := (C.frame.symm y).2
  have hy : (C.frame.symm y).1=0 := by
    have h := C.intertwine ((g^m)⁻¹) p
    rw [C.frame.apply_symm_apply,map_inv,map_pow,←hm] at h
    simpa only [p,y,Equiv.Perm.inv_def,Equiv.symm_apply_apply] using h
  have hb : C.frame (0,b)=y := by
    apply C.frame.symm.injective
    rw [C.frame.symm_apply_apply]
    exact Prod.ext hy.symm rfl
  refine ⟨b,m,?_⟩
  rw [hb]
  exact smul_inv_smul (g^m) x

end SymmetricSubgroupAsymptotics.QuartetBlockCyclicNaturalUniform
