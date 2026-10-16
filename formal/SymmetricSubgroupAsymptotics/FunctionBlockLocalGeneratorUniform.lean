import SymmetricSubgroupAsymptotics.RepresentationGeneratorRestrictionMaschke
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.Defs

/-! A single local cyclic vector generates a transitive family of vector
blocks when actual group elements supply its local basis and invertible
block transports. Restriction to a finite group of invertible order makes
the same one-generator bound uniform for every invariant subspace. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators

namespace SymmetricSubgroupAsymptotics.FunctionBlockLocalGeneratorUniform

variable {k H I V : Type} [Field k] [Group H] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module k V]
  (rho : Representation k H (I → V)) (i₀ : I) (v₀ : V)
  {d : ℕ} (basis : Module.Basis (Fin d) k V)

theorem generatedBy
    (hseed : ∀ j : Fin d, ∃ h : H,
      rho h (Pi.single i₀ v₀) = Pi.single i₀ (basis j))
    (hblock : ∀ i : I, ∃ (h : H) (L : V ≃ₗ[k] V),
      ∀ v : V, rho h (Pi.single i₀ v) = Pi.single i (L v)) :
    RepresentationGeneratedBy rho 1 := by
  let code : Fin 1 → rho.asModule :=
    fun _ => rho.asModuleEquiv.symm (Pi.single i₀ v₀)
  let P : Submodule k[H] rho.asModule := Submodule.span k[H] (Set.range code)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hstart : (Pi.single i₀ v₀ : I → V) ∈ S := by
    change code 0 ∈ P
    exact Submodule.subset_span (Set.mem_range_self 0)
  have hbasis (j : Fin d) : (Pi.single i₀ (basis j) : I → V) ∈ S := by
    obtain ⟨h,hh⟩ := hseed j
    rw [← hh]
    exact S.apply_mem_toSubmodule h hstart
  have hlocal (v : V) : (Pi.single i₀ v : I → V) ∈ S := by
    let seed : V →ₗ[k] (I → V) := LinearMap.single k (fun _ : I => V) i₀
    have he : (∑ j : Fin d, basis.repr v j • seed (basis j)) = seed v := by
      simpa only [map_sum,map_smul] using congrArg seed (basis.sum_repr v)
    have hm : (∑ j : Fin d, basis.repr v j • seed (basis j)) ∈ S :=
      S.toSubmodule.sum_mem fun j _ => S.toSubmodule.smul_mem _ (hbasis j)
    change seed v ∈ S
    exact he ▸ hm
  have hsingle (i : I) (v : V) : (Pi.single i v : I → V) ∈ S := by
    obtain ⟨h,L,hL⟩ := hblock i
    have hm := S.apply_mem_toSubmodule h (hlocal (L.symm v))
    rwa [hL,LinearEquiv.apply_symm_apply] at hm
  have hall (v : I → V) : v ∈ S := by
    have hm : (∑ i : I, Pi.single i (v i)) ∈ S :=
      S.toSubmodule.sum_mem fun i _ => hsingle i (v i)
    exact LinearMap.sum_single_apply (fun _ : I => V) v ▸ hm
  refine ⟨code,top_unique ?_⟩
  intro v _
  exact hall v

theorem uniform_of_restriction
    {L : Type} [Group L] [Finite L] [NeZero (Nat.card L : k)]
    (f : L →* H)
    (hseed : ∀ j : Fin d, ∃ h : L,
      rho (f h) (Pi.single i₀ v₀) = Pi.single i₀ (basis j))
    (hblock : ∀ i : I, ∃ (h : L) (T : V ≃ₗ[k] V),
      ∀ v : V, rho (f h) (Pi.single i₀ v) = Pi.single i (T v)) :
    UniformSubrepresentationGeneratorBound rho 1 := by
  apply UniformSubrepresentationGeneratorBound.of_comp rho f
  apply RepresentationGeneratedBy.uniform_of_invertible_order
  exact generatedBy (rho.comp f) i₀ v₀ basis hseed hblock

end SymmetricSubgroupAsymptotics.FunctionBlockLocalGeneratorUniform

end
