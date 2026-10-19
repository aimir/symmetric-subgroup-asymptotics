import SymmetricSubgroupAsymptotics.RepresentationPolynomialGeneratorBound
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Basis.Defs

/-! A cyclic orbit of blocks bounds every invariant subspace by the
dimension of one block. The chosen acting element may carry arbitrary
invertible local maps. Its actual powers, rather than an ambient block
permutation group, supply the required transports. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical Polynomial BigOperators

namespace SymmetricSubgroupAsymptotics.FunctionBlockOrbitUniform

variable {k H I V : Type} [Field k] [Group H] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module k V]
  (rho : Representation k H (I → V)) (g : H) (i₀ : I)
  {d : ℕ} (basis : Module.Basis (Fin d) k V)
  (hblock : ∀ i : I, ∃ (m : ℕ) (L : V ≃ₗ[k] V),
    ∀ v : V, rho (g^m) (Pi.single i₀ v) = Pi.single i (L v))

include hblock in
theorem polynomial_span :
    Submodule.span k[X]
      (Set.range (fun j : Fin d => Module.AEval'.of (rho g)
        (Pi.single i₀ (basis j)))) = ⊤ := by
  let e := Module.AEval'.of (rho g)
  let code : Fin d → Module.AEval' (rho g) :=
    fun j => e (Pi.single i₀ (basis j))
  let P : Submodule k[X] (Module.AEval' (rho g)) :=
    Submodule.span k[X] (Set.range code)
  have hseed (v : V) : e (Pi.single i₀ v) ∈ P := by
    let seed : V →ₗ[k] (I → V) := LinearMap.single k (fun _ : I => V) i₀
    have hs : (∑ j : Fin d, basis.repr v j • e (seed (basis j))) = e (seed v) := by
      simpa only [map_sum,map_smul] using
        congrArg (fun w : V => e (seed w)) (basis.sum_repr v)
    have hm : (∑ j : Fin d, basis.repr v j • e (seed (basis j))) ∈ P := by
      apply P.sum_mem
      intro j _
      apply P.smul_of_tower_mem
      exact Submodule.subset_span ⟨j,rfl⟩
    exact hs ▸ hm
  have hsingle (i : I) (v : V) : e (Pi.single i v) ∈ P := by
    obtain ⟨m,L,hL⟩ := hblock i
    have hp := P.smul_mem ((Polynomial.X : k[X])^m) (hseed (L.symm v))
    have heq : ((Polynomial.X : k[X])^m) • e (Pi.single i₀ (L.symm v)) =
        e (rho (g^m) (Pi.single i₀ (L.symm v))) := by
      dsimp only [e]
      rw [Module.AEval'.X_pow_smul_of,map_pow]
      rfl
    rw [heq,hL,LinearEquiv.apply_symm_apply] at hp
    exact hp
  have hall (v : I → V) : e v ∈ P := by
    have hm : (∑ i : I, e (Pi.single i (v i))) ∈ P :=
      P.sum_mem fun i _ => hsingle i (v i)
    have hs : (∑ i : I, e (Pi.single i (v i))) = e v := by
      simpa only [map_sum] using
        congrArg e (LinearMap.sum_single_apply (fun _ : I => V) v)
    exact hs ▸ hm
  apply top_unique
  intro v _
  simpa only [LinearEquiv.apply_symm_apply] using hall (e.symm v)

include g i₀ basis hblock in
theorem generatedBy : RepresentationGeneratedBy rho d :=
  representationGeneratedBy_of_polynomial rho g _
    (polynomial_span rho g i₀ basis hblock)

include g i₀ basis hblock in
theorem uniform : UniformSubrepresentationGeneratorBound rho d :=
  uniformSubrepresentationGeneratorBound_of_polynomial rho g _
    (polynomial_span rho g i₀ basis hblock)

omit [Fintype I] in
theorem single_of_apply (b : H →* Equiv.Perm I)
    (L : H → I → V ≃ₗ[k] V)
    (happly : ∀ (h : H) (v : I → V) (i : I),
      rho h v i = L h i (v (b h⁻¹ i)))
    (h : H) (i : I) (v : V) :
    rho h (Pi.single i v) = Pi.single (b h i) (L h (b h i) v) := by
  funext j
  rw [happly]
  by_cases hj : j = b h i
  · subst j
    have he : b h⁻¹ (b h i) = i := by
      rw [map_inv]
      exact (b h).symm_apply_apply i
    rw [he,Pi.single_eq_same,Pi.single_eq_same]
  · have hn : b h⁻¹ j ≠ i := by
      intro hi
      apply hj
      rw [map_inv] at hi
      exact ((b h).eq_symm_apply.mp hi.symm).symm
    simp only [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hn,map_zero]

omit [Fintype I] in
theorem orbit_transports (b : H →* Equiv.Perm I)
    (L : H → I → V ≃ₗ[k] V)
    (happly : ∀ (h : H) (v : I → V) (i : I),
      rho h v i = L h i (v (b h⁻¹ i)))
    (hcover : ∀ i : I, ∃ m : ℕ, ((b g)^m) i₀ = i) :
    ∀ i : I, ∃ (m : ℕ) (T : V ≃ₗ[k] V),
      ∀ v : V, rho (g^m) (Pi.single i₀ v) = Pi.single i (T v) := by
  intro i
  obtain ⟨m,hm⟩ := hcover i
  refine ⟨m,L (g^m) i,?_⟩
  intro v
  rw [single_of_apply rho b L happly,map_pow,hm]

include basis in
theorem generatedBy_of_apply (b : H →* Equiv.Perm I)
    (L : H → I → V ≃ₗ[k] V)
    (happly : ∀ (h : H) (v : I → V) (i : I),
      rho h v i = L h i (v (b h⁻¹ i)))
    (hcover : ∀ i : I, ∃ m : ℕ, ((b g)^m) i₀ = i) :
    RepresentationGeneratedBy rho d :=
  generatedBy rho g i₀ basis (orbit_transports rho g i₀ b L happly hcover)

include basis in
theorem uniform_of_apply (b : H →* Equiv.Perm I)
    (L : H → I → V ≃ₗ[k] V)
    (happly : ∀ (h : H) (v : I → V) (i : I),
      rho h v i = L h i (v (b h⁻¹ i)))
    (hcover : ∀ i : I, ∃ m : ℕ, ((b g)^m) i₀ = i) :
    UniformSubrepresentationGeneratorBound rho d :=
  uniform rho g i₀ basis (orbit_transports rho g i₀ b L happly hcover)

end SymmetricSubgroupAsymptotics.FunctionBlockOrbitUniform

end
