import SymmetricSubgroupAsymptotics.BinaryCubicScalarGeneratorTransfer

/-! A transitive action on binary planes is cyclic when an actual
acting element supplies the common cubic scalar. Operators outside the
cubic centralizer may be semilinear: only their actual unit-valued
images of supported seeds are used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical MonoidAlgebra BigOperators
namespace SymmetricSubgroupAsymptotics.BinaryCubicTransitiveCyclic
open BinaryQuadraticField (Scalar omega)

variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]
    [MulAction G I] [MulAction.IsPretransitive G I] [Nonempty I]
    (rho : Representation (ZMod 2) G (I → Scalar)) (H : Subgroup G)
    (tau : Representation Scalar H (I → Scalar))
    (hact : ∀ h : H, ∀ v : I → Scalar, tau h v = rho (h : G) v)
    (k : H) (hk : ∀ v : I → Scalar, rho (k : G) v = omega • v)
    (hdelta : ∀ g : G, ∀ i : I, ∃ u : Scalarˣ,
      rho g (Pi.single i 1) = (u : Scalar) • (Pi.single (g • i) 1 : I → Scalar))

include hact k hk hdelta in
/-- An actual supported seed generates the entire binary representation. -/
theorem generatedBy_one : RepresentationGeneratedBy rho 1 := by
  let i₀ : I := Classical.choice inferInstance
  let seed : Fin 1 → rho.asModule := fun _ =>
    rho.asModuleEquiv.symm (Pi.single i₀ 1)
  let P : Submodule (ZMod 2)[G] rho.asModule := Submodule.span _ (Set.range seed)
  let S : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  let restricted : Subrepresentation (rho.comp H.subtype) := {
    toSubmodule := S.toSubmodule
    apply_mem_toSubmodule h _ hv := S.apply_mem_toSubmodule (h : G) hv }
  let Q := BinaryCubicScalarGeneratorTransfer.scalarUpgrade
    (rho.comp H.subtype) tau hact k hk restricted
  have hseed : (Pi.single i₀ 1 : I → Scalar) ∈ S := by
    change seed 0 ∈ P
    exact Submodule.subset_span ⟨0,rfl⟩
  have hpoint (i : I) : (Pi.single i 1 : I → Scalar) ∈ Q.toSubmodule := by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G i₀ i
    obtain ⟨u,hu⟩ := hdelta g i₀
    have himage := S.apply_mem_toSubmodule g hseed
    rw [hu,hg] at himage
    have hQimage : (u : Scalar) • (Pi.single i 1 : I → Scalar) ∈ Q.toSubmodule := himage
    have hinv := Q.toSubmodule.smul_mem (↑(u⁻¹) : Scalar) hQimage
    have hunit : (↑(u⁻¹) : Scalar) * (u : Scalar) = 1 := by
      simpa only [Units.val_mul,Units.val_one] using
        congrArg (fun z : Scalarˣ => (z : Scalar)) (inv_mul_cancel u)
    simpa only [smul_smul,hunit,one_smul] using hinv
  have hall (v : I → Scalar) : v ∈ Q.toSubmodule := by
    have hsum : (∑ i : I, v i • (Pi.single i 1 : I → Scalar)) = v := by
      calc
        (∑ i : I, v i • (Pi.single i 1 : I → Scalar)) =
            ∑ i : I, Pi.single i (v i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [←Pi.single_smul]
          simp only [smul_eq_mul,mul_one]
        _ = v := LinearMap.sum_single_apply (fun _ : I => Scalar) v
    rw [←hsum]
    exact Q.toSubmodule.sum_mem fun i _ => Q.toSubmodule.smul_mem (v i) (hpoint i)
  refine ⟨seed,top_unique ?_⟩
  intro x _
  change rho.asModuleEquiv x ∈ S
  exact hall (rho.asModuleEquiv x)

end SymmetricSubgroupAsymptotics.BinaryCubicTransitiveCyclic
