import SymmetricSubgroupAsymptotics.BinaryCubicKernelMultiplicityUniform

/-! Explicit packed generators for actual cubic kernel classes of bounded
multiplicity. Only actual local actions and their subgroup averages are used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators MonoidAlgebra
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics.BinaryCubicKernelMultiplicityGenerators
open BinaryPlanePermutationAffineEquiv BinaryCubicKernelMultiplicityUniform

variable {O I : Type} [Group O] [Finite O] [Fintype I] [DecidableEq I]
    (rho : Representation (ZMod 2) O (I → Plane)) (L : I → O →* Linear)
    (happly : ∀ g v i, rho g v i = L i g (v i))

omit [Fintype I] [DecidableEq I] in
private theorem average_formula (D : Subgroup O)
    [Invertible (Fintype.card D : ZMod 2)] (v : I → Plane) :
    (Representation.averageMap (rho.comp D.subtype)) v =
      ⅟(Fintype.card D : ZMod 2) • ∑ g : D, rho (g : O) v := by
  simp [Representation.averageMap,GroupAlgebra.average,map_sum,
    LinearMap.smul_apply,Finset.sum_apply]

private theorem projector_mem (hO : IsPGroup 3 O) (i : I)
    (W : Subrepresentation rho) (v : I → Plane) (hv : v ∈ W) :
    kernelProjector rho L hO i v ∈ W := by
  unfold kernelProjector
  rw [average_formula]
  exact W.toSubmodule.smul_mem _ (W.toSubmodule.sum_mem
    (fun g _ => W.apply_mem_toSubmodule (g : O) hv))

private def e0 : Plane := ![1,0]
private def e1 : Plane := ![0,1]

private theorem plane_alternative : ∀ v : Plane, v≠0 → v≠e0 →
    ∃ c : ZMod 2, v=e1+c • e0 := by decide +kernel

private theorem plane_decomposition (v : Plane) : v=v 0 • e0+v 1 • e1 := by
  funext i
  fin_cases i <;> simp [e0,e1]

include happly in
/-- One seed per color generates the actual ambient module. Each coordinate
is recovered by its literal kernel average and a nonidentity local cubic. -/
theorem generatedBy_m (hO : IsPGroup 3 O)
    (hcubic : ∀ i g, L i g ^ 3 = 1)
    (hnonzero : ∀ i, ∃ g, L i g ≠ 1)
    (hcards : ∀ i j, Nat.card (localKernel L i) = Nat.card (localKernel L j))
    (m : ℕ) (hbound : ∀ K : Subgroup O, Nat.card {i : I // localKernel L i = K} ≤ m) :
    RepresentationGeneratedBy rho m := by
  let color : I → Fin m := fibreColor (localKernel L) m hbound
  let seed : Fin m → I → Plane := fun j => packedSeed color j e0
  let code : Fin m → rho.asModule := fun c => rho.asModuleEquiv.symm (seed c)
  let P : Submodule (ZMod 2)[O] rho.asModule :=
    Submodule.span (ZMod 2)[O] (Set.range code)
  let W : Subrepresentation rho := Subrepresentation.ofSubmodule' P
  have hseed (c : Fin m) : seed c ∈ W := by
    change rho.asModuleEquiv.symm (seed c) ∈ P
    exact Submodule.subset_span ⟨c,rfl⟩
  have hsingle0 (i : I) : Pi.single i e0 ∈ W := by
    have hm := projector_mem rho L hO i W (seed (color i)) (hseed (color i))
    have he : kernelProjector rho L hO i (seed (color i)) = Pi.single i e0 :=
      packed_average_single rho L happly hO hcubic hcards m hbound i e0
    rwa [he] at hm
  have hsingle (i : I) (v : Plane) : Pi.single i v∈W := by
    obtain ⟨g,hg⟩ := hnonzero i
    have hact : rho g (Pi.single i e0)=Pi.single i (L i g e0) := by
      funext j
      rw [happly]
      by_cases hj : j=i
      · subst j; rw [Pi.single_eq_same,Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hj,Pi.single_eq_of_ne hj,map_zero]
    have hmem := W.apply_mem_toSubmodule g (hsingle0 i)
    rw [hact] at hmem
    have hn : L i g e0≠0 := by
      intro h
      exact (by decide +kernel : e0≠0)
        ((L i g).injective (h.trans (map_zero (L i g)).symm))
    have he : L i g e0≠e0 := by
      intro h
      exact (by decide +kernel : e0≠0)
        (BinaryPlaneNontrivialCubicFixedFree.fixedFree (L i g) (hcubic i g) hg e0 h)
    obtain ⟨c,hc⟩ := plane_alternative (L i g e0) hn he
    have hsingle1 : Pi.single i e1∈W := by
      have hm := W.toSubmodule.sub_mem hmem (W.toSubmodule.smul_mem c (hsingle0 i))
      have hc' : L i g e0-c • e0=e1 := by rw [hc,add_sub_cancel_right]
      rw [← Pi.single_smul,← Pi.single_sub,hc'] at hm
      exact hm
    have hm := W.toSubmodule.add_mem
      (W.toSubmodule.smul_mem (v 0) (hsingle0 i))
      (W.toSubmodule.smul_mem (v 1) hsingle1)
    rw [← Pi.single_smul,← Pi.single_smul,← Pi.single_add,← plane_decomposition v] at hm
    exact hm
  refine ⟨code,top_unique ?_⟩
  intro v _
  have hm := W.toSubmodule.sum_mem (fun i (_ : i∈Finset.univ) =>
    hsingle i (rho.asModuleEquiv v i))
  rw [LinearMap.sum_single_apply] at hm
  exact hm

include happly in
/-- Odd-order semisimplicity transfers the explicit packed ambient
m-generator bound to every actual invariant subspace. -/
theorem uniform_m (hO : IsPGroup 3 O)
    (hcubic : ∀ i g, L i g ^ 3 = 1)
    (hnonzero : ∀ i, ∃ g, L i g ≠ 1)
    (hcards : ∀ i j, Nat.card (localKernel L i) = Nat.card (localKernel L j))
    (m : ℕ) (hbound : ∀ K : Subgroup O, Nat.card {i : I // localKernel L i = K} ≤ m) :
    UniformSubrepresentationGeneratorBound rho m := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : NeZero (Nat.card O : ZMod 2) := ⟨by
    obtain ⟨n,hn⟩ := hO.exists_card_eq
    rw [hn,Nat.cast_pow,show ((3 : ℕ) : ZMod 2) = 1 by decide +kernel,one_pow]
    exact one_ne_zero⟩
  exact RepresentationGeneratedBy.uniform_of_invertible_order rho
    (generatedBy_m rho L happly hO hcubic hnonzero hcards m hbound)

/-- Restricting an actual larger group action to its displayed cubic
subgroup is enough; no extension of scalar actions is introduced. -/
theorem uniform_of_restrict {G : Type} [Group G]
    (rhoG : Representation (ZMod 2) G (I → Plane)) (alpha : O →* G)
    (hact : ∀ g v i, rhoG (alpha g) v i = L i g (v i))
    (hO : IsPGroup 3 O) (hcubic : ∀ i g, L i g ^ 3 = 1)
    (hnonzero : ∀ i, ∃ g, L i g ≠ 1)
    (hcards : ∀ i j, Nat.card (localKernel L i) = Nat.card (localKernel L j))
    (m : ℕ) (hbound : ∀ K : Subgroup O, Nat.card {i : I // localKernel L i = K} ≤ m) :
    UniformSubrepresentationGeneratorBound rhoG m := by
  exact UniformSubrepresentationGeneratorBound.of_comp rhoG alpha
    (uniform_m (rhoG.comp alpha) L hact hO hcubic hnonzero hcards m hbound)

end SymmetricSubgroupAsymptotics.BinaryCubicKernelMultiplicityGenerators
