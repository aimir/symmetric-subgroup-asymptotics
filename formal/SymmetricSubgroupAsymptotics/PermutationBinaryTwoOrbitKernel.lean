import SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitSplit

/-! The exact lower denominator in the two-block residual.

A four-dimensional trivial quotient of an original binary permutation
submodule on two four-point orbits has kernel equal to the original
space of block-constant functions. The proof uses the actual restriction
images and their one-dimensional coinvariant kernels. It does not assume
that a correlated module splits, that a group extension splits, or that
the lower kernel equals a larger original normal subgroup.
-/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitKernel

open RepresentationHeadExact
open PermutationBinaryTwoOrbitFiltration

section OneDimensionalKernel
variable {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)

/-- The original coinvariant kernel, with its unchanged restricted action. -/
def coinvariantsSubrepresentation : Subrepresentation ρ where
  toSubmodule := Representation.Coinvariants.ker ρ
  apply_mem_toSubmodule g v hv := by
    apply (Representation.Coinvariants.mk_eq_zero ρ).mp
    rw [Representation.Coinvariants.mk_self_apply,
      (Representation.Coinvariants.mk_eq_zero ρ).mpr hv]

/-- A one-dimensional original coinvariant kernel is fixed under the
original binary group. No quotient or image group replaces that action. -/
theorem coinvariantsKer_le_invariants_of_finrank_one (hG : IsPGroup 2 G)
    (hdim : Module.finrank (ZMod 2) (Representation.Coinvariants.ker ρ)=1) :
    Representation.Coinvariants.ker ρ≤ρ.invariants := by
  let S := coinvariantsSubrepresentation ρ
  letI : Nontrivial S.toSubmodule :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by
      change 0<Module.finrank (ZMod 2) (Representation.Coinvariants.ker ρ)
      omega)
  obtain ⟨v,hv,hfixed⟩ := pGroup_representation_nonzero_fixed hG S.toRepresentation
  have hne : S.toRepresentation.invariants≠⊥ := by
    intro he
    have hm : v∈S.toRepresentation.invariants := hfixed
    rw [he] at hm
    exact hv (by simpa only [Submodule.mem_bot] using hm)
  have hlo := Submodule.one_le_finrank_iff.mpr hne
  have hhi := Submodule.finrank_le S.toRepresentation.invariants
  have ht : S.toRepresentation.invariants=⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank (ZMod 2) S.toRepresentation.invariants=
      Module.finrank (ZMod 2) (Representation.Coinvariants.ker ρ)
    change Module.finrank (ZMod 2) S.toRepresentation.invariants≤
      Module.finrank (ZMod 2) (Representation.Coinvariants.ker ρ) at hhi
    omega
  intro v hv g
  have hm : (⟨v,hv⟩ : S.toSubmodule)∈S.toRepresentation.invariants := by
    rw [ht]
    exact Submodule.mem_top
  exact congrArg Subtype.val (hm g)

end OneDimensionalKernel

section TwoOrbits
variable {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (hG : IsPGroup 2 G)
    (o₁ o₂ : MulAction.orbitRel.Quotient G X)
    (hcover : ∀ o : MulAction.orbitRel.Quotient G X,o=o₁ ∨ o=o₂)
    (hcard₁ : Nat.card o₁.orbit=4) (hcard₂ : Nat.card o₂.orbit=4)

include hG o₁ o₂ hcover hcard₁ hcard₂ in
private theorem head_le_four :
    Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))≤4 := by
  let x₁ : o₁.orbit := ⟨o₁.nonempty_orbit.choose,o₁.nonempty_orbit.choose_spec⟩
  let x₂ : o₂.orbit := ⟨o₂.nonempty_orbit.choose,o₂.nonempty_orbit.choose_spec⟩
  have hb₁ := twoGroup_permutationSubrepresentationHead_le_width hG 2
    (by simpa using hcard₁) x₁ (firstKernelImage M o₁ o₂)
  have hb₂ := twoGroup_permutationSubrepresentationHead_le_width hG 2
    (by simpa using hcard₂) x₂ (secondImage M o₂)
  have hs := head_finrank_le_two_coordinates
    (permutationSubrepresentationOrbitRestriction M o₁)
    (permutationSubrepresentationOrbitRestriction M o₂) (jointInjective M o₁ o₂ hcover)
  change Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))≤
    Module.finrank (ZMod 2) ((firstKernelImage M o₁ o₂).toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2)))+
    Module.finrank (ZMod 2) ((secondImage M o₂).toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2))) at hs
  norm_num at hb₁ hb₂
  omega

include hG o₁ o₂ hcover hcard₁ hcard₂ in
private theorem second_coinvariants_fixed
    (hhead : 4≤Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    Representation.Coinvariants.ker (secondImage M o₂).toRepresentation≤
      (secondImage M o₂).toRepresentation.invariants := by
  let x₁ : o₁.orbit := ⟨o₁.nonempty_orbit.choose,o₁.nonempty_orbit.choose_spec⟩
  let x₂ : o₂.orbit := ⟨o₂.nonempty_orbit.choose,o₂.nonempty_orbit.choose_spec⟩
  have hb₁ := twoGroup_permutationSubrepresentationHead_le_width hG 2
    (by simpa using hcard₁) x₁ (firstKernelImage M o₁ o₂)
  have hb₂ := twoGroup_permutationSubrepresentationHead_le_width hG 2
    (by simpa using hcard₂) x₂ (secondImage M o₂)
  have hs := head_finrank_le_two_coordinates
    (permutationSubrepresentationOrbitRestriction M o₁)
    (permutationSubrepresentationOrbitRestriction M o₂) (jointInjective M o₁ o₂ hcover)
  change Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))≤
    Module.finrank (ZMod 2) ((firstKernelImage M o₁ o₂).toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2)))+
    Module.finrank (ZMod 2) ((secondImage M o₂).toRepresentation.IntertwiningMap
      (Representation.trivial (ZMod 2) G (ZMod 2))) at hs
  norm_num at hb₁ hb₂
  have hh₂ : Module.finrank (ZMod 2)
      ((secondImage M o₂).toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) G (ZMod 2)))=2 := by omega
  have hd₂ := PermutationBinaryFourAugmentation.dimension_eq_three_of_head_ge_two
    (secondImage M o₂) x₂ hcard₂ hh₂.ge
  have hr := (Representation.Coinvariants.ker
    (secondImage M o₂).toRepresentation).finrank_quotient_add_finrank
  rw [representationHead_finrank_eq_coinvariants] at hh₂
  apply coinvariantsKer_le_invariants_of_finrank_one _ hG
  change Module.finrank (ZMod 2) (secondImage M o₂).toRepresentation.Coinvariants+
    Module.finrank (ZMod 2) (Representation.Coinvariants.ker
      (secondImage M o₂).toRepresentation)=
    Module.finrank (ZMod 2) (secondImage M o₂).toSubmodule at hr
  omega

include hG o₁ o₂ hcover hcard₁ hcard₂ in
/-- Every original displacement in the extremal source is fixed. Both
actual coordinate images are used; no invariant functional is extended. -/
theorem coinvariantsKer_le_invariants
    (hhead : 4≤Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))) :
    Representation.Coinvariants.ker M.toRepresentation≤M.toRepresentation.invariants := by
  have hfix₂ := second_coinvariants_fixed M hG o₁ o₂ hcover hcard₁ hcard₂ hhead
  have hfix₁ := second_coinvariants_fixed M hG o₂ o₁
    (fun o => (hcover o).symm) hcard₂ hcard₁ hhead
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,m⟩,rfl⟩ h
  apply jointInjective M o₁ o₂ hcover
  apply Prod.ext
  · let f := rangeProjection (permutationSubrepresentationOrbitRestriction M o₁)
    have hm : f (M.toRepresentation g m-m)∈
        Representation.Coinvariants.ker (secondImage M o₁).toRepresentation := by
      rw [map_sub,Representation.IntertwiningMap.isIntertwining _ _ f]
      exact Representation.Coinvariants.sub_mem_ker g (f m)
    have he := congrArg Subtype.val (hfix₁ hm h)
    have hi := congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining _ _ f h (M.toRepresentation g m-m))
    exact hi.trans he
  · let f := rangeProjection (permutationSubrepresentationOrbitRestriction M o₂)
    have hm : f (M.toRepresentation g m-m)∈
        Representation.Coinvariants.ker (secondImage M o₂).toRepresentation := by
      rw [map_sub,Representation.IntertwiningMap.isIntertwining _ _ f]
      exact Representation.Coinvariants.sub_mem_ker g (f m)
    have he := congrArg Subtype.val (hfix₂ hm h)
    have hi := congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining _ _ f h (M.toRepresentation g m-m))
    exact hi.trans he

/-- Restriction of a fixed original function to one actual orbit. -/
def fixedRestriction (o : MulAction.orbitRel.Quotient G X) :
    (permutationFunctionRepresentation (ZMod 2) G X).invariants →ₗ[ZMod 2]
      (permutationFunctionRepresentation (ZMod 2) G o.orbit).invariants where
  toFun f := ⟨fun x => f.val x.val,fun g => by
    funext x
    exact congrFun (f.property g) x.val⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include o₁ o₂ hcover in
private theorem ambient_invariants_le_two :
    Module.finrank (ZMod 2) (permutationFunctionRepresentation (ZMod 2) G X).invariants≤2 := by
  let f := (fixedRestriction o₁).prod (fixedRestriction o₂)
  have hi : Function.Injective f := by
    intro v w he
    apply Subtype.ext
    funext x
    let o : MulAction.orbitRel.Quotient G X := Quotient.mk'' x
    let x' : o.orbit := ⟨x,MulAction.orbitRel.Quotient.mem_orbit.mpr rfl⟩
    rcases hcover o with ho | ho
    · have h := congrArg Prod.fst he
      have hx : x∈o₁.orbit := ho ▸ x'.property
      exact congrFun (congrArg Subtype.val h) ⟨x,hx⟩
    · have h := congrArg Prod.snd he
      have hx : x∈o₂.orbit := ho ▸ x'.property
      exact congrFun (congrArg Subtype.val h) ⟨x,hx⟩
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  have hd₁ := PermutationBinaryFourSection.invariants_finrank
    (k := ZMod 2) (G := G) (X := o₁.orbit)
    ⟨o₁.nonempty_orbit.choose,o₁.nonempty_orbit.choose_spec⟩
  have hd₂ := PermutationBinaryFourSection.invariants_finrank
    (k := ZMod 2) (G := G) (X := o₂.orbit)
    ⟨o₂.nonempty_orbit.choose,o₂.nonempty_orbit.choose_spec⟩
  rw [Module.finrank_prod,hd₁,hd₂] at hd
  exact hd

include hG o₁ o₂ hcover hcard₁ hcard₂ in
/-- The literal ambient image of the original quotient kernel is exactly
the original fixed-function space, hence the constants on the two actual
orbits. The quotient kernel remains distinct from any larger group normal. -/
theorem quotient_kernel_eq_block_constants
    {A : Type} [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]
    (q : M.toSubmodule →ₗ[ZMod 2] A) (hq : Function.Surjective q)
    (htrivial : ∀ (g : G) (m : M.toSubmodule),q (M.toRepresentation g m)=q m)
    (hA : Module.finrank (ZMod 2) A=4) :
    q.ker.map M.toSubmodule.subtype=
        (permutationFunctionRepresentation (ZMod 2) G X).invariants ∧
      Module.finrank (ZMod 2) q.ker=2 := by
  let q' : M.toRepresentation.Coinvariants →ₗ[ZMod 2] A :=
    Representation.Coinvariants.lift M.toRepresentation q (by
      intro g
      apply LinearMap.ext
      exact htrivial g)
  have hq' : Function.Surjective q' := by
    intro a
    obtain ⟨m,rfl⟩ := hq a
    exact ⟨Representation.Coinvariants.mk M.toRepresentation m,rfl⟩
  have hlo := LinearMap.finrank_le_finrank_of_surjective hq'
  rw [← representationHead_finrank_eq_coinvariants,hA] at hlo
  have hhi := head_le_four M hG o₁ o₂ hcover hcard₁ hcard₂
  have hh : Module.finrank (ZMod 2)
      (M.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2)))=4 :=
    Nat.le_antisymm hhi hlo
  have hdM := (filtration_eq_augmentation M hG o₁ o₂ hcover hcard₁ hcard₂ hlo).2.2
  have hqdim := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hq,finrank_top,hA,hdM] at hqdim
  have hdker : Module.finrank (ZMod 2) q.ker=2 := by omega
  have hc := (Representation.Coinvariants.ker M.toRepresentation).finrank_quotient_add_finrank
  rw [representationHead_finrank_eq_coinvariants] at hh
  change Module.finrank (ZMod 2) M.toRepresentation.Coinvariants+
    Module.finrank (ZMod 2) (Representation.Coinvariants.ker M.toRepresentation)=
      Module.finrank (ZMod 2) M.toSubmodule at hc
  have hcle : Representation.Coinvariants.ker M.toRepresentation≤q.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,m⟩,rfl⟩
    change q (M.toRepresentation g m-m)=0
    rw [map_sub,htrivial,sub_self]
  have hceq : Representation.Coinvariants.ker M.toRepresentation=q.ker :=
    Submodule.eq_of_le_of_finrank_le hcle (by omega)
  have hfixed := coinvariantsKer_le_invariants M hG o₁ o₂ hcover hcard₁ hcard₂ hlo
  have hle : q.ker.map M.toSubmodule.subtype≤
      (permutationFunctionRepresentation (ZMod 2) G X).invariants := by
    rintro _ ⟨m,hm,rfl⟩ g
    rw [← hceq] at hm
    exact congrArg Subtype.val (hfixed hm g)
  refine ⟨Submodule.eq_of_le_of_finrank_le hle ?_,hdker⟩
  rw [Submodule.finrank_map_subtype_eq,hdker]
  exact ambient_invariants_le_two o₁ o₂ hcover

end TwoOrbits
end SymmetricSubgroupAsymptotics.PermutationBinaryTwoOrbitKernel

namespace SymmetricSubgroupAsymptotics

variable {G X A : Type} [Group G] [Finite G] [Finite X]
    [MulAction G X] [MulAction.IsPretransitive G X]
    [AddCommGroup A] [Module (ZMod 2) A] [FiniteDimensional (ZMod 2) A]

/-- The actual common-character section identifies its original lower
kernel. This says nothing about a larger normal subgroup whose image may
also lie in the common-character kernel. -/
theorem permutationBinary_twoBlockCharacter_original_kernel_eq
    (hG : IsPGroup 2 G) (x : X) (hX : Nat.card X=8)
    (ρ : Representation (ZMod 2) G A)
    (M : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (hA : Module.finrank (ZMod 2) A=4)
    (data : RepresentationBinaryCommonCharacter.TwoBlockCharacter ρ) :
    q.toLinearMap.ker.map M.toSubmodule.subtype=
        (permutationFunctionRepresentation (ZMod 2) ρ.ker X).invariants ∧
      Module.finrank (ZMod 2) q.toLinearMap.ker=2 := by
  obtain ⟨hclasses,hcard⟩ := permutationBinary_twoBlockCharacter_orbits hG x hX ρ M q hq hA data
  let MH := PermutationBinaryTwoOrbitSplit.restrictedModule ρ.ker M
  have ht : ∀ (g : ρ.ker) (m : MH.toSubmodule),q (MH.toRepresentation g m)=q m := by
    intro g m
    change q (M.toRepresentation (g:G) m)=q m
    rw [Representation.IntertwiningMap.isIntertwining _ _ q]
    have hg : ρ (g:G)=1 := g.property
    rw [hg]
    rfl
  obtain ⟨o₁,o₂,_,hcover,_,_,_⟩ :=
    PermutationBinaryTwoOrbitFiltration.exists_filtration_eq_augmentation
      MH (hG.to_subgroup ρ.ker) hclasses hcard q.toLinearMap hq ht hA.ge
  exact PermutationBinaryTwoOrbitKernel.quotient_kernel_eq_block_constants
    MH (hG.to_subgroup ρ.ker) o₁ o₂ hcover (hcard o₁) (hcard o₂)
    q.toLinearMap hq ht hA

end SymmetricSubgroupAsymptotics
