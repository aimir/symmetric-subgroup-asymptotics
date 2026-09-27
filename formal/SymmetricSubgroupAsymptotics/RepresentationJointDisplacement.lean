import SymmetricSubgroupAsymptotics.RepresentationFixedDisplacement
import SymmetricSubgroupAsymptotics.PermutationBinaryOrbitSection

/-! Joint displacement slices for actual subgroups of the original
acting group. Their preimages are actual fixed spaces, and are pulled
back through an original equivariant permutation-section map. The orbit
budget is proved, not supplied. Identifying a character common kernel's
orbit numbers and constructing a separator remain separate tasks. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite
namespace SymmetricSubgroupAsymptotics

variable {k G A : Type} [Field k] [Group G] [AddCommGroup A] [Module k A]
    (ρ : Representation k G A) (K : Subgroup G)

/-- Vanishing on every element of the literal original subgroup. -/
def subgroupZeroFunctions : Submodule k (G → A) where
  carrier := {f | ∀ g : K, f (g:G)=0}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro f f' hf hf' g
    change f (g:G)+f' (g:G)=0
    rw [hf g,hf' g,add_zero]
  smul_mem' := by
    intro c f hf g
    change c • f (g:G)=0
    rw [hf g,smul_zero]

/-- The full connecting slice, restricted by the actual common-kernel
condition. No scalar-line replacement is made. -/
def displacementJointSlice : Submodule k (G → A) :=
  displacementSlice ρ ρ.invariants ⊓ subgroupZeroFunctions (k := k) (A := A) K

/-- Its actual preimage retains both fixed-valued displacement and
pointwise fixedness under the same original subgroup K. -/
def displacementJointPreimage : Submodule k A :=
  displacementPreimage ρ ρ.invariants ⊓ Representation.invariants (ρ.comp K.subtype)

theorem invariants_le_displacementJointPreimage :
    ρ.invariants≤displacementJointPreimage ρ K := by
  intro a ha
  exact ⟨invariants_le_displacementPreimage ρ ρ.invariants ha,fun g => ha (g:G)⟩

def displacementToJointSlice :
    displacementJointPreimage ρ K →ₗ[k] displacementJointSlice ρ K :=
  ((representationDisplacement ρ).comp (displacementJointPreimage ρ K).subtype).codRestrict
    (displacementJointSlice ρ K) (fun a =>
      ⟨⟨⟨(a:A),rfl⟩,a.property.1⟩,fun g => sub_eq_zero.mpr (a.property.2 g)⟩)

theorem displacementToJointSlice_surjective :
    Function.Surjective (displacementToJointSlice ρ K) := by
  intro f
  obtain ⟨a,ha⟩ := f.property.1.1
  have haP : a∈displacementJointPreimage ρ K := by
    constructor
    · change representationDisplacement ρ a∈subspaceValuedFunctions (G := G) ρ.invariants
      rw [ha]
      exact f.property.1.2
    · intro g
      have hg := f.property.2 g
      rw [← ha] at hg
      change ρ (g:G) a-a=0 at hg
      exact sub_eq_zero.mp hg
  exact ⟨⟨a,haP⟩,Subtype.ext ha⟩

theorem displacementToJointSlice_ker :
    (displacementToJointSlice ρ K).ker=
      ρ.invariants.comap (displacementJointPreimage ρ K).subtype := by
  ext a
  rw [LinearMap.mem_ker,Subtype.ext_iff]
  change representationDisplacement ρ (a:A)=0 ↔ (a:A)∈ρ.invariants
  rw [← LinearMap.mem_ker,representationDisplacement_ker]

/-- The joint budget's left side is exactly the dimension of its actual
K-fixed preimage, rather than a bound inferred from tensor labels. -/
theorem displacementJointPreimage_finrank [Finite G] [FiniteDimensional k A] :
    Module.finrank k (displacementJointPreimage ρ K)=
      Module.finrank k ρ.invariants+Module.finrank k (displacementJointSlice ρ K) := by
  have hd := (displacementToJointSlice ρ K).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (displacementToJointSlice_surjective ρ K),
    finrank_top,displacementToJointSlice_ker,
    (Submodule.comapSubtypeEquivOfLe
      (invariants_le_displacementJointPreimage ρ K)).finrank_eq] at hd
  exact hd.symm.trans (Nat.add_comm _ _)

section OriginalPermutationSection

variable {X : Type} [Finite G] [Finite X] [MulAction G X] [FiniteDimensional k A]

/-- The joint subgroup-kernel budget for an ACTUAL equivariant quotient
of a subrepresentation of the original permutation module. Every orbit
and all original correlations of the preimage are retained. -/
theorem permutationSection_displacementJoint_finrank_le_orbit_widths
    (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (t : MulAction.orbitRel.Quotient K X → ℕ)
    (hcard : ∀ o : MulAction.orbitRel.Quotient K X, Nat.card o.orbit=2^(t o)) :
    Module.finrank k ρ.invariants+Module.finrank k (displacementJointSlice ρ K) ≤
      ∑ o, (t o).choose (t o/2) := by
  let W := displacementJointPreimage ρ K
  let P : Submodule k M.toSubmodule := W.comap q.toLinearMap
  have hfixed (g : K) (v : M.toSubmodule) (hv : v∈P) :
      q (M.toRepresentation (g:G) v)=q v :=
    (Representation.IntertwiningMap.isIntertwining _ _ q (g:G) v).trans (hv.2 g)
  let M' : Subrepresentation (permutationFunctionRepresentation k K X) := {
    toSubmodule := P.map M.toSubmodule.subtype
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨v,hv,rfl⟩ := hv
      refine ⟨M.toRepresentation (g:G) v,?_,rfl⟩
      change q (M.toRepresentation (g:G) v)∈W
      rw [hfixed g v hv]
      exact hv }
  let e : P ≃ₗ[k] M'.toSubmodule := M.toSubmodule.equivSubtypeMap P
  let qP : P →ₗ[k] W := (q.toLinearMap.comp P.subtype).codRestrict W
    (fun v => v.property)
  have hqP : Function.Surjective qP := by
    intro w
    obtain ⟨v,hv⟩ := hq (w:A)
    have hvP : v∈P := by
      change q v∈W
      rw [hv]
      exact w.property
    exact ⟨⟨v,hvP⟩,Subtype.ext hv⟩
  let qM : M'.toSubmodule →ₗ[k] W := qP.comp e.symm.toLinearMap
  have hqM : Function.Surjective qM := hqP.comp e.symm.surjective
  have htrivial : ∀ (g : K) (m : M'.toSubmodule),
      qM (M'.toRepresentation g m)=qM m := by
    intro g m
    apply Subtype.ext
    change q (e.symm (M'.toRepresentation g m) : M.toSubmodule)=
      q (e.symm m : M.toSubmodule)
    have he : (e.symm (M'.toRepresentation g m) : M.toSubmodule)=
        M.toRepresentation (g:G) (e.symm m : M.toSubmodule) := by
      apply Subtype.ext
      rfl
    rw [he]
    exact hfixed g (e.symm m : M.toSubmodule) (e.symm m).property
  have hb := twoGroup_permutation_trivial_quotient_finrank_le_orbit_widths
    (hG.to_subgroup K) t hcard M' qM hqM htrivial
  change Module.finrank k (displacementJointPreimage ρ K)≤_ at hb
  rw [displacementJointPreimage_finrank] at hb
  exact hb

/-- Equal actual orbit lengths give the numerical form of the joint
budget. The character-kernel orbit identity must be proved separately. -/
theorem permutationSection_displacementJoint_finrank_le_uniform_orbits
    (hG : IsPGroup 2 G)
    (M : Subrepresentation (permutationFunctionRepresentation k G X))
    (q : M.toRepresentation.IntertwiningMap ρ) (hq : Function.Surjective q)
    (a j : ℕ) (horbits : Nat.card (MulAction.orbitRel.Quotient K X)=2^j)
    (hcard : ∀ o : MulAction.orbitRel.Quotient K X, Nat.card o.orbit=2^a) :
    Module.finrank k ρ.invariants+Module.finrank k (displacementJointSlice ρ K) ≤
      2^j*a.choose (a/2) := by
  have hb := permutationSection_displacementJoint_finrank_le_orbit_widths
    ρ K hG M q hq (fun _ => a) hcard
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Fintype.card_eq_nat_card,horbits] using hb

end OriginalPermutationSection
end SymmetricSubgroupAsymptotics
