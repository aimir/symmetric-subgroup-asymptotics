import SymmetricSubgroupAsymptotics.C1TernaryPrimeBaseOwner
import SymmetricSubgroupAsymptotics.OriginalKernelArbitraryNormalQuotient
import SymmetricSubgroupAsymptotics.PermutationSubrepresentationHead

/-!
# Every original normal quotient of the intrinsic ternary prime-base owner

The faithful coordinates identify the original kernel with its literal
image submodule.  For every original normal N, the arbitrary-normal adapter
constructs G/N -> G/(ker(top) sup N), with its actual kernel action.  Its
denominator is exactly the original axis image inside the coordinate image.

The onto map from the original A4 top and the action factorization are
constructed here.  The regular-module embedding therefore has no supplied
factorization, splitting, diagonal/full, or normal-kernel containment premise.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics
namespace C1TernaryPrimeBaseOwnerWitness

open TernaryA4InvariantSubmodules

variable {G : Type} [Group G] (W : C1TernaryPrimeBaseOwnerWitness G)

/-- The natural A4 action restricted to the actual correlated kernel image. -/
def baseModule : Rep Scalar A4 :=
  Rep.of ((permutationFunctionRepresentation Scalar A4 (Fin 4)).subrepresentation
    W.baseImage (fun g v hv => W.baseImage_invariant g.1 g.2 v hv))

@[simp] theorem baseModule_apply (g : A4) (v : W.baseImage) :
    (W.baseModule.ρ g v).val = coordinateAction g.1 v.val := rfl

/-- The original coordinates with their exact image as codomain. -/
def baseCoordinates : W.top.ker →* Multiplicative W.baseImage where
  toFun k := Multiplicative.ofAdd (W.coordinateVector k)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd W.coordinates.map_one
  map_mul' k l := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (W.coordinates.map_mul k l)

theorem baseCoordinates_injective : Function.Injective W.baseCoordinates := by
  intro k l h
  apply W.coordinates_injective
  apply Multiplicative.toAdd.injective
  exact congrArg (fun v : Multiplicative W.baseImage => v.toAdd.val) h

theorem baseCoordinates_surjective : Function.Surjective W.baseCoordinates := by
  intro v
  obtain ⟨k, hk⟩ := (W.mem_baseImage v.toAdd.val).mp v.toAdd.property
  refine ⟨k, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hk

def baseEquiv : W.top.ker ≃* Multiplicative W.baseImage :=
  MulEquiv.ofBijective W.baseCoordinates
    ⟨W.baseCoordinates_injective, W.baseCoordinates_surjective⟩

@[simp] theorem baseEquiv_apply (k : W.top.ker) :
    (W.baseEquiv k).toAdd = W.coordinateVector k := rfl

theorem coordinateVector_conjugation (g : G) (k : W.top.ker) :
    W.coordinateVector (MulAut.conjNormal g k) =
      W.baseModule.ρ (W.top g) (W.coordinateVector k) := by
  apply Subtype.ext
  exact W.coordinates_conjugation g k

/-- The original extension, without a chosen complement. -/
def baseChart : OriginalKernelModuleChart W.top W.baseModule where
  equiv := W.baseEquiv.symm
  conjugate g v := by
    let k : W.top.ker := W.baseEquiv.symm (Multiplicative.ofAdd v)
    have hk : W.coordinateVector k = v :=
      congrArg Multiplicative.toAdd (W.baseEquiv.apply_symm_apply (Multiplicative.ofAdd v))
    have he : W.baseEquiv (MulAut.conjNormal g k) =
        Multiplicative.ofAdd (W.baseModule.ρ (W.top g) v) := by
      apply Multiplicative.toAdd.injective
      rw [W.baseEquiv_apply, W.coordinateVector_conjugation, hk]
      rfl
    have he' : W.baseEquiv.symm
        (Multiplicative.ofAdd (W.baseModule.ρ (W.top g) v)) = MulAut.conjNormal g k := by
      apply W.baseEquiv.injective
      rw [W.baseEquiv.apply_symm_apply, he]
      rfl
    exact congrArg (fun x : W.top.ker => (x : G)) he'

@[simp] theorem baseChart_kernelCoordinates (k : W.top.ker) :
    (W.baseChart.kernelCoordinates W.top W.baseModule k).toAdd =
      W.coordinateVector k := rfl

variable (N : Subgroup G)

/-- The adapter denominator is the same original axis, written inside
the actual coordinate image. N need not lie in the top kernel. -/
theorem normalSpace_eq_axisImage_comap :
    W.baseChart.normalSpace W.top W.baseModule N =
      (W.axisImage N).comap W.baseImage.subtype := by
  ext v
  obtain ⟨k, hk⟩ := W.baseEquiv.surjective (Multiplicative.ofAdd v)
  have hv : W.coordinateVector k = v := congrArg Multiplicative.toAdd hk
  rw [← hv]
  have hker : (W.baseChart.kernelCoordinates W.top W.baseModule).ker ≤
      N.subgroupOf W.top.ker := by
    intro l hl
    have hl1 : l = 1 := W.baseEquiv.injective
      ((MonoidHom.mem_ker.mp hl).trans W.baseEquiv.map_one.symm)
    exact hl1.symm ▸ (N.subgroupOf W.top.ker).one_mem
  change (W.baseChart.kernelCoordinates W.top W.baseModule k).toAdd ∈
      sectionSubgroupImage (p := 3)
        (W.baseChart.kernelCoordinates W.top W.baseModule) (N.subgroupOf W.top.ker) ↔
    (W.coordinates k).toAdd ∈ W.axisImage N
  rw [sectionSubgroupImage_mem_iff _ _ hker k]
  exact (W.coordinates_mem_axisImage_iff N k).symm

variable [N.Normal]

/-- The actual quotient group from the arbitrary-normal adapter. -/
abbrev quotientTop := G ⧸ (W.top.ker ⊔ N)

/-- The onto top map is factored from the original onto A4 map. -/
def topQuotient : A4 →* W.quotientTop N :=
  W.top.liftOfSurjective W.top_surjective
    ⟨QuotientGroup.mk' (W.top.ker ⊔ N), by
      rw [QuotientGroup.ker_mk']
      exact le_sup_left⟩

@[simp] theorem topQuotient_apply (g : G) :
    W.topQuotient N (W.top g) = QuotientGroup.mk' (W.top.ker ⊔ N) g :=
  MonoidHom.liftOfRightInverse_comp_apply W.top (Function.surjInv W.top_surjective)
    (Function.rightInverse_surjInv W.top_surjective) _ g

theorem topQuotient_surjective : Function.Surjective (W.topQuotient N) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (W.top.ker ⊔ N) q
  exact ⟨W.top g, W.topQuotient_apply N g⟩

/-- The unchanged original extension G/N -> G/(ker(top) sup N). -/
abbrev quotientBase : (G ⧸ N) →* W.quotientTop N :=
  OriginalKernelModuleChart.base W.top N

theorem quotientBase_surjective : Function.Surjective (W.quotientBase N) :=
  OriginalKernelModuleChart.base_surjective W.top N

@[simp] theorem quotientBase_apply (g : G) :
    W.quotientBase N (QuotientGroup.mk' N g) =
      QuotientGroup.mk' (W.top.ker ⊔ N) g := rfl

abbrev quotientModule : Rep Scalar (W.quotientTop N) :=
  W.baseChart.sectionRepresentation W.top W.baseModule N

def quotientChart : OriginalKernelModuleChart (W.quotientBase N) (W.quotientModule N) :=
  W.baseChart.quotientChart W.top W.baseModule N

@[simp] theorem quotientChart_sectionMap (k : W.top.ker) :
    ((W.quotientChart N).equiv (W.baseChart.sectionMap W.top W.baseModule N k) : G ⧸ N) =
      QuotientGroup.mk' N (k : G) :=
  congrArg Subtype.val (W.baseChart.kernelEquiv_apply W.top W.baseModule N k)

/-- Equality of denominators identifies the adapter module with the
literal section expected by the regular-section theorem. -/
def axisSectionEquiv : W.quotientModule N ≃ₗ[Scalar] W.axisSection N :=
  Submodule.quotEquivOfEq _ _ (W.normalSpace_eq_axisImage_comap N)

@[simp] theorem axisSectionEquiv_sectionMap (k : W.top.ker) :
    W.axisSectionEquiv N (W.baseChart.sectionMap W.top W.baseModule N k).toAdd =
      TernaryA4SectionRegularEmbedding.sectionMk W.baseImage (W.axisImage N)
        (W.coordinateVector k) := rfl

/-- The action is transported from the actual arbitrary-normal quotient,
not supplied as a factorization hypothesis. -/
def axisRepresentation : Representation Scalar (W.quotientTop N) (W.axisSection N) :=
  (W.axisSectionEquiv N).conjRingEquiv.toMonoidHom.comp (W.quotientModule N).ρ

theorem axisRepresentation_equiv (q : W.quotientTop N) (v : W.quotientModule N) :
    W.axisRepresentation N q (W.axisSectionEquiv N v) =
      W.axisSectionEquiv N ((W.quotientModule N).ρ q v) := by
  change W.axisSectionEquiv N ((W.quotientModule N).ρ q
    ((W.axisSectionEquiv N).symm (W.axisSectionEquiv N v))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The actual quotient action agrees with every original A4 coordinate
representative, including axes with nontrivial top image. -/
theorem axisRepresentation_factors :
    TernaryA4SectionRegularEmbedding.FactorsSection W.baseImage (W.axisImage N)
      W.baseImage_invariant (W.topQuotient N) (W.axisRepresentation N) := by
  intro t v
  obtain ⟨g, rfl⟩ := W.top_surjective t
  obtain ⟨k, hk⟩ := W.baseEquiv.surjective (Multiplicative.ofAdd v)
  have hv : W.coordinateVector k = v := congrArg Multiplicative.toAdd hk
  rw [← hv]
  rw [W.topQuotient_apply, ← W.axisSectionEquiv_sectionMap N k,
    W.axisRepresentation_equiv]
  have hact := W.baseChart.sectionRepresentation_apply W.top W.baseModule N g k
  change W.axisSectionEquiv N
      ((W.quotientModule N).ρ (QuotientGroup.mk' (W.top.ker ⊔ N) g)
        (W.baseChart.sectionMap W.top W.baseModule N k).toAdd) = _
  rw [hact, W.axisSectionEquiv_sectionMap]
  apply congrArg (TernaryA4SectionRegularEmbedding.sectionMk W.baseImage (W.axisImage N))
  apply Subtype.ext
  exact W.coordinates_conjugation g k

theorem axis_regular_embedding :
    ∃ F : (W.axisRepresentation N).IntertwiningMap
      (Representation.leftRegular Scalar (W.quotientTop N)), Function.Injective F :=
  W.axis_descended_regular_embedding N (W.topQuotient N) (W.topQuotient_surjective N)
    (W.axisRepresentation N) (W.axisRepresentation_factors N)

/-- The module of the original G/N kernel embeds in the regular module
of its actual acting quotient. No action factorization is left as input. -/
theorem quotient_regular_embedding :
    ∃ F : (W.quotientModule N).ρ.IntertwiningMap
      (Representation.leftRegular Scalar (W.quotientTop N)), Function.Injective F := by
  obtain ⟨F, hF⟩ := W.axis_regular_embedding N
  let L : (W.quotientModule N).ρ.IntertwiningMap
      (Representation.leftRegular Scalar (W.quotientTop N)) := {
    toLinearMap := F.toLinearMap.comp (W.axisSectionEquiv N).toLinearMap
    isIntertwining' q := by
      apply LinearMap.ext
      intro v
      change F (W.axisSectionEquiv N ((W.quotientModule N).ρ q v)) =
        Representation.leftRegular Scalar (W.quotientTop N) q (F (W.axisSectionEquiv N v))
      rw [← W.axisRepresentation_equiv, F.isIntertwining] }
  exact ⟨L, hF.comp (W.axisSectionEquiv N).injective⟩

end C1TernaryPrimeBaseOwnerWitness
end SymmetricSubgroupAsymptotics

end
