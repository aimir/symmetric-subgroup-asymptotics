import SymmetricSubgroupAsymptotics.BinaryPlaneDihedralKleinRestrictionUniform
import SymmetricSubgroupAsymptotics.BinaryPlaneDihedralLinearNonbinarySocles
import SymmetricSubgroupAsymptotics.OriginalKernelRetainedNonbinaryInterval
import SymmetricSubgroupAsymptotics.OriginalKernelSectionSocleRows
import SymmetricSubgroupAsymptotics.SocleNormalSubgroupGeneratorInheritance
import SymmetricSubgroupAsymptotics.BinaryPlaneDihedralRetainedComparator
import SymmetricSubgroupAsymptotics.BinaryPlaneCyclicActualKernelBounds

/-! Whole-socle capacity two on the retained NONBINARY interval of an
actual affine D8 frame. Every original N remains literal; binary axes
containing the retained odd preimage are left to the faithful8 comparator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.BinaryPlaneDihedralRetainedQuotientSocles
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel OriginalKernelModuleChart
open DihedralEightRegularKleinBlockModel (R Q regular regular_smul)
local instance : Fintype R := BinaryRegularKleinWreath.rFintype
local instance : DecidableEq R := BinaryRegularKleinWreath.rDecidableEq

variable {G : Type} [Group G] [Finite G]
  (C : Subgroup (W (R := Q) (I := R)))
  (pi : G →* C) (hpi : Function.Surjective pi)
  (A : Rep.{0} (ZMod 2) C) [FiniteDimensional (ZMod 2) A]
  (E : OriginalKernelModuleChart pi A)
  (j : Representation.IntertwiningMap A.ρ (BinaryPlaneCyclicWreathUniform.representation C))
  (hj : Function.Injective j)
  (hblocks : Function.Surjective
    ((PermutationalWreathProduct.rightHom : W (R := Q) (I := R) →* Q).comp C.subtype))
  (hG : ¬ IsPGroup 2 G)

include pi hpi A E j hj hblocks hG in
theorem quotientSocle (N : Subgroup G) [N.Normal]
    (hnot : ¬ (oddKernel C).comap pi≤N) : SocleNormalGeneratorBound (G ⧸ N) 2 := by
  let O := oddKernel C
  letI : IsMulCommutative O := commutative C
  letI : NeZero (Nat.card O : ZMod 2) := ⟨card_cast_ne_zero C⟩
  have hC : ¬ IsPGroup 2 C := BinaryPlaneCyclicActualKernelBounds.linear_nonbinary
    (C := C) (pi := pi) (A := A) (E := E) hG
  have hR : IsPGroup 2 Q := DihedralEightRegularKleinBlockModel.binary
  have htrans : ∀ i k : R, ∃ h : C, (h : W (R := Q) (I := R)).right • i=k := by
    intro i k
    obtain ⟨h,hh⟩ := hblocks (regular (k*i⁻¹))
    refine ⟨h,?_⟩
    change (h : W (R := Q) (I := R)).right • i=k
    change (h : W (R := Q) (I := R)).right=regular (k*i⁻¹) at hh
    rw [hh,regular_smul]
    group
  have hu : UniformSubrepresentationGeneratorBound A.ρ 2 :=
    (BinaryPlaneDihedralKleinRestrictionUniform.uniform C hC hblocks).of_injective j hj
  have hfixed : ∀ a : A, (∀ o : O, A.ρ (o : C) a=a) → a=0 := by
    intro a ha
    apply hj
    have hz := fixedFree_of_nonbinary C hR hC htrans (j a) (fun o => by
      rw [← Representation.IntertwiningMap.isIntertwining _ _ j (o : C) a,ha o])
    simpa only [map_zero] using hz
  have hnonbinary := E.retained_linear_nonbinary pi A N hpi O (cube_eq_one C) hfixed hnot
  have hsurj : Function.Surjective (sectionTop pi N hpi) := by
    intro y
    obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (pi.ker ⊔ N) y
    exact ⟨pi g,(sectionTop_apply pi N hpi g).trans hg⟩
  have hlinear : SocleNormalGeneratorBound (G ⧸ (pi.ker ⊔ N)) 2 :=
    BinaryPlaneDihedralLinearNonbinarySocles.socle_of_surjective C hblocks
      (sectionTop pi N hpi) hsurj hnonbinary
  let D := retainedOddSeparator pi N O
  let F := trivialActionSoclePart (G ⧸ N) D
  let f := base pi N
  have hf : Function.Surjective f := base_surjective pi N
  letI : (F.map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hFImage : F.map f≤finiteGroupSocle (G ⧸ (pi.ker ⊔ N)) :=
    (Subgroup.map_mono (minimalNormalSoclePart_le_finiteGroupSocle _ _)).trans
      (SocleActionPartQuotientKernel.socle_map_le f hf)
  have hFImageBound : MarkedC4.normalGen (F.map f)≤2 :=
    (MarkedC4.normalGen_le_socle_of_normal_le (F.map f) hFImage).trans
      ((socleNormalGeneratorBound_iff_normalGen_le _ _).mp hlinear)
  have hF : MarkedC4.normalGen F≤2 :=
    (E.fixedSocleRow_normalGen_le_image pi A N hpi O hfixed).trans hFImageBound
  have hM : MarkedC4.normalGen (nontrivialActionSoclePart (G ⧸ N) D)≤2 :=
    E.movingSocleRow_normalGen_le_two pi A N hpi O hu
  apply (socleNormalGeneratorBound_iff_normalGen_le _ _).mpr
  exact (normalGen_finiteGroupSocle_le_max_actionSocleParts (G ⧸ N) D).trans (max_le hM hF)

end SymmetricSubgroupAsymptotics.BinaryPlaneDihedralRetainedQuotientSocles
