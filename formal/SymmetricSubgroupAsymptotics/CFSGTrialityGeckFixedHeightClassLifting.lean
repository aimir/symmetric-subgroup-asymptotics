import SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedCoordinateDecomposition
import SymmetricSubgroupAsymptotics.CFSGFiniteOrderedFamilyLeading

/-! Every fixed class in an actual positive height image has a genuinely
fixed representative in that height tail.  The lift is an ordered product
of the displayed long and short sections; it is not an assumed exactness
property of fixed points. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHeightClassLifting
open CFSGTrialityGeckFixedCoordinateDecomposition CFSGTrialityGeckFixedCoordinateParameters
open CFSGTrialityGeckSectionQuotientCoordinates CFSGTrialityGeckWordCoordinateTwist
open CFSGTrialityGeckWordRootIndex CFSGTrialityGeckWordHeightCoordinates
open CFSGTrialityGeckPositiveTwist CFSGTrialityGeckHeightQuotientTwist
open CFSGTrialityGeckHeightCoordinateAction CFSGNormTwoCoordinateRootHeightFiltration
open CFSGFiniteQuotientFamilyProduct CFSGFiniteOrderedFamilyLeading CFSGTrialityD4NormTwo

local instance liftTailNormal (K : Type) [Field K] (h : ℤ) :
    (TailInPositive K h).Normal :=
  heightTail_normal_in_positive (CartanMatrix.D 4) (CartanMatrix.D_diag 4)
    (CartanMatrix.D_transpose 4) D4_positive_definite (CartanMatrix.D_off_diag_nonpos 4) K h

def heightProjection (K : Type) [Field K] (h : ℤ) :
    TailInPositive K h →* HeightImage K h :=
  ((QuotientGroup.mk' (TailInPositive K (h + 1))).comp
    (TailInPositive K h).subtype).codRestrict (HeightImage K h)
      (fun u => ⟨u.val,u.property,rfl⟩)

def longTailElement (K : Type) [Field K] [Finite K] (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (s : LongAt h) : TailInPositive K h :=
  ⟨longPositiveSection K s.val (c (longHeightIndex s.val s.property)), by
    have hm := longPositiveSection_mem_tail K s.val (c (longHeightIndex s.val s.property))
    have he := congrArg (TailInPositive K) s.property
    exact (congrArg (fun N : Subgroup (Positive K) =>
      longPositiveSection K s.val (c (longHeightIndex s.val s.property)) ∈ N) he).mp hm⟩

def shortTailElement (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (s : ShortAt h) : TailInPositive K h :=
  ⟨shortPositiveSection K σ s.val (c (shortHeightIndex s.val 0 s.property)), by
    have hm := shortPositiveSection_mem_tail K σ s.val (c (shortHeightIndex s.val 0 s.property))
    have he := congrArg (TailInPositive K) s.property
    exact (congrArg (fun N : Subgroup (Positive K) =>
      shortPositiveSection K σ s.val (c (shortHeightIndex s.val 0 s.property)) ∈ N) he).mp hm⟩

def sectionRepresentative (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) : TailInPositive K h :=
  orderedFamilyProduct (longTailElement K h c) * orderedFamilyProduct (shortTailElement K σ h c)

theorem sectionRepresentative_val (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) :
    (sectionRepresentative K σ h c).val =
      orderedFamilyProduct (fun s : LongAt h =>
        longPositiveSection K s.val (c (longHeightIndex s.val s.property))) *
      orderedFamilyProduct (fun s : ShortAt h =>
        shortPositiveSection K σ s.val (c (shortHeightIndex s.val 0 s.property))) := by
  change (TailInPositive K h).subtype
    (orderedFamilyProduct (longTailElement K h c) *
      orderedFamilyProduct (shortTailElement K σ h c)) = _
  rw [map_mul, map_orderedFamilyProduct, map_orderedFamilyProduct]
  rfl

private theorem ordered_fixed {G I : Type*} [Group G] [Fintype I]
    (F : MulAut G) (f : I → G) (hf : ∀ i,F (f i) = f i) :
    F (orderedFamilyProduct f) = orderedFamilyProduct f := by
  change F.toMonoidHom (orderedFamilyProduct f) = _
  rw [map_orderedFamilyProduct]
  exact congrArg orderedFamilyProduct (funext hf)

theorem sectionRepresentative_fixed (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (h : ℤ)
    (c : WordHeightIndex h → Multiplicative K) (hc : coordinateTwist K σ h c = c) :
    positiveTwist K σ (sectionRepresentative K σ h c).val =
      (sectionRepresentative K σ h c).val := by
  rw [sectionRepresentative_val, map_mul]
  rw [ordered_fixed (positiveTwist K σ) _ (fun s : LongAt h =>
    longPositiveSection_fixed K σ s.val _ (fixed_long_parameter K σ h c hc s.val s.property))]
  rw [ordered_fixed (positiveTwist K σ) _ (fun s : ShortAt h =>
    shortPositiveSection_fixed K σ s.val _
      (fixed_short_parameter_thrice K σ h c hc s.val s.property))]

theorem sectionRepresentative_image (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (hh : 0 < h) (c : WordHeightIndex h → Multiplicative K)
    (hc : coordinateTwist K σ h c = c) :
    heightProjection K h (sectionRepresentative K σ h c) = wordHeightLayerEquiv K h hh c := by
  let E := wordHeightLayerEquiv K h hh
  letI : CommGroup (HeightImage K h) :=
    MonoidHom.commGroupOfSurjective E.toMonoidHom E.surjective
  have hlong (s : LongAt h) :
      heightProjection K h (longTailElement K h c s) =
        E (Pi.mulSingle (longHeightIndex s.val s.property)
          (c (longHeightIndex s.val s.property))) := by
    apply Subtype.ext
    exact (longSectionCoordinates_image K s.val hh s.property _).symm
  have hshort (s : ShortAt h) :
      heightProjection K h (shortTailElement K σ h c s) =
        E (shortSectionCoordinates K σ s.val s.property
          (c (shortHeightIndex s.val 0 s.property))) := by
    apply Subtype.ext
    exact (shortSectionCoordinates_image K σ s.val hh s.property _).symm
  calc
    heightProjection K h (sectionRepresentative K σ h c) =
        (∏ s : LongAt h,heightProjection K h (longTailElement K h c s)) *
        (∏ s : ShortAt h,heightProjection K h (shortTailElement K σ h c s)) := by
      simp only [sectionRepresentative, map_mul, orderedFamilyProduct, map_list_prod,
        List.map_map, Function.comp_def, Finset.prod_map_toList]
    _ = E (longCoordinateProduct K h c * shortCoordinateProduct K σ h c) := by
      simp only [hlong,hshort,map_mul,map_prod,longCoordinateProduct,shortCoordinateProduct]
    _ = E c := congrArg E (fixed_coordinate_decomposition K σ h c hc)

theorem exists_fixed_height_representative (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (h : ℤ) (hh : 0 < h) (x : HeightImage K h) (hx : heightImageTwist K σ h x = x) :
    ∃ u : Positive K,u ∈ TailInPositive K h ∧ positiveTwist K σ u = u ∧
      QuotientGroup.mk' (TailInPositive K (h + 1)) u = x.val := by
  let c := (wordHeightLayerEquiv K h hh).symm x
  have he : wordHeightLayerEquiv K h hh c = x :=
    (wordHeightLayerEquiv K h hh).apply_symm_apply x
  have hc : coordinateTwist K σ h c = c :=
    (fixed_iff_coordinates K σ h hh c).mp (by rw [he]; exact hx)
  refine ⟨(sectionRepresentative K σ h c).val,
    (sectionRepresentative K σ h c).property,sectionRepresentative_fixed K σ h c hc,?_⟩
  have hi := congrArg Subtype.val (sectionRepresentative_image K σ h hh c hc)
  change QuotientGroup.mk' (TailInPositive K (h + 1))
    (sectionRepresentative K σ h c).val = (wordHeightLayerEquiv K h hh c).val at hi
  exact hi.trans (congrArg Subtype.val he)

end SymmetricSubgroupAsymptotics.CFSGTrialityGeckFixedHeightClassLifting
