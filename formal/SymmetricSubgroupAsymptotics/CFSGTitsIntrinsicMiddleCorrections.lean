import SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicOuterBlocks

/-! The WHOLE S*T^-1, S^2 and T^2 corrections belong to the SAME R.
The unsquared S/T blocks are proved positive/strict but are NOT claimed
in the derived group or R. In particular these square corrections are
not asserted to be squares of elements of R, or Frattini elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleCorrections
open CFSGTitsIntrinsicFirstLayer CFSGTitsIntrinsicMiddleRadical
open CFSGReeFFourInnerBracketOriginalBlocks CFSGReeFFourInnerBracketFixedBlocks
open CFSGReeFFourMiddlePositiveKernelIntersection CFSGReeFFourMiddleGradedKernel
open CFSGReeFFourMiddlePositiveIntersectionNormalizer CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFieldParameters CFSGReeFFourFixedModelEquivalence
open CFSGNormTwoCoordinateFunctionalRootLeading CFSGNormTwoCoordinateRootStarInjection
open CFSGNormTwoCoordinateSelectedRootElement CFSGNormTwoCoordinatePositiveRootGenerators
open CFSGNormTwoRootPairing CFSGNormTwoGeckLatticeDegree CFSGNormTwoGeckHeightSupport
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckPositiveTwist
open CFSGE6GeckMiddleRootSupport CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGGradedMatrixSubgroups CFSGGradedMatrixHighLayerProducts
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "f" => outsideHeight.toAddMonoidHom
private abbrev W := functionalWeight A hd hs hp ho f
private abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K
private abbrev rootUnit (K : Type) [Field K] (k : Roots A) : (Mat K)ˣ :=
  selectedRootElement A hd hs hp ho K k 1

private theorem W_eq : W=middleWeight := by
  funext j
  cases j <;> rfl

private theorem root_strict_positive (K : Type) [Field K] (k : Roots A)
    (hk : 0<f k.val) : rootUnit K k∈strictUnits W := by
  have hcut : BelowCut W (f k.val) ((rootUnit K k : Mat K)-1) :=
    (selected_functional_cut_and_leading A hd hs hp ho K f k hk 1).1
  intro i j hij
  have hh := hcut i j (by omega)
  change (rootUnit K k : Mat K) i j-(1 : Mat K) i j=0 at hh
  exact sub_eq_zero.mp hh

private theorem block_roots (K : Type) [Field K] [CharP K 2] (b : Fin 2) :
    middleBlock K b=rootUnit K (middleRoot b 0)*rootUnit K (middleRoot b 1)*
      rootUnit K (middleRoot b 2)*rootUnit K (middleRoot b 3) := by
  rw [middleBlock_eq]
  rfl

private theorem four_members {G : Type*} [Group G] (P : Subgroup G)
    (a b c d : G) (ha : a∈P) (hb : b∈P) (hc : c∈P) (hlast : d∈P) : a*b*c*d∈P :=
  P.mul_mem (P.mul_mem (P.mul_mem ha hb) hc) hlast

private theorem block_positive (K : Type) [Field K] [CharP K 2] (b : Fin 2) :
    middleBlock K b∈Positive K := by
  have hpos (i : Fin 4) : rootUnit K (middleRoot b i)∈Positive K :=
    selected_positive_root_mem A hd hs hp ho K _ (root_properties.2 b i).2 1
  exact Eq.mpr (congrArg (fun u : (Mat K)ˣ=>u∈Positive K) (block_roots K b))
    (four_members (Positive K) _ _ _ _ (hpos 0) (hpos 1) (hpos 2) (hpos 3))

private theorem block_strict (K : Type) [Field K] [CharP K 2] (b : Fin 2) :
    middleBlock K b∈strictUnits middleWeight := by
  have hheight : ∀i : Fin 4,0<f (middleRoot b i).val := by
    intro i
    fin_cases b <;> fin_cases i <;> decide
  have hm : middleBlock K b∈strictUnits W :=
    Eq.mpr (congrArg (fun u : (Mat K)ˣ=>u∈strictUnits W) (block_roots K b))
      (four_members (strictUnits W) _ _ _ _ (root_strict_positive K _ (hheight 0))
        (root_strict_positive K _ (hheight 1)) (root_strict_positive K _ (hheight 2))
        (root_strict_positive K _ (hheight 3)))
  exact Eq.mp (congrArg (fun w : GeckIndex→ℤ=>middleBlock K b∈strictUnits w) W_eq) hm

private theorem raw_middle_positive (m : ℕ) (b : Fin 2) :
    fixedRawHom m (actualMiddleBlock m b)∈Positive (Field m) :=
  Eq.mpr (congrArg (fun u : (Mat (Field m))ˣ=>u∈Positive (Field m))
    (raw_actualMiddleBlock m b)) (block_positive (Field m) b)

private theorem raw_middle_strict (m : ℕ) (b : Fin 2) :
    fixedRawHom m (actualMiddleBlock m b)∈strictUnits middleWeight :=
  Eq.mpr (congrArg (fun u : (Mat (Field m))ˣ=>u∈strictUnits middleWeight)
    (raw_actualMiddleBlock m b)) (block_strict (Field m) b)

private theorem middle_positive (m : ℕ) (b : Fin 2) :
    actualMiddleBlock m b∈fixedPositive m := raw_middle_positive m b

private theorem middle_opposed_positive (m : ℕ) (b : Fin 2) :
    CFSGReeFFourRelativePositiveSubgroups.middleFixedWeyl m*actualMiddleBlock m b*
      (CFSGReeFFourRelativePositiveSubgroups.middleFixedWeyl m)⁻¹∈fixedPositive m :=
  (positive_strict_iff_opposite_positive m (actualMiddleBlock m b)
    (middle_positive m b)).mp (raw_middle_strict m b)

private theorem opposed_membership {G : Type*} [Group G]
    (P : Subgroup G) (w x : G) (hx : x∈P) (hc : w*x*w⁻¹∈P) :
    x∈P⊓P.comap (MulAut.conj w).toMonoidHom := ⟨hx,hc⟩

private theorem middle_intersection (m : ℕ) (b : Fin 2) :
    actualMiddleBlock m b∈middlePositiveIntersection m :=
  opposed_membership (fixedPositive m)
    (CFSGReeFFourRelativePositiveSubgroups.middleFixedWeyl m) (actualMiddleBlock m b)
    (middle_positive m b) (middle_opposed_positive m b)

def middleDifference (m : ℕ) : originalModelFixed m :=
  actualMiddleBlock m 1*(actualMiddleBlock m 0)⁻¹

theorem middleDifference_derived (m : ℕ) :
    middleDifference m∈commutator (originalModelFixed m) := by
  rw [←Abelianization.ker_of (originalModelFixed m)]
  change Abelianization.of (actualMiddleBlock m 1*(actualMiddleBlock m 0)⁻¹)=1
  rw [map_mul,map_inv,middle_image,middle_image,mul_inv_cancel]

theorem middleDifference_intersection (m : ℕ) :
    middleDifference m∈middlePositiveIntersection m :=
  (middlePositiveIntersection m).mul_mem (middle_intersection m 1)
    ((middlePositiveIntersection m).inv_mem (middle_intersection m 0))

def differenceSource : sourceIntersection :=
  ⟨⟨middleDifference 0,middleDifference_derived 0⟩,middleDifference_intersection 0⟩

def squareSource (b : Fin 2) : sourceIntersection :=
  ⟨⟨(actualMiddleBlock 0 b)^2,middle_square_mem_derived 0 b⟩,
    (middlePositiveIntersection 0).pow_mem (middle_intersection 0 b) 2⟩

def differencePoint : middleRadical := sourceEquiv differenceSource

def squarePoint (b : Fin 2) : middleRadical := sourceEquiv (squareSource b)

end SymmetricSubgroupAsymptotics.CFSGTitsIntrinsicMiddleCorrections
