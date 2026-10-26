import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterStarDiagramMate
import SymmetricSubgroupAsymptotics.CFSGReeFFourOuterWedgeMiddleWord

/-! The WHOLE original outer involution has the exact same y/r
conjugate, joining the node-0, diagram-mate node-5 and node-1 wedge
identities. This is a genuine word-generation reduction, with every
higher term retained. No intrinsic head dimension is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourWholeOuterMiddleRelation
open CFSGReeFFourOuterStarDiagramMate CFSGReeFFourOuterStarOriginalMiddle
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGReeFFourOuterWedgeRootActions
open CFSGReeFFourOuterWedgeRootData CFSGReeFFourFieldParameters
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOuterThreeWord CFSGReeFFourMiddleDerivedFiveWord
open CFSGReeFFourOuterFixedRoot CFSGFFourOriginalMiddleWords
open CFSGFFourE6FixedGeneratedGroup CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckDiagramCovariance CFSGExceptionalNormTwoBases
open CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
open CFSGNormTwoCoordinateSelectedRootElement CFSGSerreQuadraticMatrix
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K

private theorem wedge_zero_root : (wedgeRoot 0).val=(E6Index 1 : Roots A) := by
  apply Subtype.ext
  funext j
  change wedgeRow 0 j=(Pi.single (1 : Fin 6) (1 : ℤ) : Fin 6→ℤ) j
  fin_cases j <;> rfl

private theorem parameter_one (m : ℕ) :
    parameter (Field m) 0 1=canonicalRoot rawData (Field m) false 1 1 :=
  (congrArg (fun k : Roots A=>selectedRootElement A hd hs hp ho (Field m) k 1)
    wedge_zero_root).trans (simple_one (Field m) 1).symm

private theorem node_one_relation (m : ℕ) :
    fixedRawHom m (fourCycle m)*canonicalRoot rawData (Field m) false 1 1*
      (fixedRawHom m (fourCycle m))⁻¹=
    fixedRawHom m (fiveWord m)*canonicalRoot rawData (Field m) false 1 1*
      (fixedRawHom m (fiveWord m))⁻¹ := by
  rw [raw_fourCycle_eq,raw_fiveWord_eq]
  have hparam := parameter_one m
  calc
    _=CFSGReeFFourOuterStarMiddleWord.rawY (Field m)*parameter (Field m) 0 1*
        (CFSGReeFFourOuterStarMiddleWord.rawY (Field m))⁻¹ :=
      congrArg (fun u : (Mat (Field m))ˣ=>
        CFSGReeFFourOuterStarMiddleWord.rawY (Field m)*u*
          (CFSGReeFFourOuterStarMiddleWord.rawY (Field m))⁻¹) hparam.symm
    _=CFSGReeFFourOuterStarMiddleWord.rawR (Field m)*parameter (Field m) 0 1*
        (CFSGReeFFourOuterStarMiddleWord.rawR (Field m))⁻¹ :=
      CFSGReeFFourOuterWedgeMiddleWord.selected_parameter_conjugate (Field m) 1
    _=_ := congrArg (fun u : (Mat (Field m))ˣ=>
      CFSGReeFFourOuterStarMiddleWord.rawR (Field m)*u*
        (CFSGReeFFourOuterStarMiddleWord.rawR (Field m))⁻¹) hparam

private theorem raw_outer (m : ℕ) : fixedRawHom m (outerInvolution m)=
    canonicalRoot rawData (Field m) false 0 1*canonicalRoot rawData (Field m) false 5 1*
      canonicalRoot rawData (Field m) false 1 1 := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (CFSGReeFFourOuterFixedRoot.outerWord m 1)=_
  simp only [CFSGReeFFourOuterFixedRoot.outerWord,map_mul,rawHom_root,map_one,
    folded_root_eq_orbitParameter]
  rfl

private theorem hom_triple {G H : Type*} [Group G] [Group H]
    (f g : G→*H) (a b c : G) (ha : f a=g a) (hb : f b=g b) (hc : f c=g c) :
    f (a*b*c)=g (a*b*c) := by
  simp only [map_mul]
  exact congrArg₂ (fun u v : H=>u*v) (congrArg₂ (fun u v : H=>u*v) ha hb) hc

private theorem raw_whole_relation (m : ℕ) :
    fixedRawHom m (fourCycle m)*fixedRawHom m (outerInvolution m)*
      (fixedRawHom m (fourCycle m))⁻¹=
    fixedRawHom m (fiveWord m)*fixedRawHom m (outerInvolution m)*
      (fixedRawHom m (fiveWord m))⁻¹ := by
  let fy := (MulAut.conj (fixedRawHom m (fourCycle m))).toMonoidHom
  let fr := (MulAut.conj (fixedRawHom m (fiveWord m))).toMonoidHom
  have ht := hom_triple fy fr
    (canonicalRoot rawData (Field m) false 0 1)
    (canonicalRoot rawData (Field m) false 5 1)
    (canonicalRoot rawData (Field m) false 1 1)
    (node_zero_relation m) (node_five_relation m) (node_one_relation m)
  exact (congrArg fy (raw_outer m)).trans (ht.trans (congrArg fr (raw_outer m)).symm)

private theorem injective_conjugation_transfer {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Injective f) (y r x : G)
    (h : f y*f x*(f y)⁻¹=f r*f x*(f r)⁻¹) : y*x*y⁻¹=r*x*r⁻¹ :=
  hf (by simpa only [map_mul,map_inv] using h)

private theorem fixed_raw_injective (m : ℕ) : Function.Injective (fixedRawHom m) := by
  intro a b h
  exact Subtype.ext (rawHom_injective (Field m) h)

theorem outer_middle_conjugation (m : ℕ) :
    fourCycle m*outerInvolution m*(fourCycle m)⁻¹=
      fiveWord m*outerInvolution m*(fiveWord m)⁻¹ :=
  injective_conjugation_transfer (fixedRawHom m) (fixed_raw_injective m)
    (fourCycle m) (fiveWord m) (outerInvolution m) (raw_whole_relation m)

theorem outer_middle_conjugate_mem (m : ℕ) (H : Subgroup (originalModelFixed m))
    (hx : outerInvolution m∈H) (hr : fiveWord m∈H) :
    fourCycle m*outerInvolution m*(fourCycle m)⁻¹∈H :=
  Eq.mpr (congrArg (fun g : originalModelFixed m=>g∈H) (outer_middle_conjugation m))
    (H.mul_mem (H.mul_mem hr hx) (H.inv_mem hr))

end SymmetricSubgroupAsymptotics.CFSGReeFFourWholeOuterMiddleRelation
