import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeOppositionLattice
import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleSquareSelectedWordTransport
import SymmetricSubgroupAsymptotics.CFSGReeFFourSignedOuterOddProduct
import SymmetricSubgroupAsymptotics.CFSGTitsMiddleWeylRecovery

/-! Actual opposition of the WHOLE parameter-one outer involution.
The checked lattice opposition reverses the two outer E6 nodes; their
root units commute. Equality is first proved under the faithful original
raw hom, then transported through the FULL derived-centre quotient.
No finite matrix diagnostic or automorphism lift is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical Matrix
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionOuterWord
open CFSGReeFFourRelativeOppositionLattice CFSGReeFFourInversionSuffixSignPilot
open CFSGReeFFourMiddleSquareSelectedWordTransport CFSGNormTwoCoordinateSelectedRootElement
open CFSGNormTwoGeckColumns CFSGNormTwoRootPairing CFSGSerreDiagram
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGSerreQuadraticMatrix CFSGSerreQuadraticWeylWord CFSGFFourE6PositiveRootUnits
open CFSGNormTwoGeckOrthogonalWeyl CFSGNormTwoGeckIntegralWord
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourOppositionFixedPositiveNegative CFSGReeFFourRelativePositiveSubgroups
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourOuterThreeWord
open CFSGReeFFourOuterFixedRoot CFSGFFourOriginalMiddleWords CFSGFFourE6FixedGeneratedGroup
open CFSGReeFFourFieldParameters CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckDiagramCovariance CFSGReeFFourSignedOuterOddProduct
open CFSGReeFFourAmbientCentralQuotientAction CFSGTitsMiddleWeylRecovery
open CFSGReeFFourOriginalPositiveSylow
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
private abbrev Mat (K : Type) := Matrix GeckIndex GeckIndex K
private abbrev negSimple (i : Fin 6) := negativeIndex A hs hp (E6Index i)

private theorem opposition_degree (i : Fin 6) :
    vectorWord relativeOppositionWord (Pi.single i (1 : ℤ))=
      (negSimple (e6Permutation i)).val := by
  have hn : (negSimple (e6Permutation i)).val=
      -(Pi.single (e6Permutation i) (1 : ℤ) : Fin 6→ℤ) :=
    negative_val A hs hp (E6Index (e6Permutation i))
  exact ((vectorWord_eq relativeOppositionWord (Pi.single i (1 : ℤ))).trans
    (relative_opposition_simple_lattice i)).trans hn.symm

private theorem outer_degree (i : Fin 6) (hi : i=0∨i=5∨i=1) :
    vectorWord [0,5,1] (Pi.single i (1 : ℤ))=(negSimple i).val := by
  have hn : (negSimple i).val=-(Pi.single i (1 : ℤ) : Fin 6→ℤ) :=
    negative_val A hs hp (E6Index i)
  apply Eq.trans _ hn.symm
  rcases hi with rfl|rfl|rfl <;> decide +kernel

private theorem opposition_simple (K : Type) [CommRing K] [CharP K 2] (i : Fin 6) :
    canonicalWord e6Data K relativeOppositionWord*canonicalRoot e6Data K false i 1*
      (canonicalWord e6Data K relativeOppositionWord)⁻¹=
        selectedRootElement A hd hs hp ho K (negSimple (e6Permutation i)) 1 :=
  word_simple_one K relativeOppositionWord i _ (opposition_degree i)

private theorem outer_simple (K : Type) [CommRing K] [CharP K 2]
    (i : Fin 6) (hi : i=0∨i=5∨i=1) :
    canonicalWord e6Data K [0,5,1]*canonicalRoot e6Data K false i 1*
      (canonicalWord e6Data K [0,5,1])⁻¹=
        selectedRootElement A hd hs hp ho K (negSimple i) 1 :=
  word_simple_one K [0,5,1] i _ (outer_degree i hi)

private theorem hom_triple_swap {G H : Type*} [Group G] [Group H]
    (F T : G→*H) (a b c : G) (ha : F a=T b) (hb : F b=T a)
    (hc : F c=T c) (hab : Commute a b) : F (a*b*c)=T (a*b*c) := by
  simp only [map_mul]
  rw [ha,hb,hc]
  exact congrArg (fun u : H=>u*T c) (hab.map T).eq.symm

private theorem raw_triple_opposition (K : Type) [CommRing K] [CharP K 2] :
    (MulAut.conj (canonicalWord e6Data K relativeOppositionWord))
      (canonicalRoot e6Data K false 0 1*canonicalRoot e6Data K false 5 1*
        canonicalRoot e6Data K false 1 1)=
    (MulAut.conj (canonicalWord e6Data K [0,5,1]))
      (canonicalRoot e6Data K false 0 1*canonicalRoot e6Data K false 5 1*
        canonicalRoot e6Data K false 1 1) := by
  have h0 := opposition_simple K 0
  have h5 := opposition_simple K 5
  have h1 := opposition_simple K 1
  have p0 : e6Permutation 0=5 := by decide
  have p5 : e6Permutation 5=0 := by decide
  have p1 : e6Permutation 1=1 := by decide
  rw [p0] at h0
  rw [p5] at h5
  rw [p1] at h1
  exact hom_triple_swap
    (MulAut.conj (canonicalWord e6Data K relativeOppositionWord)).toMonoidHom
    (MulAut.conj (canonicalWord e6Data K [0,5,1])).toMonoidHom
    (canonicalRoot e6Data K false 0 1) (canonicalRoot e6Data K false 5 1)
    (canonicalRoot e6Data K false 1 1)
    (h0.trans (outer_simple K 5 (Or.inr (Or.inl rfl))).symm)
    (h5.trans (outer_simple K 0 (Or.inl rfl)).symm)
    (h1.trans (outer_simple K 1 (Or.inr (Or.inr rfl))).symm)
    (orthogonal_signed_roots A hs hp E6Base E6Index K 0 5
      (by rw [E6_cartan]; decide) false false 1 1)

private theorem raw_outer (m : ℕ) : fixedRawHom m (outerInvolution m)=
    canonicalRoot e6Data (Field m) false 0 1*canonicalRoot e6Data (Field m) false 5 1*
      canonicalRoot e6Data (Field m) false 1 1 := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (CFSGReeFFourOuterFixedRoot.outerWord m 1)=_
  simp only [CFSGReeFFourOuterFixedRoot.outerWord,map_mul,rawHom_root,map_one,
    folded_root_eq_orbitParameter]
  rfl

private theorem raw_outer_weyl (m : ℕ) : fixedRawHom m (outerFixedWeyl m)=
    canonicalWord e6Data (Field m) [0,5,1] := by
  rw [fixedRawHom_apply]
  exact (rawHom_outerRelativeWeyl m).trans
    (word_eq_canonicalWord A hs hp E6Base E6Index (Field m) [0,5,1])

private theorem raw_opposition (m : ℕ) : fixedRawHom m (oppositionFixed m)=
    canonicalWord e6Data (Field m) relativeOppositionWord :=
  (fixedRawHom_oppositionFixed m).trans
    (word_eq_canonicalWord A hs hp E6Base E6Index (Field m) relativeOppositionWord)

private theorem injective_conjugation {G H : Type*} [Group G] [Group H]
    (f : G→*H) (hf : Function.Injective f) (a b x : G)
    (h : f a*f x*(f a)⁻¹=f b*f x*(f b)⁻¹) : a*x*a⁻¹=b*x*b⁻¹ :=
  hf (by simpa only [map_mul,map_inv] using h)

private theorem raw_injective (m : ℕ) : Function.Injective (fixedRawHom m) := by
  intro a b h
  exact Subtype.ext (rawHom_injective (Field m) h)

theorem opposition_outer_conjugation (m : ℕ) :
    oppositionFixed m*outerInvolution m*(oppositionFixed m)⁻¹=
      outerFixedWeyl m*outerInvolution m*(outerFixedWeyl m)⁻¹ := by
  apply injective_conjugation (fixedRawHom m) (raw_injective m)
  rw [raw_opposition,raw_outer_weyl,raw_outer]
  exact raw_triple_opposition (Field m)

theorem original_opposition_outer_conjugation (m : ℕ) :
    ambientAction m (oppositionFixed m) (originalOuterRoot m)=negativeOriginalOuterRoot m := by
  have he : MulAut.conjNormal (oppositionFixed m) (derivedOuterRoot m)=
      derivedOuterWeyl m*derivedOuterRoot m*(derivedOuterWeyl m)⁻¹ :=
    Subtype.ext (opposition_outer_conjugation m)
  calc
    _=derivedReeHom m (MulAut.conjNormal (oppositionFixed m) (derivedOuterRoot m)) :=
      ambientAction_apply m (oppositionFixed m) (derivedOuterRoot m)
    _=derivedReeHom m (derivedOuterWeyl m*derivedOuterRoot m*(derivedOuterWeyl m)⁻¹) :=
      congrArg (derivedReeHom m) he
    _=negativeOriginalOuterRoot m := by
      rw [map_mul,map_mul,map_inv]
      rfl

theorem original_opposition_outer_product_order (m : ℕ) :
    orderOf (ambientAction m (oppositionFixed m) (originalOuterRoot m)*originalOuterRoot m)=3 := by
  rw [original_opposition_outer_conjugation]
  exact negative_mul_positive_order m

theorem intrinsic_opposition_outer_product_order :
    orderOf ((oppositionRoot*originalOuterRoot 0*oppositionRoot⁻¹)*originalOuterRoot 0)=3 := by
  have h := congrArg (fun F : MulAut CFSG.Models.Tits=>F (originalOuterRoot 0))
    oppositionRoot_action
  change oppositionRoot*originalOuterRoot 0*oppositionRoot⁻¹=
    ambientAction 0 (oppositionFixed 0) (originalOuterRoot 0) at h
  exact (congrArg (fun z : CFSG.Models.Tits=>orderOf (z*originalOuterRoot 0)) h).trans
    (original_opposition_outer_product_order 0)

end SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionOuterWord
