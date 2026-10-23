import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedBruhatCell
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckCentralTwistedCellFactors
import SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckRelativeRootGenerated
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateRootNormalizerEnvelope
import SymmetricSubgroupAsymptotics.CFSGNormTwoCoordinateBorelRootNormalization
import SymmetricSubgroupAsymptotics.CFSGFixedSubgroupConjugation

/-! One literal E6 relative-root cover works for every coefficient-field
automorphism, including identity (the folded F4 case). The finite menu
is the actual relative-Weyl orbit of the chosen dominant root. Fixedness
is retained in the positive coordinate, and the enlarged diagonal
normalizer normalizes each root line without a torus-recognition premise. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRootFamilyCover
open CFSGIntegerMatrixPairing CFSGNormTwoRootPairing
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite
open CFSGExceptionalNormalizerWordIdentity CFSGSignedCartanReflections
open CFSGTwistedE6GeckDiagramCovariance CFSGTwistedE6GeckSourceAction
open CFSGTwistedE6GeckMatrixTwist CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckCentralTwistedBruhatCell CFSGTwistedE6GeckCentralTwistedCellFactors
open CFSGTwistedE6GeckInversionParts CFSGTwistedE6GeckRelativeRootGenerated
open CFSGTwistedE6GeckRelativeWordTwist CFSGTwistedE6WeylChamber
open CFSGTwistedE6FixedWordClassification
open CFSGNormTwoCoordinateRootNormalizerEnvelope CFSGNormTwoCoordinateRootSubgroup
open CFSGNormTwoCoordinateRootWeylAction CFSGNormTwoCoordinateBorelRootNormalization
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckIntegralWord
open CFSGSubgroupConjugateOrbitCardinality
open CFSGFixedSubgroupConjugation CFSGCentralTwistedCommutatorLift
open CFSGNormTwoCoordinatePositiveRootGenerators
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

def RootLine (K : Type) [Field K] (k : Roots A) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ := rootSubgroup A hd hs hp ho K k

def relativeRootMenu (theta : Roots A) : Set (Roots A) :=
  Set.range (fun r : List (Fin 4)=>rootAction (expandRelative r) theta)

theorem relativeRootMenu_card_le (theta : Roots A) :
    Nat.card (relativeRootMenu theta) ≤ Nat.card (Roots A) :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

def fixedRootLine (K : Type) [Field K] (sigma : K≃+*K) (k : Roots A) :
    Subgroup (Matrix GeckIndex GeckIndex K)ˣ :=
  RootLine K k ⊓ fixedSubgroup (unitTwist K sigma)

theorem relative_rootLine_map (K : Type) [Field K]
    (r : List (Fin 4)) (theta : Roots A) :
    (RootLine K theta).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=
        RootLine K (rootAction (expandRelative r) theta) := by
  change (rootSubgroup A hd hs hp ho K theta).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=
        rootSubgroup A hd hs hp ho K (rootAction (expandRelative r) theta)
  rw [word_eq_canonicalWord]
  exact rootSubgroup_map_word A hd hs hp ho K (expandRelative r) theta

theorem relative_fixedRootLine_map (K : Type) [Field K] (sigma : K≃+*K)
    (r : List (Fin 4)) (theta : Roots A) :
    (fixedRootLine K sigma theta).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=
        fixedRootLine K sigma (rootAction (expandRelative r) theta) := by
  have hW : unitTwist K sigma (wordUnit A hs hp E6Base E6Index K (expandRelative r))=
      wordUnit A hs hp E6Base E6Index K (expandRelative r) := by
    rw [word_eq_canonicalWord]
    exact relative_word_fixed K sigma r
  rw [fixedRootLine,map_inf_fixed (unitTwist K sigma) _ _ hW,relative_rootLine_map]
  rfl

theorem fixedRootLine_le_generated (K : Type) [Field K] (sigma : K≃+*K)
    (theta : Roots A) (htheta : ∀i,0≤theta.val i) (k : relativeRootMenu theta) :
    fixedRootLine K sigma k.val ≤ fixedRootGenerated K sigma := by
  have hbase : fixedRootLine K sigma theta ≤ fixedRootGenerated K sigma := by
    intro x hx
    exact signedFixed_le_generated K sigma false
      ⟨positive_root_subgroup_le A hd hs hp ho K theta htheta hx.1,hx.2⟩
  obtain ⟨r,hr⟩ := k.property
  rw [←hr,←relative_fixedRootLine_map K sigma r theta]
  rintro _ ⟨x,hx,rfl⟩
  have hW := relativeWord_mem_generated K sigma r
  exact (fixedRootGenerated K sigma).mul_mem
    ((fixedRootGenerated K sigma).mul_mem hW (hbase hx))
    ((fixedRootGenerated K sigma).inv_mem hW)

private theorem conjugate_cell {G : Type*} [Group G]
    (S T : Subgroup G) (g u d w v : G) (he : g=u*d*w*v)
    (hv : S.map (MulAut.conj v).toMonoidHom=S)
    (hw : S.map (MulAut.conj w).toMonoidHom=T)
    (hD : T.map (MulAut.conj d).toMonoidHom=T) :
    S.map (MulAut.conj g).toMonoidHom=T.map (MulAut.conj u).toMonoidHom := by
  rw [he,conjugate_mul,hv,conjugate_mul,hw,conjugate_mul,hD]

theorem conjugate_eq_fixed_positive_conjugate (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (theta : Roots A) (htheta : ∀i,0≤theta.val i)
    (hdom : ∀i,0 ≤ integerPairing A theta.val (Pi.single i (1 : ℤ) : Fin 6→ℤ))
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g∈MatrixGroup K)
    (hfixed : unitTwist K sigma g=g) :
    ∃ k : relativeRootMenu theta, ∃ u : signedFixed K sigma false,
      (RootLine K theta).map (MulAut.conj g).toMonoidHom =
        (RootLine K k.val).map (MulAut.conj u.val).toMonoidHom := by
  have hz : (1 : MatrixGroup K)∈Subgroup.center (MatrixGroup K) := Subgroup.one_mem _
  have htwist : unitTwist K sigma g=(1 : MatrixGroup K).val*g := by simpa using hfixed
  obtain ⟨r,b,hb,v,he⟩ := exists_central_twisted_relative_cell K sigma g hg 1 hz htwist
  have hW : unitTwist K sigma (wordUnit A hs hp E6Base E6Index K (expandRelative r))=
      wordUnit A hs hp E6Base E6Index K (expandRelative r) := by
    rw [word_eq_canonicalWord]
    exact relative_word_fixed K sigma r
  have hcell : unitTwist K sigma
      (b*wordUnit A hs hp E6Base E6Index K (expandRelative r)*inversionEmbedding K (expandRelative r) v)=
      (1 : MatrixGroup K).val*
      (b*wordUnit A hs hp E6Base E6Index K (expandRelative r)*inversionEmbedding K (expandRelative r) v) := by
    rw [←he]
    exact htwist
  have hcoords := central_twisted_cell_coordinates K sigma (expandRelative r) hW 1 hz ⟨b,hb⟩ v hcell
  obtain ⟨u,hu,huf,d,hD,_,hbe⟩ := exists_central_twisted_envelope_factors K sigma b hb 1 hz hcoords.1
  let k : relativeRootMenu theta := ⟨rootAction (expandRelative r) theta,⟨r,rfl⟩⟩
  have hw : (RootLine K theta).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=RootLine K k.val := by
    change (rootSubgroup A hd hs hp ho K theta).map
      (MulAut.conj (wordUnit A hs hp E6Base E6Index K (expandRelative r))).toMonoidHom=
        rootSubgroup A hd hs hp ho K (rootAction (expandRelative r) theta)
    rw [word_eq_canonicalWord]
    exact rootSubgroup_map_word A hd hs hp ho K (expandRelative r) theta
  have hv : (RootLine K theta).map
      (MulAut.conj (inversionEmbedding K (expandRelative r) v)).toMonoidHom=RootLine K theta :=
    conjugate_eq_of_mem_normalizer (RootLine K theta) _
      (Subgroup.centralizer_le_normalizer _
        (positive_le_centralizer_root A hd hs hp ho K theta htheta hdom v.val.property))
  have hdroot : d∈Subgroup.normalizer (RootLine K k.val : Set (Matrix GeckIndex GeckIndex K)ˣ) :=
    diagonalNormalizer_le_normalizer_root A hd hs hp ho K E6Signs E6_signs_square
      E6_signs_cartan (E6_normalizer_word_identity K) (by decide) k.val hD
  have hdmap : (RootLine K k.val).map (MulAut.conj d).toMonoidHom=RootLine K k.val :=
    conjugate_eq_of_mem_normalizer (RootLine K k.val) d hdroot
  refine ⟨k,⟨u,⟨hu,huf⟩⟩,?_⟩
  apply conjugate_cell _ _ g u d _ _ _ hv hw hdmap
  rw [he,hbe]

theorem fixed_conjugate_eq_fixed_positive_conjugate (K : Type) [Field K] [Finite K]
    (sigma : K≃+*K) (theta : Roots A) (htheta : ∀i,0≤theta.val i)
    (hdom : ∀i,0 ≤ integerPairing A theta.val (Pi.single i (1 : ℤ) : Fin 6→ℤ))
    (g : (Matrix GeckIndex GeckIndex K)ˣ) (hg : g∈MatrixGroup K)
    (hfixed : unitTwist K sigma g=g) :
    ∃ k : relativeRootMenu theta, ∃ u : signedFixed K sigma false,
      (fixedRootLine K sigma theta).map (MulAut.conj g).toMonoidHom =
        (fixedRootLine K sigma k.val).map (MulAut.conj u.val).toMonoidHom := by
  obtain ⟨k,u,he⟩ := conjugate_eq_fixed_positive_conjugate K sigma theta htheta hdom g hg hfixed
  have huf : unitTwist K sigma u.val=u.val := u.property.2
  refine ⟨k,u,?_⟩
  rw [fixedRootLine,fixedRootLine,map_inf_fixed (unitTwist K sigma) _ _ hfixed,
    map_inf_fixed (unitTwist K sigma) _ _ huf,he]

end SymmetricSubgroupAsymptotics.CFSGTwistedE6GeckFixedRootFamilyCover
