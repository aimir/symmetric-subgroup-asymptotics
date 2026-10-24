import SymmetricSubgroupAsymptotics.CFSGOpposedSubgroupPeelingMembership
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylInvolutions
import SymmetricSubgroupAsymptotics.CFSGReeFFourSimpleInversionBlocks
import SymmetricSubgroupAsymptotics.CFSGReeFFourInversionSuffixSignPilot
import SymmetricSubgroupAsymptotics.CFSGReeFFourRelativeWeylRawWords
import SymmetricSubgroupAsymptotics.CFSGReeFFourOppositionFixedPositiveNegative

/-! Actual source words for alternating peels and inverse suffixes.
All identities here are literal group/list identities; no lattice-action
comparison is used to identify original elements. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeelingWords
open CFSGOpposedSubgroupPeelingChain CFSGOpposedSubgroupPeelingMembership
open CFSGReeFFourSimpleInversionBlocks CFSGReeFFourRelativeWeylInvolutions
open CFSGReeFFourRelativeWeylRawWords CFSGReeFFourInversionSuffixSignPilot
open CFSGReeFFourFixedBruhatCover CFSGReeFFourFixedPositiveFamilies
open CFSGReeFFourFixedModelEquivalence CFSGReeFFourFieldParameters
open CFSGReeFFourRelativeSimpleWeyl CFSGReeFFourPairedModelWords
open CFSGReeFFourOriginalWeylWords CFSGReeFFourFixedWordClassification
open CFSGReeFFourPairedWordActions CFSGReeFFourOppositionFixedPositiveNegative
open CFSGReeFFourRelativeOpposition CFSGFFourOriginalMiddleWords
open CFSGNormTwoGeckWeylWordDegree CFSGNormTwoGeckWeylWordAlgebra
open CFSGNormTwoRootPairing CFSGExceptionalCartanPositiveDefinite
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local notation "b₀" => coordinateBase A hd hs hp ho
local notation "s₀" => coordinateIndexEquiv A hd hs hp ho

def axis (head : Bool) (n : ℕ) : Bool := if n%2=0 then head else !head

def step (m : ℕ) (head : Bool) (n : ℕ) : originalModelFixed m :=
  fixedPairedWord m [axis head n]

def suffixWord (head : Bool) : ℕ → ℕ → List (Fin 6)
  | 0,_ => []
  | _+1,0 => []
  | n+1,k+1 => suffixWord head n k ++ simpleRawWord (axis head n)

def alternatingWord (head : Bool) (n : ℕ) : List Bool :=
  (List.range n).map (axis head)

theorem step_inv (m : ℕ) (head : Bool) (n : ℕ) :
    (step m head n)⁻¹=step m head n := by
  apply Subtype.ext
  change (fixedPairedWord m [axis head n]).val⁻¹=(fixedPairedWord m [axis head n]).val
  rw [single_paired_word_val]
  cases axis head n
  · exact outerRelativeWeyl_inv m
  · exact middleRelativeWeyl_inv m

theorem fixedRawHom_step (m : ℕ) (head : Bool) (n : ℕ) :
    fixedRawHom m (step m head n)=
      wordUnit A hs hp b₀ s₀ (Field m) (simpleRawWord (axis head n)) := by
  rw [fixedRawHom_apply]
  change rawHom (Field m) (fixedPairedWord m [axis head n]).val=_
  rw [single_paired_word_val]
  cases axis head n
  · exact rawHom_outerRelativeWeyl m
  · exact rawHom_middleRelativeWeyl m

theorem fixedRawHom_inverseSuffix (m : ℕ) (head : Bool) (n k : ℕ) :
    fixedRawHom m (inverseSuffix (step m head) n k)=
      wordUnit A hs hp b₀ s₀ (Field m) (suffixWord head n k) := by
  induction n generalizing k with
  | zero =>
    simp only [inverseSuffix,suffixWord,map_one,wordUnit]
    rfl
  | succ n ih =>
    cases k with
    | zero =>
      simp only [inverseSuffix,suffixWord,map_one,wordUnit]
      rfl
    | succ k =>
      rw [inverseSuffix,step_inv,map_mul,ih,fixedRawHom_step,suffixWord,wordUnit_append]
      rfl

private theorem suffix_profile_certificate :
    ∀ head : Bool, ∀ n : Fin 8, ∀ k : Fin 8, k.val≤n.val →
      suffixWord head n.val k.val=conjugatingWord (axis head n.val) k.val := by
  decide +kernel

theorem suffixWord_eq_profile (head : Bool) (n k : Fin 8) (hk : k.val≤n.val) :
    suffixWord head n.val k.val=conjugatingWord (axis head n.val) k.val :=
  suffix_profile_certificate head n k hk

theorem fixedPairedWord_append (m : ℕ) (v w : List Bool) :
    fixedPairedWord m (v++w)=fixedPairedWord m v*fixedPairedWord m w := by
  apply Subtype.ext
  change modelWeylWord (Field m) (expandPaired (v++w))=
    modelWeylWord (Field m) (expandPaired v)*modelWeylWord (Field m) (expandPaired w)
  rw [expandPaired_append,modelWeylWord_append]

theorem wordPrefix_eq_inverse (m : ℕ) (head : Bool) (n : ℕ) :
    wordPrefix (step m head) n=(fixedPairedWord m (alternatingWord head n))⁻¹ := by
  induction n with
  | zero =>
    have hz : fixedPairedWord m []=1 := Subtype.ext rfl
    simp only [wordPrefix,alternatingWord,List.range_zero,List.map_nil,hz,inv_one]
  | succ n ih =>
    have ha : alternatingWord head (n+1)=alternatingWord head n++[axis head n] := by
      simp only [alternatingWord,List.range_succ,List.map_append,List.map_singleton]
    rw [wordPrefix,ih,ha,fixedPairedWord_append,mul_inv_rev]
    change step m head n*(fixedPairedWord m (alternatingWord head n))⁻¹=
      (step m head n)⁻¹*(fixedPairedWord m (alternatingWord head n))⁻¹
    rw [step_inv]

theorem eighth_prefix_eq_opposition (m : ℕ) :
    wordPrefix (step m true) 8=oppositionFixed m := by
  apply Subtype.ext
  have hv (n : ℕ) : (step m true n).val=
      if axis true n then middleRelativeWeyl m else outerRelativeWeyl m :=
    single_paired_word_val m (axis true n)
  change (wordPrefix (step m true) 8).val=
    (outerRelativeWeyl m*middleRelativeWeyl m)^4
  simp only [wordPrefix,Subgroup.coe_mul,Subgroup.coe_one,hv]
  change outerRelativeWeyl m*(middleRelativeWeyl m*(outerRelativeWeyl m*
    (middleRelativeWeyl m*(outerRelativeWeyl m*(middleRelativeWeyl m*
      (outerRelativeWeyl m*(middleRelativeWeyl m*1)))))))=
        (outerRelativeWeyl m*middleRelativeWeyl m)^4
  simp only [pow_succ,pow_zero,mul_one,one_mul,mul_assoc]

end SymmetricSubgroupAsymptotics.CFSGReeFFourInversionPeelingWords
