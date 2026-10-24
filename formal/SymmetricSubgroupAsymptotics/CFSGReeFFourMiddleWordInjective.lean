import SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleFixedWords
import SymmetricSubgroupAsymptotics.CFSGE6GeckMiddleHigherLeading

/-! The four original middle parameters are unique. Ambient simple leading
coordinates recover the first two; the checked higher-factor theorem and
actual simple-parameter injection recover the last two. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordInjective
open CFSG.Models.Chevalley CFSGSerreModelRootGeneration CFSGSerreQuadraticMatrix
open CFSGFFourOriginalMiddleWords CFSGReeFFourMiddleFixedWords
open CFSGReeFFourFieldParameters CFSGE6GeckMiddleHigherLeading
open CFSGE6GeckMiddleFactorInjective CFSGE6GeckMiddleAThreeCollecting
open CFSGE6GeckSignedSimpleParameters CFSGTwistedE6GeckPositiveTwist
open CFSGTwistedE6GeckDiagramCovariance CFSGNormTwoCoordinateLeadingHom
open CFSGExceptionalNormTwoBases CFSGExceptionalCartanPositiveDefinite CFSGNormTwoRootPairing
local notation "A" => CartanMatrix.E₆
local notation "hd" => CartanMatrix.E₆_diag
local notation "hs" => CartanMatrix.E₆_transpose
local notation "hp" => E6_positive_definite
local notation "ho" => CartanMatrix.E₆_off_diag_nonpos
local instance : DecidableEq (Roots A) := Classical.decEq _

private abbrev simplePositive (K : Type) [Field K] (j : Fin 6) (t : K) : Positive K :=
  positiveRoot A hd hs hp ho K j t

def matrixMiddleWord (K : Type) [Field K] (a b c d : K) : Positive K :=
  pairedPositive K (RingEquiv.refl K) a*simplePositive K 3 b*
    higherPositive K d*pairedHigherPositive K c

private theorem matrixMiddleWord_leading (K : Type) [Field K] (a b c d : K) :
    ambientLeading K (matrixMiddleWord K a b c d)=
      Multiplicative.ofAdd (((Pi.single 2 a : Fin 6→K)+Pi.single 4 a)+Pi.single 3 b) := by
  simp only [matrixMiddleWord,map_mul,higherPositive_leading_one,
    pairedHigherPositive_leading_one,mul_one]
  change leadingHom A hd hs hp ho K
    (positiveRoot A hd hs hp ho K 2 a*positiveRoot A hd hs hp ho K 4 a)*
      leadingHom A hd hs hp ho K (positiveRoot A hd hs hp ho K 3 b)=_
  simp only [map_mul,leadingHom_positiveRoot,←_root_.ofAdd_add]

theorem matrixMiddleWord_leading_two (K : Type) [Field K] (a b c d : K) :
    (ambientLeading K (matrixMiddleWord K a b c d)).toAdd 2=a := by
  rw [matrixMiddleWord_leading]
  simp

theorem matrixMiddleWord_leading_three (K : Type) [Field K] (a b c d : K) :
    (ambientLeading K (matrixMiddleWord K a b c d)).toAdd 3=b := by
  rw [matrixMiddleWord_leading]
  simp

private theorem raw_root_one (K : Type) [Field K] [Finite K] [CharP K 2] (a : K) :
    rawHom K (modelRoot CartanMatrix.F₄ K false 1 a)=
      (pairedPositive K (RingEquiv.refl K) a).val := by
  rw [rawHom_root,CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter]
  rfl

private theorem raw_root_two (K : Type) [Field K] [Finite K] [CharP K 2] (b : K) :
    rawHom K (modelRoot CartanMatrix.F₄ K false 2 b)=
      (positiveRoot A hd hs hp ho K 3 b).val := by
  rw [rawHom_root,CFSGFFourE6FixedGeneratedGroup.folded_root_eq_orbitParameter]
  rfl

theorem rawHom_middleWord (m : ℕ) (a b c d : Field m) :
    rawHom (Field m) (middleWord m a b c d)=(matrixMiddleWord (Field m) a b c d).val := by
  simp only [middleWord,map_mul,raw_root_one,raw_root_two,rawHom_middleLong,rawHom_middleShort,
    matrixMiddleWord,simplePositive,Subgroup.coe_mul,higherPositive_val,pairedHigherPositive_val]

theorem middleWord_parameters_eq (m : ℕ) (a b c d a' b' c' d' : Field m)
    (he : middleWord m a b c d=middleWord m a' b' c' d') :
    a=a' ∧ b=b' ∧ c=c' ∧ d=d' := by
  have hr := congrArg (rawHom (Field m)) he
  rw [rawHom_middleWord,rawHom_middleWord] at hr
  have hpos : matrixMiddleWord (Field m) a b c d=matrixMiddleWord (Field m) a' b' c' d' :=
    Subtype.ext hr
  have hl := congrArg (ambientLeading (Field m)) hpos
  have ha := congrArg (fun z : Multiplicative (Fin 6→Field m)=>z.toAdd 2) hl
  have hb := congrArg (fun z : Multiplicative (Fin 6→Field m)=>z.toAdd 3) hl
  dsimp only at ha hb
  rw [matrixMiddleWord_leading_two,matrixMiddleWord_leading_two] at ha
  rw [matrixMiddleWord_leading_three,matrixMiddleWord_leading_three] at hb
  rw [←ha,←hb] at he
  have ht : middleLong (Field m) d*middleShort (Field m) c=
      middleLong (Field m) d'*middleShort (Field m) c' := by
    apply mul_left_cancel (a := modelRoot CartanMatrix.F₄ (Field m) false 1 a*
      modelRoot CartanMatrix.F₄ (Field m) false 2 b)
    simpa only [middleWord,mul_assoc] using he
  have hh := congrArg (rawHom (Field m)) ht
  simp only [map_mul,rawHom_middleLong,rawHom_middleShort] at hh
  have hc := middleFactor_snd_eq (Field m) (RingEquiv.refl (Field m)) d d' c c' hh
  rw [←hc] at hh
  have hd0 := mul_right_cancel hh
  have hd1 : (Multiplicative.ofAdd d : Multiplicative (Field m))=Multiplicative.ofAdd d' := by
    apply rawSimple_positive_injective (Field m) 3
    apply (MulAut.conj (canonicalWeyl rawData (Field m) 2*canonicalWeyl rawData (Field m) 4)).injective
    exact hd0
  have hparamd : d=d' := congrArg (Multiplicative.toAdd : Multiplicative (Field m)→Field m) hd1
  exact ⟨ha,hb,hc,hparamd⟩

end SymmetricSubgroupAsymptotics.CFSGReeFFourMiddleWordInjective
