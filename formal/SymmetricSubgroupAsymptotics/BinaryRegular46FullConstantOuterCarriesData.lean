import SymmetricSubgroupAsymptotics.FiniteEightRowSlices
import SymmetricSubgroupAsymptotics.DerivedSignedPairOffsetWords
import SymmetricSubgroupAsymptotics.BinaryLinearConstraintCertificate
import SymmetricSubgroupAsymptotics.BinaryBitmaskCoordinates
import Mathlib.Logic.Equiv.Fin.Basic
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
abbrev V := Fin 16 → ZMod 2
abbrev Offsets := Fin 96 → ZMod 2

def generatorImages : Fin 6 → Fin 16 → Fin 16 := ![![8,9,10,3,4,5,6,15,0,1,2,11,12,13,14,7],![8,9,2,11,4,5,14,7,0,1,10,3,12,13,6,15],![8,1,10,11,4,13,6,7,0,9,2,3,12,5,14,15],![7,2,1,4,3,6,5,0,15,10,9,12,11,14,13,8],![2,7,0,5,6,3,4,1,10,15,8,13,14,11,12,9],![4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11]]
theorem generator_involution : ∀ i j, generatorImages i (generatorImages i j) = j := by decide +kernel
def generators (i : Fin 6) : Equiv.Perm (Fin 16) := {
  toFun := generatorImages i
  invFun := generatorImages i
  left_inv := generator_involution i
  right_inv := generator_involution i }
def relators : Fin 21 → DerivedGeneratorWord (Fin 6) := ![(.comm 0 1),(.comm 0 2),(.comm 0 3),(.comm 0 4),(.comm 1 2),(.mul (.comm 1 3) (.inv (.comm 0 5))),(.mul (.comm 1 4) (.inv (.comm 0 5))),(.mul (.comm 1 5) (.inv (.comm 0 5))),(.mul (.comm 2 3) (.inv (.comm 0 5))),(.comm 2 4),(.mul (.comm 2 5) (.inv (.comm 0 5))),(.comm 3 4),(.comm 3 5),(.comm 4 5),(.mul (.comm 0 5) (.comm 0 5)),(.mul (.comm 0 5) (.conj 0 (.inv (.comm 0 5)))),(.mul (.comm 0 5) (.conj 1 (.inv (.comm 0 5)))),(.mul (.comm 0 5) (.conj 2 (.inv (.comm 0 5)))),(.mul (.comm 0 5) (.conj 3 (.inv (.comm 0 5)))),(.mul (.comm 0 5) (.conj 4 (.inv (.comm 0 5)))),(.mul (.comm 0 5) (.conj 5 (.inv (.comm 0 5))))]
def rawWords : Fin 21 → List (BinarySignedOffsetWord.Letter (Fin 6)) := ![[(0, true),(1, true),(0, false),(1, false)],[(0, true),(2, true),(0, false),(2, false)],[(0, true),(3, true),(0, false),(3, false)],[(0, true),(4, true),(0, false),(4, false)],[(1, true),(2, true),(1, false),(2, false)],[(1, true),(3, true),(1, false),(3, false),(5, true),(0, true),(5, false),(0, false)],[(1, true),(4, true),(1, false),(4, false),(5, true),(0, true),(5, false),(0, false)],[(1, true),(5, true),(1, false),(5, false),(5, true),(0, true),(5, false),(0, false)],[(2, true),(3, true),(2, false),(3, false),(5, true),(0, true),(5, false),(0, false)],[(2, true),(4, true),(2, false),(4, false)],[(2, true),(5, true),(2, false),(5, false),(5, true),(0, true),(5, false),(0, false)],[(3, true),(4, true),(3, false),(4, false)],[(3, true),(5, true),(3, false),(5, false)],[(4, true),(5, true),(4, false),(5, false)],[(0, true),(5, true),(0, false),(5, false),(0, true),(5, true),(0, false),(5, false)],[(0, true),(5, true),(0, false),(5, false),(0, true),(5, true),(0, true),(5, false),(0, false),(0, false)],[(0, true),(5, true),(0, false),(5, false),(1, true),(5, true),(0, true),(5, false),(0, false),(1, false)],[(0, true),(5, true),(0, false),(5, false),(2, true),(5, true),(0, true),(5, false),(0, false),(2, false)],[(0, true),(5, true),(0, false),(5, false),(3, true),(5, true),(0, true),(5, false),(0, false),(3, false)],[(0, true),(5, true),(0, false),(5, false),(4, true),(5, true),(0, true),(5, false),(0, false),(4, false)],[(0, true),(5, true),(0, false),(5, false),(5, true),(5, true),(0, true),(5, false),(0, false),(5, false)]]
theorem relators_words : ∀ r, BinarySignedOffsetWord.ofDerived (relators r) = rawWords r := by decide +kernel
theorem relators_top : ∀ r, (relators r).eval generators = 1 := by decide +kernel

def sourceOffsets : Offsets →ₗ[ZMod 2] (Fin 6 → Fin 16 → ZMod 2) where
  toFun x i j := x (finProdFinEquiv (i,generatorImages i j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def layerChange : V →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 16 16 (![257,514,1028,2056,4112,8224,16448,32896,256,512,1024,2048,4096,8192,16384,32768] : Fin 16 → ℕ)).mulVecLin
def squareMap (i : Fin 6) : Offsets →ₗ[ZMod 2] V :=
  layerChange.comp ((BinarySignedOffsetWord.offset generators [(i,true),(i,true)]).comp sourceOffsets)
def relatorMap (r : Fin 21) : Offsets →ₗ[ZMod 2] V :=
  layerChange.comp ((BinarySignedOffsetWord.offset generators (rawWords r)).comp sourceOffsets)
def annihilatorSpace {q : ℕ} (masks : Fin q → ℕ) : Submodule (ZMod 2) V :=
  ⨅ i,(binaryRowFunctional (binaryVectorOfMask 16 (masks i))).ker
def stateAnnihilator : Fin 4 → ℕ := ![57600,53760,46080,30720]
def radicalAnnihilator : Fin 8 → ℕ := ![255,33024,33280,33792,34816,36864,40960,49152]
abbrev wideState := annihilatorSpace stateAnnihilator
abbrev lowerRadical := annihilatorSpace radicalAnnihilator
abbrev pointState := wideState.comap layerChange
abbrev pointRadical := lowerRadical.comap layerChange

def inputMasks : Fin 192 → ℕ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,18446462598732840960,18446462598732840960,0,1208907372870555465154560,0,1208907372870555465154560,0,79226953588444722964369244160,79226953588444722964369244160,79226953588444722964369244160,79226953588444722964369244160,2273790795,0,0,0,0,0,0,0,149013890346285,0,0,0,0,0,0,0,9765774316976209920,0,34695,34695,39321,39321,57825,57825,640009785637352893317120,34695,0,34695,43690,53970,43690,53970,82786252554240,0,0,0,0,0,0,0,37283272289936196174868381695,39321,2273815210,2273823948,2576941056,2576980377,3789662890,3789671628,37284125623296013556091191295,2273810841,43690,2273823948,2863267840,3537017241,2863311530,3537030348,63381562870755778375790362623,2576980377,2863311530,3435973836,0,2576980377,2863311530,3435973836,37283272292106649711694381055,39321,149013890378410,149013890387148,168882409046016,168882409085337,248356483934890,248356483943628,213336595212450964439040,149013890334720,0,149013890334720,187647121162240,231799384965120,187647121162240,231799384965120,52817969058963430113594638335,168882409085337,187647121205930,225176545447116,0,168882409085337,187647121205930,225176545447116,0,9765774316976209920,640009785637352893317120,640019551411669869527040,725356721364065767653376,725359614926826353197056,1066695273703987310755840,1066698167266747896299520,0,11067877559239704576,41943681323827200948919336960,41943681326286729295417049088,47536172153066833778621546496,47536172164134711337861251072,69906135531513573759873187840,69906135533973102106370899968,0,41944406655953281549709869056,805938248580370310103040,41944648437427855660802899968,52817969058963148642912829440,65246451829025258892171411456,52818774997211729013222932480,65246693610499833003264442368,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4294967295,0,0,0,0,0,0,0,281470681808895,0,0,0,0,0,0,0,18446462598732840960,0,65535,65535,0,0,65535,65535,1208907372870555465154560,65535,0,65535,0,65535,0,65535,79226953588444722964369244160,0,0,0,0,0,0,0]
def targetMasks : Fin 6 → Fin 8 → ℕ := ![![34695,0,0,0,0,0,0,0],![1263206400,0,0,0,0,0,0,0],![49671296778240,0,0,0,0,0,0,0],![0,0,9765774316976209920,9765774316976209920,11067877559239704576,11067877559239704576,16276290528293683200,16276290528293683200],![0,640009785637352893317120,0,640009785637352893317120,805938248580370310103040,995570777658104500715520,805938248580370310103040,995570777658104500715520],![0,47536172153066833778621546496,52817969058963148642912829440,63381562870755778371495395328,0,47536172153066833778621546496,52817969058963148642912829440,63381562870755778371495395328]]
def input (i : Fin 192) : Offsets := binaryVectorOfMask 96 (inputMasks i)
def target (i : Fin 6) (j : Fin 8) : Offsets := binaryVectorOfMask 96 (targetMasks i j)
def inputSource : Fin 192 → (Fin 6 × Fin 4) ⊕ (Fin 21 × Fin 8) := ![(.inl (0,0)),(.inl (0,1)),(.inl (0,2)),(.inl (0,3)),(.inl (1,0)),(.inl (1,1)),(.inl (1,2)),(.inl (1,3)),(.inl (2,0)),(.inl (2,1)),(.inl (2,2)),(.inl (2,3)),(.inl (3,0)),(.inl (3,1)),(.inl (3,2)),(.inl (3,3)),(.inl (4,0)),(.inl (4,1)),(.inl (4,2)),(.inl (4,3)),(.inl (5,0)),(.inl (5,1)),(.inl (5,2)),(.inl (5,3)),(.inr (0,0)),(.inr (0,1)),(.inr (0,2)),(.inr (0,3)),(.inr (0,4)),(.inr (0,5)),(.inr (0,6)),(.inr (0,7)),(.inr (1,0)),(.inr (1,1)),(.inr (1,2)),(.inr (1,3)),(.inr (1,4)),(.inr (1,5)),(.inr (1,6)),(.inr (1,7)),(.inr (2,0)),(.inr (2,1)),(.inr (2,2)),(.inr (2,3)),(.inr (2,4)),(.inr (2,5)),(.inr (2,6)),(.inr (2,7)),(.inr (3,0)),(.inr (3,1)),(.inr (3,2)),(.inr (3,3)),(.inr (3,4)),(.inr (3,5)),(.inr (3,6)),(.inr (3,7)),(.inr (4,0)),(.inr (4,1)),(.inr (4,2)),(.inr (4,3)),(.inr (4,4)),(.inr (4,5)),(.inr (4,6)),(.inr (4,7)),(.inr (5,0)),(.inr (5,1)),(.inr (5,2)),(.inr (5,3)),(.inr (5,4)),(.inr (5,5)),(.inr (5,6)),(.inr (5,7)),(.inr (6,0)),(.inr (6,1)),(.inr (6,2)),(.inr (6,3)),(.inr (6,4)),(.inr (6,5)),(.inr (6,6)),(.inr (6,7)),(.inr (7,0)),(.inr (7,1)),(.inr (7,2)),(.inr (7,3)),(.inr (7,4)),(.inr (7,5)),(.inr (7,6)),(.inr (7,7)),(.inr (8,0)),(.inr (8,1)),(.inr (8,2)),(.inr (8,3)),(.inr (8,4)),(.inr (8,5)),(.inr (8,6)),(.inr (8,7)),(.inr (9,0)),(.inr (9,1)),(.inr (9,2)),(.inr (9,3)),(.inr (9,4)),(.inr (9,5)),(.inr (9,6)),(.inr (9,7)),(.inr (10,0)),(.inr (10,1)),(.inr (10,2)),(.inr (10,3)),(.inr (10,4)),(.inr (10,5)),(.inr (10,6)),(.inr (10,7)),(.inr (11,0)),(.inr (11,1)),(.inr (11,2)),(.inr (11,3)),(.inr (11,4)),(.inr (11,5)),(.inr (11,6)),(.inr (11,7)),(.inr (12,0)),(.inr (12,1)),(.inr (12,2)),(.inr (12,3)),(.inr (12,4)),(.inr (12,5)),(.inr (12,6)),(.inr (12,7)),(.inr (13,0)),(.inr (13,1)),(.inr (13,2)),(.inr (13,3)),(.inr (13,4)),(.inr (13,5)),(.inr (13,6)),(.inr (13,7)),(.inr (14,0)),(.inr (14,1)),(.inr (14,2)),(.inr (14,3)),(.inr (14,4)),(.inr (14,5)),(.inr (14,6)),(.inr (14,7)),(.inr (15,0)),(.inr (15,1)),(.inr (15,2)),(.inr (15,3)),(.inr (15,4)),(.inr (15,5)),(.inr (15,6)),(.inr (15,7)),(.inr (16,0)),(.inr (16,1)),(.inr (16,2)),(.inr (16,3)),(.inr (16,4)),(.inr (16,5)),(.inr (16,6)),(.inr (16,7)),(.inr (17,0)),(.inr (17,1)),(.inr (17,2)),(.inr (17,3)),(.inr (17,4)),(.inr (17,5)),(.inr (17,6)),(.inr (17,7)),(.inr (18,0)),(.inr (18,1)),(.inr (18,2)),(.inr (18,3)),(.inr (18,4)),(.inr (18,5)),(.inr (18,6)),(.inr (18,7)),(.inr (19,0)),(.inr (19,1)),(.inr (19,2)),(.inr (19,3)),(.inr (19,4)),(.inr (19,5)),(.inr (19,6)),(.inr (19,7)),(.inr (20,0)),(.inr (20,1)),(.inr (20,2)),(.inr (20,3)),(.inr (20,4)),(.inr (20,5)),(.inr (20,6)),(.inr (20,7))]
def inputActual (k : Fin 192) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  match inputSource k with
  | .inl ij => (binaryRowFunctional (binaryVectorOfMask 16 (stateAnnihilator ij.2))).comp (squareMap ij.1)
  | .inr ij => (binaryRowFunctional (binaryVectorOfMask 16 (radicalAnnihilator ij.2))).comp (relatorMap ij.1)
def targetActual (i : Fin 6) (j : Fin 8) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  (binaryRowFunctional (binaryVectorOfMask 16 (radicalAnnihilator j))).comp (squareMap i)

end SymmetricSubgroupAsymptotics.BinaryRegular46FullConstantOuterCarries
