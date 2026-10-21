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
namespace SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarries
abbrev V := Fin 16 → ZMod 2
abbrev Offsets := Fin 64 → ZMod 2

def generatorImages : Fin 4 → Fin 16 → Fin 16 := ![![8,9,10,11,12,13,14,15,0,1,2,3,4,5,6,7],![7,2,1,4,3,6,5,0,15,10,9,12,11,14,13,8],![2,7,0,5,6,3,4,1,10,15,8,13,14,11,12,9],![4,5,6,7,0,1,2,3,12,13,14,15,8,9,10,11]]
theorem generator_involution : ∀ i j, generatorImages i (generatorImages i j) = j := by decide +kernel
def generators (i : Fin 4) : Equiv.Perm (Fin 16) := {
  toFun := generatorImages i
  invFun := generatorImages i
  left_inv := generator_involution i
  right_inv := generator_involution i }
def relators : Fin 6 → DerivedGeneratorWord (Fin 4) := ![(.comm 0 1),(.comm 0 2),(.comm 0 3),(.comm 1 2),(.comm 1 3),(.comm 2 3)]
def rawWords : Fin 6 → List (BinarySignedOffsetWord.Letter (Fin 4)) := ![[(0, true),(1, true),(0, false),(1, false)],[(0, true),(2, true),(0, false),(2, false)],[(0, true),(3, true),(0, false),(3, false)],[(1, true),(2, true),(1, false),(2, false)],[(1, true),(3, true),(1, false),(3, false)],[(2, true),(3, true),(2, false),(3, false)]]
theorem relators_words : ∀ r, BinarySignedOffsetWord.ofDerived (relators r) = rawWords r := by decide +kernel
theorem relators_top : ∀ r, (relators r).eval generators = 1 := by decide +kernel

def sourceOffsets : Offsets →ₗ[ZMod 2] (Fin 4 → Fin 16 → ZMod 2) where
  toFun x i j := x (finProdFinEquiv (i,generatorImages i j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
def layerChange : V →ₗ[ZMod 2] V :=
  (binaryRectangularMatrixOfColumnMasks 16 16 (![257,514,1028,2056,4112,8224,16448,32896,256,512,1024,2048,4096,8192,16384,32768] : Fin 16 → ℕ)).mulVecLin
def squareMap (i : Fin 4) : Offsets →ₗ[ZMod 2] V :=
  layerChange.comp ((BinarySignedOffsetWord.offset generators [(i,true),(i,true)]).comp sourceOffsets)
def relatorMap (r : Fin 6) : Offsets →ₗ[ZMod 2] V :=
  layerChange.comp ((BinarySignedOffsetWord.offset generators (rawWords r)).comp sourceOffsets)
def annihilatorSpace {q : ℕ} (masks : Fin q → ℕ) : Submodule (ZMod 2) V :=
  ⨅ i,(binaryRowFunctional (binaryVectorOfMask 16 (masks i))).ker
def stateAnnihilator : Fin 5 → ℕ := ![255,57600,53760,46080,30720]
def radicalAnnihilator : Fin 11 → ℕ := ![225,210,180,120,33024,33280,33792,34816,36864,40960,49152]
abbrev wideState := annihilatorSpace stateAnnihilator
abbrev lowerRadical := annihilatorSpace radicalAnnihilator
abbrev pointState := wideState.comap layerChange
abbrev pointRadical := lowerRadical.comap layerChange

def inputMasks : Fin 86 → ℕ := ![65535,0,0,0,0,0,0,4294901760,4294901760,0,0,281470681743360,0,281470681743360,0,0,18446462598732840960,18446462598732840960,18446462598732840960,18446462598732840960,3789619200,3536978175,3031695615,2021130240,0,34695,34695,39321,39321,57825,57825,248356483891455,231799384965120,198685187113215,132456791408640,34695,0,34695,43690,53970,43690,53970,16276290528293683455,15191204493074104575,13021032422634946815,8680688281756631295,39321,43690,52428,0,39321,43690,52428,16711680,1095216660480,1095233372160,0,2273771520,149013890334720,149016164106240,168885272313856,168885946023936,248359347159040,248360020869120,16711680,71776119077928960,71776119077928960,16711680,2576941056,9765774319839477760,9765774320412131328,11067877559239704576,11067877561816645632,16276290531156951040,16276290531729604608,71777214277877760,1095216660480,71777214277877760,1095216660480,9765943199385255936,187647121162240,9765999493521604608,12297641732488560640,15191373375483150336,12297829379609722880,15191429669619499008]
def targetMasks : Fin 4 → Fin 11 → ℕ := ![![57825,53970,46260,30840,0,0,0,0,0,0,0],![0,16711680,16711680,0,0,2273771520,2273771520,2576941056,2576941056,3789619200,3789619200],![1095216660480,0,1095216660480,0,149013890334720,0,149013890334720,187647121162240,231799384965120,187647121162240,231799384965120],![71776119061217280,71776119061217280,71776119061217280,71776119061217280,11067877559239704576,12297641732488560640,14757170078986272768,0,11067877559239704576,12297641732488560640,14757170078986272768]]
def input (i : Fin 86) : Offsets := binaryVectorOfMask 64 (inputMasks i)
def target (i : Fin 4) (j : Fin 11) : Offsets := binaryVectorOfMask 64 (targetMasks i j)
def inputSource : Fin 86 → (Fin 4 × Fin 5) ⊕ (Fin 6 × Fin 11) := ![(.inl (0,0)),(.inl (0,1)),(.inl (0,2)),(.inl (0,3)),(.inl (0,4)),(.inl (1,0)),(.inl (1,1)),(.inl (1,2)),(.inl (1,3)),(.inl (1,4)),(.inl (2,0)),(.inl (2,1)),(.inl (2,2)),(.inl (2,3)),(.inl (2,4)),(.inl (3,0)),(.inl (3,1)),(.inl (3,2)),(.inl (3,3)),(.inl (3,4)),(.inr (0,0)),(.inr (0,1)),(.inr (0,2)),(.inr (0,3)),(.inr (0,4)),(.inr (0,5)),(.inr (0,6)),(.inr (0,7)),(.inr (0,8)),(.inr (0,9)),(.inr (0,10)),(.inr (1,0)),(.inr (1,1)),(.inr (1,2)),(.inr (1,3)),(.inr (1,4)),(.inr (1,5)),(.inr (1,6)),(.inr (1,7)),(.inr (1,8)),(.inr (1,9)),(.inr (1,10)),(.inr (2,0)),(.inr (2,1)),(.inr (2,2)),(.inr (2,3)),(.inr (2,4)),(.inr (2,5)),(.inr (2,6)),(.inr (2,7)),(.inr (2,8)),(.inr (2,9)),(.inr (2,10)),(.inr (3,0)),(.inr (3,1)),(.inr (3,2)),(.inr (3,3)),(.inr (3,4)),(.inr (3,5)),(.inr (3,6)),(.inr (3,7)),(.inr (3,8)),(.inr (3,9)),(.inr (3,10)),(.inr (4,0)),(.inr (4,1)),(.inr (4,2)),(.inr (4,3)),(.inr (4,4)),(.inr (4,5)),(.inr (4,6)),(.inr (4,7)),(.inr (4,8)),(.inr (4,9)),(.inr (4,10)),(.inr (5,0)),(.inr (5,1)),(.inr (5,2)),(.inr (5,3)),(.inr (5,4)),(.inr (5,5)),(.inr (5,6)),(.inr (5,7)),(.inr (5,8)),(.inr (5,9)),(.inr (5,10))]
def inputActual (k : Fin 86) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  match inputSource k with
  | .inl ij => (binaryRowFunctional (binaryVectorOfMask 16 (stateAnnihilator ij.2))).comp (squareMap ij.1)
  | .inr ij => (binaryRowFunctional (binaryVectorOfMask 16 (radicalAnnihilator ij.2))).comp (relatorMap ij.1)
def targetActual (i : Fin 4) (j : Fin 11) : Offsets →ₗ[ZMod 2] ZMod 2 :=
  (binaryRowFunctional (binaryVectorOfMask 16 (radicalAnnihilator j))).comp (squareMap i)
private theorem input_basis_slice_0 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨0+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨0+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_8 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨8+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨8+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_16 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨16+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨16+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_24 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨24+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨24+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_32 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨32+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨32+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_40 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨40+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨40+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_48 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨48+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨48+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_56 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨56+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨56+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_64 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨64+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨64+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_72 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨72+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨72+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_slice_80 : ∀ i : Fin 6, ∀ j : Fin 64,
    binaryRowFunctional (input ⟨80+i.val,by omega⟩) (Pi.single j 1) =
      inputActual ⟨80+i.val,by omega⟩ (Pi.single j 1) := by decide +kernel
private theorem input_basis_flat (i : Fin 86) (j : Fin 64) :
    binaryRowFunctional (input i) (Pi.single j 1) =
      inputActual i (Pi.single j 1) := by
  refine FiniteEightRowSlices.apply (fun i : Fin 86 =>
    binaryRowFunctional (input i) (Pi.single j 1) =
      inputActual i (Pi.single j 1)) ?_ i
  intro q r hr
  fin_cases q
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_0 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_8 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_16 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_24 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_32 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_40 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_48 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_56 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_64 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_72 ⟨r.val,hz⟩ j
  · have hz : r.val < 6 := by simp only [Fin.val_mk] at hr; omega
    exact input_basis_slice_80 ⟨r.val,hz⟩ j
theorem input_basis : ∀ i j, binaryRowFunctional (input i) (Pi.single j 1) =
    inputActual i (Pi.single j 1) := input_basis_flat
private theorem target_basis_slice_0 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (target (⟨(⟨0+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨0+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(⟨0+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨0+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1) := by decide +kernel
private theorem target_basis_slice_8 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (target (⟨(⟨8+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨8+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(⟨8+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨8+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1) := by decide +kernel
private theorem target_basis_slice_16 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (target (⟨(⟨16+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨16+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(⟨16+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨16+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1) := by decide +kernel
private theorem target_basis_slice_24 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (target (⟨(⟨24+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨24+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(⟨24+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨24+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1) := by decide +kernel
private theorem target_basis_slice_32 : ∀ i : Fin 8, ∀ j : Fin 64,
    binaryRowFunctional (target (⟨(⟨32+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨32+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(⟨32+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨32+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1) := by decide +kernel
private theorem target_basis_slice_40 : ∀ i : Fin 4, ∀ j : Fin 64,
    binaryRowFunctional (target (⟨(⟨40+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨40+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(⟨40+i.val,by omega⟩ : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(⟨40+i.val,by omega⟩ : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1) := by decide +kernel
private theorem target_basis_flat (i : Fin 44) (j : Fin 64) :
    binaryRowFunctional (target (⟨(i : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(i : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(i : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(i : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1) := by
  refine FiniteEightRowSlices.apply (fun i : Fin 44 =>
    binaryRowFunctional (target (⟨(i : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(i : Fin 44).val%11,by omega⟩ : Fin 11)) (Pi.single j 1) =
      targetActual (⟨(i : Fin 44).val/11,by omega⟩ : Fin 4) (⟨(i : Fin 44).val%11,by omega⟩ : Fin 11) (Pi.single j 1)) ?_ i
  intro q r hr
  fin_cases q
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact target_basis_slice_0 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact target_basis_slice_8 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact target_basis_slice_16 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact target_basis_slice_24 ⟨r.val,hz⟩ j
  · have hz : r.val < 8 := by simp only [Fin.val_mk] at hr; omega
    exact target_basis_slice_32 ⟨r.val,hz⟩ j
  · have hz : r.val < 4 := by simp only [Fin.val_mk] at hr; omega
    exact target_basis_slice_40 ⟨r.val,hz⟩ j
theorem target_basis : ∀ i j k, binaryRowFunctional (target i j) (Pi.single k 1) =
    targetActual i j (Pi.single k 1) := by
  intro i j k
  let t : Fin 44 := ⟨i.val*11+j.val,by omega⟩
  have hi : (⟨t.val/11,by omega⟩ : Fin 4) = i := Fin.ext (by dsimp [t]; omega)
  have hj : (⟨t.val%11,by omega⟩ : Fin 11) = j := Fin.ext (by dsimp [t]; omega)
  simpa only [hi,hj] using target_basis_flat t k

end SymmetricSubgroupAsymptotics.BinaryElementary16PhiZeroOuterCarries
