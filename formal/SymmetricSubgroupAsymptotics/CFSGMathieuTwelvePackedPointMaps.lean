import SymmetricSubgroupAsymptotics.CFSGMathieuTwelveTransversalSeedImages
import SymmetricSubgroupAsymptotics.SignedPermutationWordPointEncoding

/-! Selected 50-row M12 seed certificate, DATA receipt SHA409f72d0f8595c3a15aebd6460357a93088709e010206943c01465bfc3e64739.
The actual original Word.toM12 transversals remain the semantic inputs.
Every supplied table is independently bound by a whole-point kernel proof.
No incidence/capacity or other-prefix assertion; no resource cap is raised.
Original certificate data: Kenta, Apache-2.0, revision7f09e33. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePackedPointMaps
open CFSG.Certificates.Mathieu12 CFSGMathieuTwelveFiveTransversalCover
open CFSGMathieuTwelveRecoveredPairRelations
open CFSGMathieuTwelveTransversalSeedImages

def packedGet (row p : ℕ) : ℕ := row / 2 ^ (5 * p) % 32

private def packedFirstRow (i : ℕ) : ℕ :=
  match i with
  | 0 => 407901468851537952
  | 1 => 396678789134945345
  | 2 => 397453980300644450
  | 3 => 398604104931415171
  | 4 => 405405439080038628
  | 5 => 11647337236603109
  | 6 => 399987010344027142
  | 7 => 401104387831956487
  | 8 => 404414811075520808
  | 9 => 405577030334185801
  | 10 => 406739249592861706
  | 11 => 1341517004510539
  | _ => 407901468851537952

def packedFirst (i p : ℕ) : ℕ := packedGet (packedFirstRow i) p

private def packedFirstInverseRow (i : ℕ) : ℕ :=
  match i with
  | 0 => 407901468851537952
  | 1 => 406739249592861706
  | 2 => 405577030334185801
  | 3 => 404414811075520808
  | 4 => 405510922296337506
  | 5 => 335661150633102603
  | 6 => 405509887148497985
  | 7 => 404348703049195585
  | 8 => 398604104931415171
  | 9 => 397453980300644450
  | 10 => 396678789134945345
  | 11 => 1341517004510539
  | _ => 407901468851537952

def packedFirstInverse (i p : ℕ) : ℕ := packedGet (packedFirstInverseRow i) p

theorem first_point_eq : ∀ (i p : Fin 12),
    packedFirst i.val p.val = (firstSeed i p).val ∧
    packedFirstInverse i.val p.val = ((firstSeed i).symm p).val := by
  decide +kernel

private def packedSecondRow (i : ℕ) : ℕ :=
  match i with
  | 1 => 407901468851537952
  | 2 => 403220947577087040
  | 3 => 407613364727094368
  | 4 => 403148377731408000
  | 5 => 407790412940583072
  | 6 => 407754137379541184
  | 7 => 336927853856856288
  | 8 => 120724491579984128
  | 9 => 407758361547809056
  | 10 => 48564507403984192
  | 11 => 366025498056336736
  | _ => 407901468851537952

def packedSecond (i p : ℕ) : ℕ := packedGet (packedSecondRow i) p

private def packedSecondInverseRow (i : ℕ) : ℕ :=
  match i with
  | 1 => 407901468851537952
  | 2 => 404272019594740896
  | 3 => 407758361547809056
  | 4 => 404305967142053056
  | 5 => 407754137379541184
  | 6 => 407790412940583072
  | 7 => 366314430035894400
  | 8 => 366165177808554080
  | 9 => 407613364727094368
  | 10 => 361699818526053728
  | 11 => 48491937752457408
  | _ => 407901468851537952

def packedSecondInverse (i p : ℕ) : ℕ := packedGet (packedSecondInverseRow i) p

theorem second_point_eq : ∀ (i p : Fin 12),
    packedSecond i.val p.val = (secondSeed i p).val ∧
    packedSecondInverse i.val p.val = ((secondSeed i).symm p).val := by
  decide +kernel

private def packedThirdRow (i : ℕ) : ℕ :=
  match i with
  | 2 => 407901468851537952
  | 3 => 192818367353261088
  | 4 => 398682136869343264
  | 5 => 403391170088277024
  | 6 => 404347679700981792
  | 7 => 403186861747641376
  | 8 => 363746112642064416
  | 9 => 120755108153992224
  | 10 => 398753498955655200
  | 11 => 118468190578846752
  | _ => 407901468851537952

def packedThird (i p : ℕ) : ℕ := packedGet (packedThirdRow i) p

private def packedThirdInverseRow (i : ℕ) : ℕ :=
  match i with
  | 2 => 407901468851537952
  | 3 => 366173934405621792
  | 4 => 403322035132213280
  | 5 => 401140541690126368
  | 6 => 403186861747641376
  | 7 => 404347679700981792
  | 8 => 120755108153992224
  | 9 => 363746112642064416
  | 10 => 398753498955655200
  | 11 => 76918851805487136
  | _ => 407901468851537952

def packedThirdInverse (i p : ℕ) : ℕ := packedGet (packedThirdInverseRow i) p

theorem third_point_eq : ∀ (i p : Fin 12),
    packedThird i.val p.val = (thirdSeed i p).val ∧
    packedThirdInverse i.val p.val = ((thirdSeed i).symm p).val := by
  decide +kernel

private def packedFourthRow (i : ℕ) : ℕ :=
  match i with
  | 3 => 407901468851537952
  | 4 => 402199268511844384
  | 5 => 404413849247320096
  | 6 => 401004338648123424
  | 7 => 221031804622309408
  | 8 => 190425633428604960
  | 9 => 263643383958112288
  | 10 => 406734819337504800
  | 11 => 255729161709389856
  | _ => 407901468851537952

def packedFourth (i p : ℕ) : ℕ := packedGet (packedFourthRow i) p

private def packedFourthInverseRow (i : ℕ) : ℕ :=
  match i with
  | 3 => 407901468851537952
  | 4 => 403218719862655008
  | 5 => 401004338648123424
  | 6 => 404413849247320096
  | 7 => 190425633428604960
  | 8 => 221031804622309408
  | 9 => 227545417734293536
  | 10 => 400056416948455456
  | 11 => 116152790821439520
  | _ => 407901468851537952

def packedFourthInverse (i p : ℕ) : ℕ := packedGet (packedFourthInverseRow i) p

theorem fourth_point_eq : ∀ (i p : Fin 12),
    packedFourth i.val p.val = (fourthSeed i p).val ∧
    packedFourthInverse i.val p.val = ((fourthSeed i).symm p).val := by
  decide +kernel

private def packedFifthRow (i : ℕ) : ℕ :=
  match i with
  | 4 => 407901468851537952
  | 5 => 256999068546467872
  | 6 => 330283676894070816
  | 7 => 370601604383082528
  | 8 => 192887470126368800
  | 9 => 153339346774231072
  | 10 => 295242345272674336
  | 11 => 224205995808753696
  | _ => 407901468851537952

def packedFifth (i p : ℕ) : ℕ := packedGet (packedFifthRow i) p

private def packedFifthInverseRow (i : ℕ) : ℕ :=
  match i with
  | 4 => 407901468851537952
  | 5 => 295242345272674336
  | 6 => 330283676894070816
  | 7 => 192887470126368800
  | 8 => 370601604383082528
  | 9 => 224205995808753696
  | 10 => 256999068546467872
  | 11 => 153339346774231072
  | _ => 407901468851537952

def packedFifthInverse (i p : ℕ) : ℕ := packedGet (packedFifthInverseRow i) p

theorem fifth_point_eq : ∀ (i p : Fin 12),
    packedFifth i.val p.val = (fifthSeed i p).val ∧
    packedFifthInverse i.val p.val = ((fifthSeed i).symm p).val := by
  decide +kernel

def packedFixed (p : ℕ) : ℕ := packedGet 324511038680927590 p

def packedFixedInverse (p : ℕ) : ℕ := packedGet 39800431412583594 p

theorem fixed_point_eq : ∀ p : Fin 12,
    packedFixed p.val = (fixedSeed p).val ∧
    packedFixedInverse p.val = (fixedSeed.symm p).val := by
  decide +kernel

end SymmetricSubgroupAsymptotics.CFSGMathieuTwelvePackedPointMaps
