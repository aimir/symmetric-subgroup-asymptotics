import SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoRawPointMaps

/-! The SAME checked82 point-map rows, represented by110-bit Nat literals.
Point lookup is division by2^(5*p) followed by mod32, replacing the large
22-branch point matcher. Every packed map is independently bound to the
passed raw map at each valid point; the existing typed shadow is retained.
No fresh seeds, candidate evaluation or desired capacity premise occurs. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPointMaps
open SignedPermutationWordPointEvaluation SignedPermutationWordPointEncoding
open CFSGMathieuTwentyTwoFiveTransversalCover
open CFSGMathieuTwentyTwoTransversalSeedImagesFirst
open CFSGMathieuTwentyTwoTransversalSeedImagesRemaining
open CFSGMathieuTwentyTwoPrefixOneOneExclusion
open CFSGMathieuTwentyTwoScalarRelationWords

def packedGet (row p : ℕ) : ℕ := row / 2 ^ (5 * p) % 32

private def packedFirstRow (i : ℕ) : ℕ :=
  match i with
  | 0 => 877989843404692497019985071278112
  | 1 => 223526180841172185842880330610785
  | 2 => 179062464989240812031737117421858
  | 3 => 825926409378061847653791457413379
  | 4 => 746783037440329414311685381202596
  | 5 => 52515320697765750364623547777349
  | 6 => 94342194973992582681534129526374
  | 7 => 335969903430606153324400644296071
  | 8 => 388078925781516786947570394372488
  | 9 => 700380695877835020777109127041097
  | 10 => 554284680122836337513557498268202
  | 11 => 410245335626782667512631717699019
  | 12 => 829652028974930741351483984943340
  | 13 => 698817750070807219225715386363277
  | 14 => 624422338188318487707690933441966
  | 15 => 592362403955547003349270731043407
  | 16 => 772197689174406470280764739328080
  | 17 => 493839451660327106546228303804433
  | 18 => 173244099323633572562125548914322
  | 19 => 710376236501521657595892975342835
  | 20 => 731020432719488295687466491690452
  | 21 => 14315932998198660497763527643765
  | _ => 877989843404692497019985071278112

def packedFirst (i p : ℕ) : ℕ := packedGet (packedFirstRow i) p

private def packedFirstInverseRow (i : ℕ) : ℕ :=
  match i with
  | 0 => 877989843404692497019985071278112
  | 1 => 493839451660327106546228303804433
  | 2 => 288245848444341823664021228945576
  | 3 => 554284680122836337513557498268202
  | 4 => 52515320697765750364623547777349
  | 5 => 746783037440329414311685381202596
  | 6 => 100204518705835986088676985099633
  | 7 => 455657467647922833893535881710186
  | 8 => 698817750070807219225715386363277
  | 9 => 654513351908572766668196118332913
  | 10 => 825926409378061847653791457413379
  | 11 => 592362403955547003349270731043407
  | 12 => 513538973432194212570117476464934
  | 13 => 388078925781516786947570394372488
  | 14 => 104407016249747569894382637331716
  | 15 => 410245335626782667512631717699019
  | 16 => 173244099323633572562125548914322
  | 17 => 223526180841172185842880330610785
  | 18 => 772197689174406470280764739328080
  | 19 => 499466315074243665590948102016235
  | 20 => 771431713195527170396530588070132
  | 21 => 2578790125363527406560281504053
  | _ => 877989843404692497019985071278112

def packedFirstInverse (i p : ℕ) : ℕ := packedGet (packedFirstInverseRow i) p

theorem first_point_eq : ∀ (i p : Fin 22),
    packedFirst i.val p.val = (firstSeed i p).val ∧
      packedFirstInverse i.val p.val = ((firstSeed i).symm p).val := by
  have h : ∀ (i p : Fin 22),
      packedFirst i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawFirst i.val p.val ∧
      packedFirstInverse i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawFirstInverse i.val p.val := by
    decide +kernel
  intro i p
  exact ⟨(h i p).1.trans (CFSGMathieuTwentyTwoRawPointMaps.first_point_eq i p).1,
    (h i p).2.trans (CFSGMathieuTwentyTwoRawPointMaps.first_point_eq i p).2⟩

private def packedSecondRow (i : ℕ) : ℕ :=
  match i with
  | 1 => 877989843404692497019985071278112
  | 2 => 676268638973433546256174479167552
  | 3 => 545940847439553866877299422810208
  | 4 => 368195771786870396630679206403200
  | 5 => 773871466362055922975040914630816
  | 6 => 465906367307933332466464237128896
  | 7 => 667404948811849360177172041795808
  | 8 => 508606974981195678850499308764416
  | 9 => 575646577546810268343873849857312
  | 10 => 740836610946216721896981644152128
  | 11 => 813166043033288935884985444343136
  | 12 => 294358819478634701663044923603328
  | 13 => 715692335054229275075989777623456
  | 14 => 541349021969774516002925810729408
  | 15 => 814474627894782837879240843888096
  | 16 => 343636539723230365330783289525760
  | 17 => 546938630171743997125045040261664
  | 18 => 423564441383783060989339218972224
  | 19 => 583801445725759377225065789763168
  | 20 => 741791095838717158558297077894784
  | 21 => 407675340779348347856304821644960
  | _ => 877989843404692497019985071278112

def packedSecond (i p : ℕ) : ℕ := packedGet (packedSecondRow i) p

private def packedSecondInverseRow (i : ℕ) : ℕ :=
  match i with
  | 1 => 877989843404692497019985071278112
  | 2 => 814474627894782837879240843888096
  | 3 => 773871466362055922975040914630816
  | 4 => 263852542170362578102512585593312
  | 5 => 545940847439553866877299422810208
  | 6 => 575646577546810268343873849857312
  | 7 => 735732782391342923426196772522272
  | 8 => 423564441383783060989339218972224
  | 9 => 465906367307933332466464237128896
  | 10 => 546938630171743997125045040261664
  | 11 => 595062306991784384485668715500160
  | 12 => 739647012996704891343847677106304
  | 13 => 715692342636863937076039754682528
  | 14 => 131184895390263245136206841982560
  | 15 => 676268638973433546256174479167552
  | 16 => 372152089833463638519809460817312
  | 17 => 740836610946216721896981644152128
  | 18 => 508606974981195678850499308764416
  | 19 => 655428106343483542933261365913120
  | 20 => 163632283145295948001042599429600
  | 21 => 54014014317303738510097543305856
  | _ => 877989843404692497019985071278112

def packedSecondInverse (i p : ℕ) : ℕ := packedGet (packedSecondInverseRow i) p

theorem second_point_eq : ∀ (i p : Fin 22),
    packedSecond i.val p.val = (secondSeed i p).val ∧
      packedSecondInverse i.val p.val = ((secondSeed i).symm p).val := by
  have h : ∀ (i p : Fin 22),
      packedSecond i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawSecond i.val p.val ∧
      packedSecondInverse i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawSecondInverse i.val p.val := by
    decide +kernel
  intro i p
  exact ⟨(h i p).1.trans (CFSGMathieuTwentyTwoRawPointMaps.second_point_eq i p).1,
    (h i p).2.trans (CFSGMathieuTwentyTwoRawPointMaps.second_point_eq i p).2⟩

private def packedThirdRow (i : ℕ) : ℕ :=
  match i with
  | 2 => 877989843404692497019985071278112
  | 3 => 175745723438609019108590143736864
  | 4 => 90809721967615181211069563637792
  | 5 => 776091131649065645904567187346464
  | 6 => 388461962826730428911488260872224
  | 7 => 506548054843082390905996738763808
  | 8 => 750932127988009593365999060885536
  | 9 => 825877125136339505504627173336096
  | 10 => 776326173912053609838984975362080
  | 11 => 534181167460970119033313367960608
  | 12 => 286950178787114183991566191341600
  | 13 => 455723663880358887098190970565664
  | 14 => 287301560906745740897587314440224
  | 15 => 253100868506409014852687564684320
  | 16 => 798167467968967898531030454419488
  | 17 => 573320143044457146747695408759840
  | 18 => 539512999767879881545592860952608
  | 19 => 658371268854607996239943652690976
  | 20 => 389692559601630238080053386891296
  | 21 => 94065387889244447010067431183392
  | _ => 877989843404692497019985071278112

def packedThird (i p : ℕ) : ℕ := packedGet (packedThirdRow i) p

private def packedThirdInverseRow (i : ℕ) : ℕ :=
  match i with
  | 2 => 877989843404692497019985071278112
  | 3 => 186710341338000818076731885816864
  | 4 => 186638398952252281732850652402720
  | 5 => 625801597007299970291230860059680
  | 6 => 573320143044457146747695408759840
  | 7 => 539512999767879881545592860952608
  | 8 => 585007778127638730393643256098848
  | 9 => 473241443485255009900390419548192
  | 10 => 253100868506409014852687564684320
  | 11 => 509838807817971097847793750423584
  | 12 => 631579813911946725999671461072928
  | 13 => 346706524593902742798527406458912
  | 14 => 389692559601630238080053386891296
  | 15 => 776326173912053609838984975362080
  | 16 => 836236584864156911087090717113376
  | 17 => 388461962826730428911488260872224
  | 18 => 506548054843082390905996738763808
  | 19 => 590810971636576743448999552762912
  | 20 => 287301560906745740897587314440224
  | 21 => 87842453296216185690443647964192
  | _ => 877989843404692497019985071278112

def packedThirdInverse (i p : ℕ) : ℕ := packedGet (packedThirdInverseRow i) p

theorem third_point_eq : ∀ (i p : Fin 22),
    packedThird i.val p.val = (thirdSeed i p).val ∧
      packedThirdInverse i.val p.val = ((thirdSeed i).symm p).val := by
  have h : ∀ (i p : Fin 22),
      packedThird i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawThird i.val p.val ∧
      packedThirdInverse i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawThirdInverse i.val p.val := by
    decide +kernel
  intro i p
  exact ⟨(h i p).1.trans (CFSGMathieuTwentyTwoRawPointMaps.third_point_eq i p).1,
    (h i p).2.trans (CFSGMathieuTwentyTwoRawPointMaps.third_point_eq i p).2⟩

private def packedFourthRow (i : ℕ) : ℕ :=
  match i with
  | 5 => 877989843404692497019985071278112
  | 6 => 145119041047889804778953577203744
  | 7 => 170361073919172476746245007378464
  | 8 => 147577514939237050468141437683744
  | 9 => 872755683167773184449978174638112
  | 10 => 871526446222097325636405614970912
  | 11 => 175278012323551224918069667858464
  | 12 => 142660567156533615213851199014944
  | 13 => 133441911964143962815366238963744
  | 14 => 134671146565238649858322404083744
  | 15 => 864909524361500522917013879883808
  | 16 => 137129620456585895547510264563744
  | 17 => 188179583675341611121263123269664
  | 18 => 129754198782535214604032165414944
  | 19 => 185725906806221384448054165932064
  | 20 => 132212672673882460293220025894944
  | _ => 877989843404692497019985071278112

def packedFourth (i p : ℕ) : ℕ := packedGet (packedFourthRow i) p

private def packedFourthInverseRow (i : ℕ) : ℕ :=
  match i with
  | 5 => 877989843404692497019985071278112
  | 6 => 175278012323551224918069667858464
  | 7 => 133441911964143962815366238963744
  | 8 => 188179583675341611121263123269664
  | 9 => 872755683167773184449978174638112
  | 10 => 871526446222097325636405614970912
  | 11 => 145119041047889804778953577203744
  | 12 => 171506210729062875276952240556064
  | 13 => 170361073919172476746245007378464
  | 14 => 177731689192671451591278625196064
  | 15 => 864909524361500522917013879883808
  | 16 => 185725906806221384448054165932064
  | 17 => 147577514939237050468141437683744
  | 18 => 181954105211733034806936738629664
  | 19 => 137129620456585895547510264563744
  | 20 => 169052533859942648603743283218464
  | _ => 877989843404692497019985071278112

def packedFourthInverse (i p : ℕ) : ℕ := packedGet (packedFourthInverseRow i) p

theorem fourth_point_eq : ∀ (i p : Fin 22),
    packedFourth i.val p.val = (fourthSeed i p).val ∧
      packedFourthInverse i.val p.val = ((fourthSeed i).symm p).val := by
  have h : ∀ (i p : Fin 22),
      packedFourth i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawFourth i.val p.val ∧
      packedFourthInverse i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawFourthInverse i.val p.val := by
    decide +kernel
  intro i p
  exact ⟨(h i p).1.trans (CFSGMathieuTwentyTwoRawPointMaps.fourth_point_eq i p).1,
    (h i p).2.trans (CFSGMathieuTwentyTwoRawPointMaps.fourth_point_eq i p).2⟩

private def packedFifthRow (i : ℕ) : ℕ :=
  match i with
  | 3 => 877989843404692497019985071278112
  | 4 => 143889806446795117735997412083744
  | 21 => 172814750788292703419453964716064
  | _ => 877989843404692497019985071278112

def packedFifth (i p : ℕ) : ℕ := packedGet (packedFifthRow i) p

private def packedFifthInverseRow (i : ℕ) : ℕ :=
  match i with
  | 3 => 877989843404692497019985071278112
  | 4 => 172814750788292703419453964716064
  | 21 => 143889806446795117735997412083744
  | _ => 877989843404692497019985071278112

def packedFifthInverse (i p : ℕ) : ℕ := packedGet (packedFifthInverseRow i) p

theorem fifth_point_eq : ∀ (i p : Fin 22),
    packedFifth i.val p.val = (fifthSeed i p).val ∧
      packedFifthInverse i.val p.val = ((fifthSeed i).symm p).val := by
  have h : ∀ (i p : Fin 22),
      packedFifth i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawFifth i.val p.val ∧
      packedFifthInverse i.val p.val = CFSGMathieuTwentyTwoRawPointMaps.rawFifthInverse i.val p.val := by
    decide +kernel
  intro i p
  exact ⟨(h i p).1.trans (CFSGMathieuTwentyTwoRawPointMaps.fifth_point_eq i p).1,
    (h i p).2.trans (CFSGMathieuTwentyTwoRawPointMaps.fifth_point_eq i p).2⟩

def packedX (p : ℕ) : ℕ := packedGet 812667300456035749144480081691182 p

def packedXInverse (p : ℕ) : ℕ := packedGet 432999280896253650370267396329094 p

theorem x_point_eq : ∀ p : Fin 22,
    packedX p.val = (xSeed p).val ∧ packedXInverse p.val = (xSeed.symm p).val := by
  have h : ∀ p : Fin 22,
      packedX p.val = CFSGMathieuTwentyTwoRawPointMaps.rawX p.val ∧
      packedXInverse p.val = CFSGMathieuTwentyTwoRawPointMaps.rawXInverse p.val := by
    decide +kernel
  intro p
  exact ⟨(h p).1.trans (CFSGMathieuTwentyTwoRawPointMaps.x_point_eq p).1,
    (h p).2.trans (CFSGMathieuTwentyTwoRawPointMaps.x_point_eq p).2⟩

def packedCandidateForward (i j k l m p : ℕ) : ℕ :=
  packedFirst i (packedSecond j (packedThird k (packedFourth l (packedFifth m p))))

def packedCandidateInverse (i j k l m p : ℕ) : ℕ :=
  packedFifthInverse m (packedFourthInverse l
    (packedThirdInverse k (packedSecondInverse j (packedFirstInverse i p))))

theorem candidateForward_point_eq (c : Code) (p : Fin 22) :
    packedCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val = (candidateForward c p).val := by
  dsimp only [packedCandidateForward, candidateForward]
  rw [(fifth_point_eq c.2.2.2.val p).1,
    (fourth_point_eq c.2.2.1.val (fifthSeed c.2.2.2.val p)).1,
    (third_point_eq c.2.1.val (fourthSeed c.2.2.1.val (fifthSeed c.2.2.2.val p))).1,
    (second_point_eq c.1.2.val (thirdSeed c.2.1.val
      (fourthSeed c.2.2.1.val (fifthSeed c.2.2.2.val p)))).1,
    (first_point_eq c.1.1 (secondSeed c.1.2.val (thirdSeed c.2.1.val
      (fourthSeed c.2.2.1.val (fifthSeed c.2.2.2.val p))))).1]

theorem candidateInverse_point_eq (c : Code) (p : Fin 22) :
    packedCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val = (candidateInverse c p).val := by
  dsimp only [packedCandidateInverse, candidateInverse]
  rw [(first_point_eq c.1.1 p).2,
    (second_point_eq c.1.2.val ((firstSeed c.1.1).symm p)).2,
    (third_point_eq c.2.1.val ((secondSeed c.1.2.val).symm ((firstSeed c.1.1).symm p))).2,
    (fourth_point_eq c.2.2.1.val ((thirdSeed c.2.1.val).symm
      ((secondSeed c.1.2.val).symm ((firstSeed c.1.1).symm p)))).2,
    (fifth_point_eq c.2.2.2.val ((fourthSeed c.2.2.1.val).symm ((thirdSeed c.2.1.val).symm
      ((secondSeed c.1.2.val).symm ((firstSeed c.1.1).symm p))))).2]

def packedRelationWord (r : ℕ) : List Letter :=
  match r with
  | 0 => powerWord [Letter.second] 11
  | 1 => powerWord recoverAWord 5
  | 2 => powerWord recoverBWord 8
  | 3 => powerWord recoverAWord 3 ++ powerWord recoverBWord 2 ++ [Letter.firstInv]
  | _ => recoverAWord ++ [Letter.first] ++ inverseWord recoverAWord ++ [Letter.secondInv]

theorem packedRelationWord_eq (r : Fin 5) : packedRelationWord r.val = relationWord r := by
  fin_cases r <;> rfl

def packedScalarRelation (r i j k l m p : ℕ) : ℕ :=
  applyWord packedX packedXInverse (packedCandidateForward i j k l m)
    (packedCandidateInverse i j k l m) (packedRelationWord r) p

theorem packedScalarRelation_eq (r : Fin 5) (c : Code) (p : Fin 22) :
    packedScalarRelation r.val c.1.1.val c.1.2.val.val c.2.1.val.val
      c.2.2.1.val.val c.2.2.2.val.val p.val = (scalarRelation r c p).val := by
  unfold packedScalarRelation scalarRelation
  rw [packedRelationWord_eq]
  exact applyWord_encoding (fun p : Fin 22 => p.val)
    xSeed xSeed.symm (candidateForward c) (candidateInverse c)
    packedX packedXInverse
    (packedCandidateForward c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (packedCandidateInverse c.1.1.val c.1.2.val.val c.2.1.val.val c.2.2.1.val.val c.2.2.2.val.val)
    (fun p => (x_point_eq p).1) (fun p => (x_point_eq p).2)
    (candidateForward_point_eq c) (candidateInverse_point_eq c) (relationWord r) p

end SymmetricSubgroupAsymptotics.CFSGMathieuTwentyTwoPackedPointMaps
