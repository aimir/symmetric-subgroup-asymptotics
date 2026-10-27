import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! One shared reduced cache in the EXACT selected Suz positive DAG.
Digit and pack bindings are kernel obligations, not trusted metadata. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheC2
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def lowColumnCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 4
  | 2 => 16
  | 3 => 64
  | 4 => 256
  | 5 => 1024
  | 6 => 4096
  | 7 => 16384
  | 8 => 65536
  | 9 => 262144
  | 10 => 1048576
  | 11 => 4194304
  | 12 => 16777216
  | 13 => 67108864
  | 14 => 268435456
  | 15 => 1073741824
  | 16 => 4294967296
  | 17 => 17179869184
  | 18 => 68719476736
  | 19 => 274877906944
  | 20 => 1099511627776
  | 21 => 4398046511104
  | 22 => 17592186044416
  | 23 => 70368744177664
  | 24 => 281474976710656
  | 25 => 1125899906842624
  | 26 => 4503599627370496
  | 27 => 18014398509481984
  | 28 => 72057594037927936
  | 29 => 288230376151711744
  | 30 => 1152921504606846976
  | 31 => 4611686018427387904
  | 32 => 18446744073709551616
  | 33 => 73786976294838206464
  | 34 => 295147905179352825856
  | 35 => 1180591620717411303424
  | 36 => 4722366482869645213696
  | 37 => 18889465931478580854784
  | 38 => 75557863725914323419136
  | 39 => 302231454903657293676544
  | 40 => 1208925819614629174706176
  | 41 => 4835703278458516698824704
  | 42 => 19342813113834066795298816
  | 43 => 77371252455336267181195264
  | 44 => 309485009821345068724781056
  | 45 => 1237940039285380274899124224
  | 46 => 4951760157141521099596496896
  | 47 => 19807040628566084398385987584
  | 48 => 79228162514264337593543950336
  | 49 => 316912650057057350374175801344
  | 50 => 1267650600228229401496703205376
  | 51 => 5070602400912917605986812821504
  | 52 => 20282409603651670423947251286016
  | 53 => 81129638414606681695789005144064
  | 54 => 324518553658426726783156020576256
  | 55 => 1298074214633706907132624082305024
  | 56 => 5192296858534827628530496329220096
  | 57 => 20769187434139310514121985316880384
  | 58 => 83076749736557242056487941267521536
  | 59 => 332306998946228968225951765070086144
  | 60 => 1329227995784915872903807060280344576
  | 61 => 5316911983139663491615228241121378304
  | 62 => 21267647932558653966460912964485513216
  | 63 => 85070591730234615865843651857942052864
  | _ => 0

def rowCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 512
  | 2 => 262144
  | 3 => 134217728
  | 4 => 68719476736
  | 5 => 35184372088832
  | 6 => 18014398509481984
  | 7 => 9223372036854775808
  | 8 => 4722366482869645213696
  | 9 => 2417851639229258349412352
  | 10 => 1237940039285380274899124224
  | 11 => 633825300114114700748351602688
  | 12 => 324518553658426726783156020576256
  | 13 => 166153499473114484112975882535043072
  | 14 => 85070591730234615865843651857942052864
  | 15 => 43556142965880123323311949751266331066368
  | 16 => 22300745198530623141535718272648361505980416
  | 17 => 11417981541647679048466287755595961091061972992
  | 18 => 5846006549323611672814739330865132078623730171904
  | 19 => 2993155353253689176481146537402947624255349848014848
  | 20 => 1532495540865888858358347027150309183618739122183602176
  | 21 => 784637716923335095479473677900958302012794430558004314112
  | 22 => 401734511064747568885490523085290650630550748445698208825344
  | 23 => 205688069665150755269371147819668813122841983204197482918576128
  | 24 => 105312291668557186697918027683670432318895095400549111254310977536
  | 25 => 53919893334301279589334030174039261347274288845081144962207220498432
  | 26 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | 27 => 14134776518227074636666380005943348126619871175004951664972849610340958208
  | 28 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | 29 => 3705346855594118253554271520278013051304639509300498049262642688253220148477952
  | 30 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | 31 => 971334446112864535459730953411759453321203419526069760625906204869452142602604249088
  | 32 => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
  | 33 => 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672
  | 34 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 35 => 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768
  | 36 => 34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216
  | 37 => 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592
  | 38 => 8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104
  | 39 => 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248
  | 40 => 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976
  | 41 => 1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712
  | 42 => 615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544
  | 43 => 315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528
  | 44 => 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336
  | 45 => 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032
  | 46 => 42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384
  | 47 => 21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608
  | 48 => 11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296
  | 49 => 5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552
  | 50 => 2907354897182427562197295231552018137414565442749272241125960796722557152453591693304764202855054262243050086425064711734138406514458624
  | 51 => 1488565707357402911845015158554633286356257506687627387456491927921949262056238946972039271861787782268441644249633132407878864135402815488
  | 52 => 762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529856
  | 53 => 390218568789499028922699653724145788218574767833121393857394619953171467352470702515038262882936496394978366390175827861930996959911035663286272
  | 54 => 199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264
  | 55 => 102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168
  | 56 => 52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016
  | 57 => 26815615859885194199148049996411692254958731641184786755447122887443528060147093953603748596333806855380063716372972101707507765623893139892867298012168192
  | 58 => 13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782961716074243975999433287625148056582230114304
  | 59 => 7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970101818523648
  | 60 => 3599131035634557106248430806148785487095757694641533306480604458089470064537190296255232548883112685719936728506816716098566612844395439751206812144692131084107776
  | 61 => 1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312
  | 62 => 943490606205385338060388645247067222729230305104110107094051575061406040598037213021531681294414691885367093757690961224942646157481198158140358562858174010912348831744
  | 63 => 483067190377157293086918986366498418037365916213304374832154406431439892786195053067024220822740322245307952003937772147170634832630373456967863584183385093587122601852928
  | _ => 0

def columnCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 483067190377157293086918986366498418037365916213304374832154406431439892786195053067024220822740322245307952003937772147170634832630373456967863584183385093587122601852928
  | 1 => 943490606205385338060388645247067222729230305104110107094051575061406040598037213021531681294414691885367093757690961224942646157481198158140358562858174010912348831744
  | 2 => 1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312
  | 3 => 3599131035634557106248430806148785487095757694641533306480604458089470064537190296255232548883112685719936728506816716098566612844395439751206812144692131084107776
  | 4 => 7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876398630012915711709843264075804970101818523648
  | 5 => 13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782961716074243975999433287625148056582230114304
  | 6 => 26815615859885194199148049996411692254958731641184786755447122887443528060147093953603748596333806855380063716372972101707507765623893139892867298012168192
  | 7 => 52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186946040961136147476104734166288853256441430016
  | 8 => 102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965208878986252219038039267058918532916516487168
  | 9 => 199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264
  | 10 => 390218568789499028922699653724145788218574767833121393857394619953171467352470702515038262882936496394978366390175827861930996959911035663286272
  | 11 => 762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529856
  | 12 => 1488565707357402911845015158554633286356257506687627387456491927921949262056238946972039271861787782268441644249633132407878864135402815488
  | 13 => 2907354897182427562197295231552018137414565442749272241125960796722557152453591693304764202855054262243050086425064711734138406514458624
  | 14 => 5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552
  | 15 => 11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296
  | 16 => 21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608
  | 17 => 42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384
  | 18 => 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032
  | 19 => 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336
  | 20 => 315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528
  | 21 => 615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544
  | 22 => 1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712
  | 23 => 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976
  | 24 => 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248
  | 25 => 8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104
  | 26 => 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592
  | 27 => 34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216
  | 28 => 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768
  | 29 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 30 => 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672
  | 31 => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
  | 32 => 971334446112864535459730953411759453321203419526069760625906204869452142602604249088
  | 33 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | 34 => 3705346855594118253554271520278013051304639509300498049262642688253220148477952
  | 35 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | 36 => 14134776518227074636666380005943348126619871175004951664972849610340958208
  | 37 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | 38 => 53919893334301279589334030174039261347274288845081144962207220498432
  | 39 => 105312291668557186697918027683670432318895095400549111254310977536
  | 40 => 205688069665150755269371147819668813122841983204197482918576128
  | 41 => 401734511064747568885490523085290650630550748445698208825344
  | 42 => 784637716923335095479473677900958302012794430558004314112
  | 43 => 1532495540865888858358347027150309183618739122183602176
  | 44 => 2993155353253689176481146537402947624255349848014848
  | 45 => 5846006549323611672814739330865132078623730171904
  | 46 => 11417981541647679048466287755595961091061972992
  | 47 => 22300745198530623141535718272648361505980416
  | 48 => 43556142965880123323311949751266331066368
  | 49 => 85070591730234615865843651857942052864
  | 50 => 166153499473114484112975882535043072
  | 51 => 324518553658426726783156020576256
  | 52 => 633825300114114700748351602688
  | 53 => 1237940039285380274899124224
  | 54 => 2417851639229258349412352
  | 55 => 4722366482869645213696
  | 56 => 9223372036854775808
  | 57 => 18014398509481984
  | 58 => 35184372088832
  | 59 => 68719476736
  | 60 => 134217728
  | 61 => 262144
  | 62 => 512
  | 63 => 1
  | _ => 0

def digit (i j : Fin 64) : ℕ := packedDigit 2 (lowColumnCode j) i.val

private theorem bound_row_00 : ∀ j : Fin 64,digit 0 j<3 := by
  decide +kernel

private theorem bound_row_01 : ∀ j : Fin 64,digit 1 j<3 := by
  decide +kernel

private theorem bound_row_02 : ∀ j : Fin 64,digit 2 j<3 := by
  decide +kernel

private theorem bound_row_03 : ∀ j : Fin 64,digit 3 j<3 := by
  decide +kernel

private theorem bound_row_04 : ∀ j : Fin 64,digit 4 j<3 := by
  decide +kernel

private theorem bound_row_05 : ∀ j : Fin 64,digit 5 j<3 := by
  decide +kernel

private theorem bound_row_06 : ∀ j : Fin 64,digit 6 j<3 := by
  decide +kernel

private theorem bound_row_07 : ∀ j : Fin 64,digit 7 j<3 := by
  decide +kernel

private theorem bound_row_08 : ∀ j : Fin 64,digit 8 j<3 := by
  decide +kernel

private theorem bound_row_09 : ∀ j : Fin 64,digit 9 j<3 := by
  decide +kernel

private theorem bound_row_10 : ∀ j : Fin 64,digit 10 j<3 := by
  decide +kernel

private theorem bound_row_11 : ∀ j : Fin 64,digit 11 j<3 := by
  decide +kernel

private theorem bound_row_12 : ∀ j : Fin 64,digit 12 j<3 := by
  decide +kernel

private theorem bound_row_13 : ∀ j : Fin 64,digit 13 j<3 := by
  decide +kernel

private theorem bound_row_14 : ∀ j : Fin 64,digit 14 j<3 := by
  decide +kernel

private theorem bound_row_15 : ∀ j : Fin 64,digit 15 j<3 := by
  decide +kernel

private theorem bound_row_16 : ∀ j : Fin 64,digit 16 j<3 := by
  decide +kernel

private theorem bound_row_17 : ∀ j : Fin 64,digit 17 j<3 := by
  decide +kernel

private theorem bound_row_18 : ∀ j : Fin 64,digit 18 j<3 := by
  decide +kernel

private theorem bound_row_19 : ∀ j : Fin 64,digit 19 j<3 := by
  decide +kernel

private theorem bound_row_20 : ∀ j : Fin 64,digit 20 j<3 := by
  decide +kernel

private theorem bound_row_21 : ∀ j : Fin 64,digit 21 j<3 := by
  decide +kernel

private theorem bound_row_22 : ∀ j : Fin 64,digit 22 j<3 := by
  decide +kernel

private theorem bound_row_23 : ∀ j : Fin 64,digit 23 j<3 := by
  decide +kernel

private theorem bound_row_24 : ∀ j : Fin 64,digit 24 j<3 := by
  decide +kernel

private theorem bound_row_25 : ∀ j : Fin 64,digit 25 j<3 := by
  decide +kernel

private theorem bound_row_26 : ∀ j : Fin 64,digit 26 j<3 := by
  decide +kernel

private theorem bound_row_27 : ∀ j : Fin 64,digit 27 j<3 := by
  decide +kernel

private theorem bound_row_28 : ∀ j : Fin 64,digit 28 j<3 := by
  decide +kernel

private theorem bound_row_29 : ∀ j : Fin 64,digit 29 j<3 := by
  decide +kernel

private theorem bound_row_30 : ∀ j : Fin 64,digit 30 j<3 := by
  decide +kernel

private theorem bound_row_31 : ∀ j : Fin 64,digit 31 j<3 := by
  decide +kernel

private theorem bound_row_32 : ∀ j : Fin 64,digit 32 j<3 := by
  decide +kernel

private theorem bound_row_33 : ∀ j : Fin 64,digit 33 j<3 := by
  decide +kernel

private theorem bound_row_34 : ∀ j : Fin 64,digit 34 j<3 := by
  decide +kernel

private theorem bound_row_35 : ∀ j : Fin 64,digit 35 j<3 := by
  decide +kernel

private theorem bound_row_36 : ∀ j : Fin 64,digit 36 j<3 := by
  decide +kernel

private theorem bound_row_37 : ∀ j : Fin 64,digit 37 j<3 := by
  decide +kernel

private theorem bound_row_38 : ∀ j : Fin 64,digit 38 j<3 := by
  decide +kernel

private theorem bound_row_39 : ∀ j : Fin 64,digit 39 j<3 := by
  decide +kernel

private theorem bound_row_40 : ∀ j : Fin 64,digit 40 j<3 := by
  decide +kernel

private theorem bound_row_41 : ∀ j : Fin 64,digit 41 j<3 := by
  decide +kernel

private theorem bound_row_42 : ∀ j : Fin 64,digit 42 j<3 := by
  decide +kernel

private theorem bound_row_43 : ∀ j : Fin 64,digit 43 j<3 := by
  decide +kernel

private theorem bound_row_44 : ∀ j : Fin 64,digit 44 j<3 := by
  decide +kernel

private theorem bound_row_45 : ∀ j : Fin 64,digit 45 j<3 := by
  decide +kernel

private theorem bound_row_46 : ∀ j : Fin 64,digit 46 j<3 := by
  decide +kernel

private theorem bound_row_47 : ∀ j : Fin 64,digit 47 j<3 := by
  decide +kernel

private theorem bound_row_48 : ∀ j : Fin 64,digit 48 j<3 := by
  decide +kernel

private theorem bound_row_49 : ∀ j : Fin 64,digit 49 j<3 := by
  decide +kernel

private theorem bound_row_50 : ∀ j : Fin 64,digit 50 j<3 := by
  decide +kernel

private theorem bound_row_51 : ∀ j : Fin 64,digit 51 j<3 := by
  decide +kernel

private theorem bound_row_52 : ∀ j : Fin 64,digit 52 j<3 := by
  decide +kernel

private theorem bound_row_53 : ∀ j : Fin 64,digit 53 j<3 := by
  decide +kernel

private theorem bound_row_54 : ∀ j : Fin 64,digit 54 j<3 := by
  decide +kernel

private theorem bound_row_55 : ∀ j : Fin 64,digit 55 j<3 := by
  decide +kernel

private theorem bound_row_56 : ∀ j : Fin 64,digit 56 j<3 := by
  decide +kernel

private theorem bound_row_57 : ∀ j : Fin 64,digit 57 j<3 := by
  decide +kernel

private theorem bound_row_58 : ∀ j : Fin 64,digit 58 j<3 := by
  decide +kernel

private theorem bound_row_59 : ∀ j : Fin 64,digit 59 j<3 := by
  decide +kernel

private theorem bound_row_60 : ∀ j : Fin 64,digit 60 j<3 := by
  decide +kernel

private theorem bound_row_61 : ∀ j : Fin 64,digit 61 j<3 := by
  decide +kernel

private theorem bound_row_62 : ∀ j : Fin 64,digit 62 j<3 := by
  decide +kernel

private theorem bound_row_63 : ∀ j : Fin 64,digit 63 j<3 := by
  decide +kernel

theorem digit_bound : ∀ i j : Fin 64,digit i j<3 := by
  intro i j
  fin_cases i
  · exact bound_row_00 j
  · exact bound_row_01 j
  · exact bound_row_02 j
  · exact bound_row_03 j
  · exact bound_row_04 j
  · exact bound_row_05 j
  · exact bound_row_06 j
  · exact bound_row_07 j
  · exact bound_row_08 j
  · exact bound_row_09 j
  · exact bound_row_10 j
  · exact bound_row_11 j
  · exact bound_row_12 j
  · exact bound_row_13 j
  · exact bound_row_14 j
  · exact bound_row_15 j
  · exact bound_row_16 j
  · exact bound_row_17 j
  · exact bound_row_18 j
  · exact bound_row_19 j
  · exact bound_row_20 j
  · exact bound_row_21 j
  · exact bound_row_22 j
  · exact bound_row_23 j
  · exact bound_row_24 j
  · exact bound_row_25 j
  · exact bound_row_26 j
  · exact bound_row_27 j
  · exact bound_row_28 j
  · exact bound_row_29 j
  · exact bound_row_30 j
  · exact bound_row_31 j
  · exact bound_row_32 j
  · exact bound_row_33 j
  · exact bound_row_34 j
  · exact bound_row_35 j
  · exact bound_row_36 j
  · exact bound_row_37 j
  · exact bound_row_38 j
  · exact bound_row_39 j
  · exact bound_row_40 j
  · exact bound_row_41 j
  · exact bound_row_42 j
  · exact bound_row_43 j
  · exact bound_row_44 j
  · exact bound_row_45 j
  · exact bound_row_46 j
  · exact bound_row_47 j
  · exact bound_row_48 j
  · exact bound_row_49 j
  · exact bound_row_50 j
  · exact bound_row_51 j
  · exact bound_row_52 j
  · exact bound_row_53 j
  · exact bound_row_54 j
  · exact bound_row_55 j
  · exact bound_row_56 j
  · exact bound_row_57 j
  · exact bound_row_58 j
  · exact bound_row_59 j
  · exact bound_row_60 j
  · exact bound_row_61 j
  · exact bound_row_62 j
  · exact bound_row_63 j

private theorem row_pack_00 :
    pack 512 (digit 0)=rowCode 0 := by
  decide +kernel

private theorem row_pack_01 :
    pack 512 (digit 1)=rowCode 1 := by
  decide +kernel

private theorem row_pack_02 :
    pack 512 (digit 2)=rowCode 2 := by
  decide +kernel

private theorem row_pack_03 :
    pack 512 (digit 3)=rowCode 3 := by
  decide +kernel

private theorem row_pack_04 :
    pack 512 (digit 4)=rowCode 4 := by
  decide +kernel

private theorem row_pack_05 :
    pack 512 (digit 5)=rowCode 5 := by
  decide +kernel

private theorem row_pack_06 :
    pack 512 (digit 6)=rowCode 6 := by
  decide +kernel

private theorem row_pack_07 :
    pack 512 (digit 7)=rowCode 7 := by
  decide +kernel

private theorem row_pack_08 :
    pack 512 (digit 8)=rowCode 8 := by
  decide +kernel

private theorem row_pack_09 :
    pack 512 (digit 9)=rowCode 9 := by
  decide +kernel

private theorem row_pack_10 :
    pack 512 (digit 10)=rowCode 10 := by
  decide +kernel

private theorem row_pack_11 :
    pack 512 (digit 11)=rowCode 11 := by
  decide +kernel

private theorem row_pack_12 :
    pack 512 (digit 12)=rowCode 12 := by
  decide +kernel

private theorem row_pack_13 :
    pack 512 (digit 13)=rowCode 13 := by
  decide +kernel

private theorem row_pack_14 :
    pack 512 (digit 14)=rowCode 14 := by
  decide +kernel

private theorem row_pack_15 :
    pack 512 (digit 15)=rowCode 15 := by
  decide +kernel

private theorem row_pack_16 :
    pack 512 (digit 16)=rowCode 16 := by
  decide +kernel

private theorem row_pack_17 :
    pack 512 (digit 17)=rowCode 17 := by
  decide +kernel

private theorem row_pack_18 :
    pack 512 (digit 18)=rowCode 18 := by
  decide +kernel

private theorem row_pack_19 :
    pack 512 (digit 19)=rowCode 19 := by
  decide +kernel

private theorem row_pack_20 :
    pack 512 (digit 20)=rowCode 20 := by
  decide +kernel

private theorem row_pack_21 :
    pack 512 (digit 21)=rowCode 21 := by
  decide +kernel

private theorem row_pack_22 :
    pack 512 (digit 22)=rowCode 22 := by
  decide +kernel

private theorem row_pack_23 :
    pack 512 (digit 23)=rowCode 23 := by
  decide +kernel

private theorem row_pack_24 :
    pack 512 (digit 24)=rowCode 24 := by
  decide +kernel

private theorem row_pack_25 :
    pack 512 (digit 25)=rowCode 25 := by
  decide +kernel

private theorem row_pack_26 :
    pack 512 (digit 26)=rowCode 26 := by
  decide +kernel

private theorem row_pack_27 :
    pack 512 (digit 27)=rowCode 27 := by
  decide +kernel

private theorem row_pack_28 :
    pack 512 (digit 28)=rowCode 28 := by
  decide +kernel

private theorem row_pack_29 :
    pack 512 (digit 29)=rowCode 29 := by
  decide +kernel

private theorem row_pack_30 :
    pack 512 (digit 30)=rowCode 30 := by
  decide +kernel

private theorem row_pack_31 :
    pack 512 (digit 31)=rowCode 31 := by
  decide +kernel

private theorem row_pack_32 :
    pack 512 (digit 32)=rowCode 32 := by
  decide +kernel

private theorem row_pack_33 :
    pack 512 (digit 33)=rowCode 33 := by
  decide +kernel

private theorem row_pack_34 :
    pack 512 (digit 34)=rowCode 34 := by
  decide +kernel

private theorem row_pack_35 :
    pack 512 (digit 35)=rowCode 35 := by
  decide +kernel

private theorem row_pack_36 :
    pack 512 (digit 36)=rowCode 36 := by
  decide +kernel

private theorem row_pack_37 :
    pack 512 (digit 37)=rowCode 37 := by
  decide +kernel

private theorem row_pack_38 :
    pack 512 (digit 38)=rowCode 38 := by
  decide +kernel

private theorem row_pack_39 :
    pack 512 (digit 39)=rowCode 39 := by
  decide +kernel

private theorem row_pack_40 :
    pack 512 (digit 40)=rowCode 40 := by
  decide +kernel

private theorem row_pack_41 :
    pack 512 (digit 41)=rowCode 41 := by
  decide +kernel

private theorem row_pack_42 :
    pack 512 (digit 42)=rowCode 42 := by
  decide +kernel

private theorem row_pack_43 :
    pack 512 (digit 43)=rowCode 43 := by
  decide +kernel

private theorem row_pack_44 :
    pack 512 (digit 44)=rowCode 44 := by
  decide +kernel

private theorem row_pack_45 :
    pack 512 (digit 45)=rowCode 45 := by
  decide +kernel

private theorem row_pack_46 :
    pack 512 (digit 46)=rowCode 46 := by
  decide +kernel

private theorem row_pack_47 :
    pack 512 (digit 47)=rowCode 47 := by
  decide +kernel

private theorem row_pack_48 :
    pack 512 (digit 48)=rowCode 48 := by
  decide +kernel

private theorem row_pack_49 :
    pack 512 (digit 49)=rowCode 49 := by
  decide +kernel

private theorem row_pack_50 :
    pack 512 (digit 50)=rowCode 50 := by
  decide +kernel

private theorem row_pack_51 :
    pack 512 (digit 51)=rowCode 51 := by
  decide +kernel

private theorem row_pack_52 :
    pack 512 (digit 52)=rowCode 52 := by
  decide +kernel

private theorem row_pack_53 :
    pack 512 (digit 53)=rowCode 53 := by
  decide +kernel

private theorem row_pack_54 :
    pack 512 (digit 54)=rowCode 54 := by
  decide +kernel

private theorem row_pack_55 :
    pack 512 (digit 55)=rowCode 55 := by
  decide +kernel

private theorem row_pack_56 :
    pack 512 (digit 56)=rowCode 56 := by
  decide +kernel

private theorem row_pack_57 :
    pack 512 (digit 57)=rowCode 57 := by
  decide +kernel

private theorem row_pack_58 :
    pack 512 (digit 58)=rowCode 58 := by
  decide +kernel

private theorem row_pack_59 :
    pack 512 (digit 59)=rowCode 59 := by
  decide +kernel

private theorem row_pack_60 :
    pack 512 (digit 60)=rowCode 60 := by
  decide +kernel

private theorem row_pack_61 :
    pack 512 (digit 61)=rowCode 61 := by
  decide +kernel

private theorem row_pack_62 :
    pack 512 (digit 62)=rowCode 62 := by
  decide +kernel

private theorem row_pack_63 :
    pack 512 (digit 63)=rowCode 63 := by
  decide +kernel

theorem row_binding : ∀ i : Fin 64,pack 512 (digit i)=rowCode i := by
  intro i
  fin_cases i
  · exact row_pack_00
  · exact row_pack_01
  · exact row_pack_02
  · exact row_pack_03
  · exact row_pack_04
  · exact row_pack_05
  · exact row_pack_06
  · exact row_pack_07
  · exact row_pack_08
  · exact row_pack_09
  · exact row_pack_10
  · exact row_pack_11
  · exact row_pack_12
  · exact row_pack_13
  · exact row_pack_14
  · exact row_pack_15
  · exact row_pack_16
  · exact row_pack_17
  · exact row_pack_18
  · exact row_pack_19
  · exact row_pack_20
  · exact row_pack_21
  · exact row_pack_22
  · exact row_pack_23
  · exact row_pack_24
  · exact row_pack_25
  · exact row_pack_26
  · exact row_pack_27
  · exact row_pack_28
  · exact row_pack_29
  · exact row_pack_30
  · exact row_pack_31
  · exact row_pack_32
  · exact row_pack_33
  · exact row_pack_34
  · exact row_pack_35
  · exact row_pack_36
  · exact row_pack_37
  · exact row_pack_38
  · exact row_pack_39
  · exact row_pack_40
  · exact row_pack_41
  · exact row_pack_42
  · exact row_pack_43
  · exact row_pack_44
  · exact row_pack_45
  · exact row_pack_46
  · exact row_pack_47
  · exact row_pack_48
  · exact row_pack_49
  · exact row_pack_50
  · exact row_pack_51
  · exact row_pack_52
  · exact row_pack_53
  · exact row_pack_54
  · exact row_pack_55
  · exact row_pack_56
  · exact row_pack_57
  · exact row_pack_58
  · exact row_pack_59
  · exact row_pack_60
  · exact row_pack_61
  · exact row_pack_62
  · exact row_pack_63

private theorem column_pack_00 :
    reversePack 512 (fun j : Fin 64 => digit j 0)=columnCode 0 := by
  decide +kernel

private theorem column_pack_01 :
    reversePack 512 (fun j : Fin 64 => digit j 1)=columnCode 1 := by
  decide +kernel

private theorem column_pack_02 :
    reversePack 512 (fun j : Fin 64 => digit j 2)=columnCode 2 := by
  decide +kernel

private theorem column_pack_03 :
    reversePack 512 (fun j : Fin 64 => digit j 3)=columnCode 3 := by
  decide +kernel

private theorem column_pack_04 :
    reversePack 512 (fun j : Fin 64 => digit j 4)=columnCode 4 := by
  decide +kernel

private theorem column_pack_05 :
    reversePack 512 (fun j : Fin 64 => digit j 5)=columnCode 5 := by
  decide +kernel

private theorem column_pack_06 :
    reversePack 512 (fun j : Fin 64 => digit j 6)=columnCode 6 := by
  decide +kernel

private theorem column_pack_07 :
    reversePack 512 (fun j : Fin 64 => digit j 7)=columnCode 7 := by
  decide +kernel

private theorem column_pack_08 :
    reversePack 512 (fun j : Fin 64 => digit j 8)=columnCode 8 := by
  decide +kernel

private theorem column_pack_09 :
    reversePack 512 (fun j : Fin 64 => digit j 9)=columnCode 9 := by
  decide +kernel

private theorem column_pack_10 :
    reversePack 512 (fun j : Fin 64 => digit j 10)=columnCode 10 := by
  decide +kernel

private theorem column_pack_11 :
    reversePack 512 (fun j : Fin 64 => digit j 11)=columnCode 11 := by
  decide +kernel

private theorem column_pack_12 :
    reversePack 512 (fun j : Fin 64 => digit j 12)=columnCode 12 := by
  decide +kernel

private theorem column_pack_13 :
    reversePack 512 (fun j : Fin 64 => digit j 13)=columnCode 13 := by
  decide +kernel

private theorem column_pack_14 :
    reversePack 512 (fun j : Fin 64 => digit j 14)=columnCode 14 := by
  decide +kernel

private theorem column_pack_15 :
    reversePack 512 (fun j : Fin 64 => digit j 15)=columnCode 15 := by
  decide +kernel

private theorem column_pack_16 :
    reversePack 512 (fun j : Fin 64 => digit j 16)=columnCode 16 := by
  decide +kernel

private theorem column_pack_17 :
    reversePack 512 (fun j : Fin 64 => digit j 17)=columnCode 17 := by
  decide +kernel

private theorem column_pack_18 :
    reversePack 512 (fun j : Fin 64 => digit j 18)=columnCode 18 := by
  decide +kernel

private theorem column_pack_19 :
    reversePack 512 (fun j : Fin 64 => digit j 19)=columnCode 19 := by
  decide +kernel

private theorem column_pack_20 :
    reversePack 512 (fun j : Fin 64 => digit j 20)=columnCode 20 := by
  decide +kernel

private theorem column_pack_21 :
    reversePack 512 (fun j : Fin 64 => digit j 21)=columnCode 21 := by
  decide +kernel

private theorem column_pack_22 :
    reversePack 512 (fun j : Fin 64 => digit j 22)=columnCode 22 := by
  decide +kernel

private theorem column_pack_23 :
    reversePack 512 (fun j : Fin 64 => digit j 23)=columnCode 23 := by
  decide +kernel

private theorem column_pack_24 :
    reversePack 512 (fun j : Fin 64 => digit j 24)=columnCode 24 := by
  decide +kernel

private theorem column_pack_25 :
    reversePack 512 (fun j : Fin 64 => digit j 25)=columnCode 25 := by
  decide +kernel

private theorem column_pack_26 :
    reversePack 512 (fun j : Fin 64 => digit j 26)=columnCode 26 := by
  decide +kernel

private theorem column_pack_27 :
    reversePack 512 (fun j : Fin 64 => digit j 27)=columnCode 27 := by
  decide +kernel

private theorem column_pack_28 :
    reversePack 512 (fun j : Fin 64 => digit j 28)=columnCode 28 := by
  decide +kernel

private theorem column_pack_29 :
    reversePack 512 (fun j : Fin 64 => digit j 29)=columnCode 29 := by
  decide +kernel

private theorem column_pack_30 :
    reversePack 512 (fun j : Fin 64 => digit j 30)=columnCode 30 := by
  decide +kernel

private theorem column_pack_31 :
    reversePack 512 (fun j : Fin 64 => digit j 31)=columnCode 31 := by
  decide +kernel

private theorem column_pack_32 :
    reversePack 512 (fun j : Fin 64 => digit j 32)=columnCode 32 := by
  decide +kernel

private theorem column_pack_33 :
    reversePack 512 (fun j : Fin 64 => digit j 33)=columnCode 33 := by
  decide +kernel

private theorem column_pack_34 :
    reversePack 512 (fun j : Fin 64 => digit j 34)=columnCode 34 := by
  decide +kernel

private theorem column_pack_35 :
    reversePack 512 (fun j : Fin 64 => digit j 35)=columnCode 35 := by
  decide +kernel

private theorem column_pack_36 :
    reversePack 512 (fun j : Fin 64 => digit j 36)=columnCode 36 := by
  decide +kernel

private theorem column_pack_37 :
    reversePack 512 (fun j : Fin 64 => digit j 37)=columnCode 37 := by
  decide +kernel

private theorem column_pack_38 :
    reversePack 512 (fun j : Fin 64 => digit j 38)=columnCode 38 := by
  decide +kernel

private theorem column_pack_39 :
    reversePack 512 (fun j : Fin 64 => digit j 39)=columnCode 39 := by
  decide +kernel

private theorem column_pack_40 :
    reversePack 512 (fun j : Fin 64 => digit j 40)=columnCode 40 := by
  decide +kernel

private theorem column_pack_41 :
    reversePack 512 (fun j : Fin 64 => digit j 41)=columnCode 41 := by
  decide +kernel

private theorem column_pack_42 :
    reversePack 512 (fun j : Fin 64 => digit j 42)=columnCode 42 := by
  decide +kernel

private theorem column_pack_43 :
    reversePack 512 (fun j : Fin 64 => digit j 43)=columnCode 43 := by
  decide +kernel

private theorem column_pack_44 :
    reversePack 512 (fun j : Fin 64 => digit j 44)=columnCode 44 := by
  decide +kernel

private theorem column_pack_45 :
    reversePack 512 (fun j : Fin 64 => digit j 45)=columnCode 45 := by
  decide +kernel

private theorem column_pack_46 :
    reversePack 512 (fun j : Fin 64 => digit j 46)=columnCode 46 := by
  decide +kernel

private theorem column_pack_47 :
    reversePack 512 (fun j : Fin 64 => digit j 47)=columnCode 47 := by
  decide +kernel

private theorem column_pack_48 :
    reversePack 512 (fun j : Fin 64 => digit j 48)=columnCode 48 := by
  decide +kernel

private theorem column_pack_49 :
    reversePack 512 (fun j : Fin 64 => digit j 49)=columnCode 49 := by
  decide +kernel

private theorem column_pack_50 :
    reversePack 512 (fun j : Fin 64 => digit j 50)=columnCode 50 := by
  decide +kernel

private theorem column_pack_51 :
    reversePack 512 (fun j : Fin 64 => digit j 51)=columnCode 51 := by
  decide +kernel

private theorem column_pack_52 :
    reversePack 512 (fun j : Fin 64 => digit j 52)=columnCode 52 := by
  decide +kernel

private theorem column_pack_53 :
    reversePack 512 (fun j : Fin 64 => digit j 53)=columnCode 53 := by
  decide +kernel

private theorem column_pack_54 :
    reversePack 512 (fun j : Fin 64 => digit j 54)=columnCode 54 := by
  decide +kernel

private theorem column_pack_55 :
    reversePack 512 (fun j : Fin 64 => digit j 55)=columnCode 55 := by
  decide +kernel

private theorem column_pack_56 :
    reversePack 512 (fun j : Fin 64 => digit j 56)=columnCode 56 := by
  decide +kernel

private theorem column_pack_57 :
    reversePack 512 (fun j : Fin 64 => digit j 57)=columnCode 57 := by
  decide +kernel

private theorem column_pack_58 :
    reversePack 512 (fun j : Fin 64 => digit j 58)=columnCode 58 := by
  decide +kernel

private theorem column_pack_59 :
    reversePack 512 (fun j : Fin 64 => digit j 59)=columnCode 59 := by
  decide +kernel

private theorem column_pack_60 :
    reversePack 512 (fun j : Fin 64 => digit j 60)=columnCode 60 := by
  decide +kernel

private theorem column_pack_61 :
    reversePack 512 (fun j : Fin 64 => digit j 61)=columnCode 61 := by
  decide +kernel

private theorem column_pack_62 :
    reversePack 512 (fun j : Fin 64 => digit j 62)=columnCode 62 := by
  decide +kernel

private theorem column_pack_63 :
    reversePack 512 (fun j : Fin 64 => digit j 63)=columnCode 63 := by
  decide +kernel

theorem column_binding : ∀ i : Fin 64,reversePack 512 (fun j => digit j i)=columnCode i := by
  intro i
  fin_cases i
  · exact column_pack_00
  · exact column_pack_01
  · exact column_pack_02
  · exact column_pack_03
  · exact column_pack_04
  · exact column_pack_05
  · exact column_pack_06
  · exact column_pack_07
  · exact column_pack_08
  · exact column_pack_09
  · exact column_pack_10
  · exact column_pack_11
  · exact column_pack_12
  · exact column_pack_13
  · exact column_pack_14
  · exact column_pack_15
  · exact column_pack_16
  · exact column_pack_17
  · exact column_pack_18
  · exact column_pack_19
  · exact column_pack_20
  · exact column_pack_21
  · exact column_pack_22
  · exact column_pack_23
  · exact column_pack_24
  · exact column_pack_25
  · exact column_pack_26
  · exact column_pack_27
  · exact column_pack_28
  · exact column_pack_29
  · exact column_pack_30
  · exact column_pack_31
  · exact column_pack_32
  · exact column_pack_33
  · exact column_pack_34
  · exact column_pack_35
  · exact column_pack_36
  · exact column_pack_37
  · exact column_pack_38
  · exact column_pack_39
  · exact column_pack_40
  · exact column_pack_41
  · exact column_pack_42
  · exact column_pack_43
  · exact column_pack_44
  · exact column_pack_45
  · exact column_pack_46
  · exact column_pack_47
  · exact column_pack_48
  · exact column_pack_49
  · exact column_pack_50
  · exact column_pack_51
  · exact column_pack_52
  · exact column_pack_53
  · exact column_pack_54
  · exact column_pack_55
  · exact column_pack_56
  · exact column_pack_57
  · exact column_pack_58
  · exact column_pack_59
  · exact column_pack_60
  · exact column_pack_61
  · exact column_pack_62
  · exact column_pack_63

def data : PackedData 64 3 512 where
  raw := digit
  digit_lt := digit_bound
  rowCode := rowCode
  columnCode := columnCode
  row_binding := row_binding
  column_binding := column_binding

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheC2
