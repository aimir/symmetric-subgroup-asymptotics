import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

/-! One shared reduced cache in the EXACT selected Suz positive DAG.
Digit and pack bindings are kernel obligations, not trusted metadata. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheB2
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

def lowColumnCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 1662833465715988124195445731233890313
  | 1 => 344152639832029895053723955865059352
  | 2 => 3334834103945737728936290659533324296
  | 3 => 669887583155295328159117420433244416
  | 4 => 10547170530508125509644862462365696
  | 5 => 3323233041644928731097684107327455232
  | 6 => 1334583265603141908294875225419415616
  | 7 => 332388208123047858222210076990504960
  | 8 => 665993677424270938086247665336582144
  | 9 => 2992142194998356097323429501580869632
  | 10 => 345450792656612855811383896687248384
  | 11 => 2992142274225990887133306413329154048
  | 12 => 1329228788690347919059952384459407360
  | 13 => 335065565418211191617354830100561920
  | 14 => 337661871999456558872312576779223040
  | 15 => 665993281602388109551644056764874752
  | 16 => 669887820844540655183625766664404992
  | 17 => 2992061143958858115796656820668596224
  | 18 => 2990844595523828195620198282493427712
  | 19 => 676378509145284422790749362843549696
  | 20 => 1668026078862688445796279834600538112
  | 21 => 2666406775677399775448528484124590080
  | 22 => 2996117705113041196351140089126977536
  | 23 => 340258020743047051581308588739526656
  | 24 => 1664293719355029460098128199760740352
  | 25 => 2677912521925866052148908500451328
  | 26 => 1999116054314246302335344867092201472
  | 27 => 3002445738300116005659978908737470464
  | 28 => 2000332998885497473020802835136118784
  | 29 => 2990925645939293780634363095588798464
  | 30 => 1664293403067094181509878886369853440
  | 31 => 2001712360910152256336371220909916160
  | 32 => 1334582710773510400576632262628474880
  | 33 => 1329228630858507453634338345839493120
  | 34 => 672402607208073323028086276824760320
  | 35 => 340258436686442332897565991336148992
  | 36 => 1673299584902423338907537657198280704
  | 37 => 1674598609545218795118850860866600960
  | 38 => 2990930637927364264196959448019763200
  | 39 => 2659937003616848823803612411616821248
  | 40 => 342691909585773564007991020957466624
  | 41 => 335309429712630408851466123321802752
  | 42 => 10127114922584322904948736
  | 43 => 28558108719860295197454119215300608
  | 44 => 420657650868244935875583226675200000
  | 45 => 3334753132767879391153047159634395136
  | 46 => 8309135703298429043618423908018946048
  | 47 => 1342209530532716882953546002398707712
  | 48 => 21945405407243933291707093103633498112
  | 49 => 85747051289470769291077815971526737920
  | 50 => 1331824461436696142987454917000560640
  | 51 => 2659754065784616568442198573289832448
  | 52 => 2005525295744164526910853681531322368
  | 53 => 1999034291155634235264190367433490432
  | 54 => 667291355188453586939653989500715008
  | 55 => 81605636408907785958092733153280
  | 56 => 6653343718536668015155768975163392
  | 57 => 2663810627557768505341573830889439232
  | 58 => 1340991873207153194662634542365409280
  | 59 => 2661133903772903353149428289394180096
  | 60 => 666074489849992849671745867041734656
  | 61 => 1460334115951320296352699327184896
  | 62 => 1342371314126172378584141084575662080
  | 63 => 1661616916660931554875473497516146688
  | _ => 0

def rowCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 525314
  | 2 => 512
  | 3 => 18014398509481984
  | 4 => 134217728
  | 5 => 1237940039285380274899124224
  | 6 => 68719476736
  | 7 => 35184372088832
  | 8 => 43556142965880123323311949751266331066368
  | 9 => 11417981541647679048466287755595961091061972992
  | 10 => 9223372036854775808
  | 11 => 4722366482869645213696
  | 12 => 2417851639229258349412352
  | 13 => 105312291668557186697918027683670432318895095400549111254310977536
  | 14 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | 15 => 633825300114114700748351602688
  | 16 => 3705346855594118253554271520278013051304639509300498049262642688253220148477952
  | 17 => 324518553658426726783156020576256
  | 18 => 166153499473114484112975882535043072
  | 19 => 85070591730234615865843651857942052864
  | 20 => 34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216
  | 21 => 22300745198530623141535718272648361505980416
  | 22 => 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976
  | 23 => 615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544
  | 24 => 5846006549323611672814739330865132078623730171904
  | 25 => 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032
  | 26 => 2993155353253689176481146537402947624255349848014848
  | 27 => 1532495540865888858358347027150309183618739122183602176
  | 28 => 2907354897182427562197295231552018137414565442749272241125960796722557152453591693304764202855054262243050086425064711734138406514458624
  | 29 => 784637716923335095479473677900958302012794430558004314112
  | 30 => 401734511064747568885490523085290650630550748445698208825344
  | 31 => 205688069665150755269371147819668813122841983204197482918576128
  | 32 => 26815615859885194199148049996411692254958731641184786755447122887443528060147093953603748596333806855380063716372972101707507765623893139892867298012168192
  | 33 => 53919893334301279589334030174039261347274288845081144962207220498432
  | 34 => 1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312
  | 35 => 3685510180489786476798393145496356338829463458447574221155108254363338583373662405684510631334526756890120750655118136814270936467547734534039148189042148299971231744
  | 36 => 14134776518227074636666380005943348126619871175004951664972849610340958208
  | 37 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | 38 => 483069036731406032910206207523789752311839931022991667029391868742247888515683486025812512703875360905974286423233170911310788113668052797302190463349757291299584178651138
  | 39 => 1890666736650419806627577840683542342496512892332091008285519309327298059067971149660853083073423055720897406221511576323633407760961697483432327661786306403032745115650
  | 40 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | 41 => 967079721313886044137765930815634205509936492062250100783217501091040358344146348660177510234107844057435473059768562327782258603083498130615871807884699909540747080106498
  | 42 => 971334446112864535459730953411759453321203419526069760625906204869452142602604249088
  | 43 => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
  | 44 => 3685517237555464901622371066353595179705125643207297696394299149576181627315425469323567562855232504820386325184749587340105966140646327973116628465447208798363059202
  | 45 => 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672
  | 46 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 47 => 66749594872528440074844428317798503581334516323645399060845050244444366430645017188217565216768
  | 48 => 966134387952590413906467342765721610332562858466757057484879875113869841993787890340458519785367210831575586578088035411762932619856526259360915358772481254869367275913729
  | 49 => 967077871374579077224696642985224424610896605392596243596705053230130760614002981807029096378650894772271515541764391598796363562184075828953981462184275220827621877351425
  | 50 => 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592
  | 51 => 8958978968711216842229769122273777112486581988938598139599956403855167484720643781523509973086428463104
  | 52 => 4586997231980143023221641790604173881593129978336562247475177678773845752176969616140037106220251373109248
  | 53 => 484957864305053960954007492586040004161433466743229139481488371221296523262209375431292289445458496275629812828306641841813543443894231508965557089608563998523310832092160
  | 54 => 1202453802380202612679414065556140558016349465041059773802132977424491020858679523053413887173001575952350707712
  | 55 => 1888827580704886459558681962126935806031643138093111435885098264271631270312071977795204914404999455949219315791268064436657088952580311466249590621530702128734573691393
  | 56 => 1886981212438256734751409732629391202127906996241309115565312571250466920729175357307148346752194682633393549938345444328752628386768123924481187357652297889932573672448
  | 57 => 315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528
  | 58 => 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352834580008614464743948248296718336
  | 59 => 483067197575419364356033599229135899656653582143538612180261545664113980477153557222297613554288787436478926107116919780894626649022263406411903140728333877515226892993025
  | 60 => 484010680997435567259478845088830474664747648385273304251159091026249363245617124306129610533907366221854971489497721042661213955409258417596282613147509050066039762059265
  | 61 => 42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384
  | 62 => 11090678776483259438313656736572334813745748301503266300681918322458485231222502492159897624416558312389564843845614287315896631296
  | 63 => 5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855943457200048954515105739075223552
  | _ => 0

def columnCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 484954171589568063763039763656992552482824376823512595046342509581562704867391127493067284185329151629186736603508562771288389865670782329533815403200961735044029248176128
  | 1 => 1888823967501015569359176487066882623627853638147876679241021219605353889869117467474746041653857537465822795522111929659586033857333886978360128889843448391881753362432
  | 2 => 1886981212410770676120777290494134445458460610208220214188103150122812081196074426043063362588829383824864705433020316412615158544454069119924268722244533465754443448320
  | 3 => 7029552803973744348141466418259346654483901747346744739219930582205996219799199797387975083245913882058999078573451770626512387555097224603709180443629883228160
  | 4 => 26815615859885194199148049996411692254958731641184786755447122887443528060147108427615011100645305138829419528697194792924924835708020643238905580949078016
  | 5 => 52374249726338269920211035149241586435466272736689036631732661889538140742482029883763678945456144054804320163963664745131478741121994236450546500239360
  | 6 => 3599131035634557106248430806148785487095757694641533306480604458089470064537190296255247022894375400656420083581610671827773803139320048634094835907429708404359168
  | 7 => 390218568789499028922699653724145788218574767833121393857394619953178704358156085188504175746044758638919886947223644663730725306445413094522880
  | 8 => 762145642166990290864647761179972242614403843424065222377723867110512033327564177569299040499174604371671073375974386003365744822592129204224
  | 9 => 1488565707357402911845015158554633286356257506687627387456491935158954839599126547751368324106462356824555683365572587433473352448241303552
  | 10 => 13729595320261219429963801598162786434538870600286610818788926918371086366795312111482124966705582977601963802637421333122431777302178819502720926378136436736
  | 11 => 11090678776483259438313656736572334813745748301503266315155929531042903796939183323385760602030109841624661528929304267088235331584
  | 12 => 42307582002575910332922579714097346549017899709721235039794855160177678342738027402533090145346185206813105252364636087386112
  | 13 => 82631996098781074868989413504096379978550585370535152464500992743602006487028301742989375065147959390124873949575458586624
  | 14 => 161390617380431786853494948250188242145606612051826523577122237488138317155569661962878291196553681450824251921351573504
  | 15 => 102293456496754433437912178025862473506770063938845774671352855253004181152120091048686608950901185742191071856599803748273135952142608512757306228736
  | 16 => 615656346818663737691860001564743965704370926101022604588426598499242324862464828927396694145301481744225085161472
  | 17 => 199791907220223502808422222706762643567910281130558153654986045416023798521470577019961804569250049197223207977287031347967250943889684959137366016
  | 18 => 4586997231980143023221641790604173881647155183962532084251209627062766040480054519283047828828447395807232
  | 19 => 17498005798264095394980017816940971133450742253288188693086542304303770847591765007367392358828081152
  | 20 => 34175792574734561318327584304344085989593281334923568912496751167779023679778122019685750959767552
  | 21 => 130370302485407109521180632003299564312924400463520478538748647945940435090542135505089200128
  | 22 => 254629497041825234794818320674962222131989748744072055079744682085745419949534632677998592
  | 23 => 497323236424260653364071979004206075125224578505484690546722780508020880983982918860800
  | 24 => 2907354897182427562197295231552018137414565442749272241125960796722557257766285096373015648341967521507159428681296052179073574918684672
  | 25 => 1897137590064188651132882155967645186030281641972603656200816669385811796519026688
  | 26 => 5678427533559428832416592249125035424637823130369672345949142181098849751079324347230468423868311367125674990349633632974206654218240
  | 27 => 7251140407875695316314206770139161227103944705834572909111525858243021635584
  | 28 => 27714825173830857711910846862710039650163591473011119411988621141475328
  | 29 => 21661481985318866090456360813617841433097164651373566993519479773963382641416066991465132625288792543738199606136721769244917760
  | 30 => 14474011154664730919485066392647102131165966884895045303435451326926115831808
  | 31 => 14474011262714936082405195459820788953357035520805001146307957548605581033472
  | 32 => 54025206429440394394223305202363798710110895440426127594449430118400
  | 33 => 54130518721107416098071010549881401238768588859580559458452008599552
  | 34 => 14474011262714935679886052664472009461136898215493226135624286460149208449024
  | 35 => 14474011262714936081620560736052829368755793888794836399688395650698645078016
  | 36 => 315216049571155833698232320801148910440645151169354930812229759282427499605532189846902275550759457726087261944020992
  | 37 => 53919894137770301718829168032217830194846782432658963074033530175488
  | 38 => 107945098960271122351676684883225617005411811745829228742001196793856
  | 39 => 105312693403068251445486956815407075856204850044142904244856422400
  | 40 => 1202453802380202612679414065556140572490360727545371673820087411673677621662067063118597959253276788752721641472
  | 41 => 210625386806139496046327080207704699827338453917564248312030167040
  | 42 => 2348542582773833227889480596789351501386945158532511557218911918636837427101989097308250594918696757342765056
  | 43 => 105313095137585302503762393240426088683752434341012019915683528704
  | 44 => 54025206429438861898682439313590510954812741807069067162163246792704
  | 45 => 8958978968711216842229769122273777166406475724974388793681555550582308440776064524385959762463524126720
  | 46 => 14474011262714936483355068807645022699726871370585573470975813685921326563328
  | 47 => 14474011208795043149053792211466345823018000062065704092682328848512929759232
  | 48 => 54130517917638393962729866316603958735405036187913736809606683820544
  | 49 => 54025205625969839769187301455582249444202666459980389620157855563777
  | 50 => 66749594872528440074844428371823709207304356092832700516342229096914322399384912134626311405568
  | 51 => 107839786668602559178668060348078522694548577694884656407284354646016
  | 52 => 105312291668560179853271281542988096925901734820673897400971034624
  | 53 => 108050411251939679538374602910824216521479442686867860029797186928640
  | 54 => 107839786668602559178668060391634665660429938962958258021832400568320
  | 55 => 54025206429438864891837792567279687435959279210007468010223148466176
  | 56 => 108050411653674187609966818586351847274966624354315558518409633202176
  | 57 => 971334446112864535670355938483390877775314911318429638730021035516291205362383585280
  | 58 => 107839787070337076229726335784503541708013664394700335239297065025536
  | 59 => 210624583337117366551189309226658529246034774964428127588812062720
  | 60 => 53919894137770301718829168032132593449618312637607478599693182697472
  | 61 => 3719820866802913296301590804417887181408573735643201400124704063638742480453632
  | 62 => 210624985071625438143404940942934541661151326759440790427705278464
  | 63 => 53919894137770301718829168032302734633077543924577514040195937206272
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

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheB2
