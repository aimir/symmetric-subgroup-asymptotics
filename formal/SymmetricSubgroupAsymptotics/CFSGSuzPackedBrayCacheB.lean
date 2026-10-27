import SymmetricSubgroupAsymptotics.MatrixKroneckerProductReflection
import Mathlib.Tactic.FinCases

import SymmetricSubgroupAsymptotics.External.CFSG.Models.MatrixGroups.Suz
/-! One shared reduced cache in the EXACT selected Suz positive DAG.
Digit and pack bindings are kernel obligations, not trusted metadata. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix BigOperators
namespace SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheB
open MatrixKroneckerProductReflection MatrixKroneckerDotReflection
open MatrixNaturalRowDotReflection SmallNaturalMatrixProductReflection

open CFSG.Models.MatrixGroups.Suz

def lowColumnCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 109168741193826076872483311502021885985
  | 1 => 192241383742438579465710403451158003744
  | 2 => 88395167688609976684632147592050901028
  | 3 => 44291757647010024761685432673924812800
  | 4 => 86909080647166900962719307273909305408
  | 5 => 214512306156451304851175557585706156032
  | 6 => 193248902337909255625316939981937180928
  | 7 => 24015802900407675853284518202244596736
  | 8 => 127694339223247529990616480547617112064
  | 9 => 3495186537165918386043218440679849984
  | 10 => 215341882062252662736103030097367285760
  | 11 => 24762798995314806590646973878681796608
  | 12 => 215511797948707254605079648195016130560
  | 13 => 45946802231053919811147641057068449792
  | 14 => 88069655296880971026002721755789000704
  | 15 => 23101264000583661749517215053335494656
  | 16 => 108425867518477928965988837878946332672
  | 17 => 23261652205319897617746099531319083008
  | 18 => 130934337493961582086604947446084665344
  | 19 => 193570895691957946462000145773224787968
  | 20 => 191415813632340988136624227789656031232
  | 21 => 22683066027954287612831283873400750080
  | 22 => 45194106838470493765913642552375902208
  | 23 => 85819038037254791139321338228027424768
  | 24 => 85408435827002641740095341291332698112
  | 25 => 171976031646501520135875072078372667392
  | 26 => 172231508876631176537249731655550107648
  | 27 => 22766056597257069963854555532452954112
  | 28 => 170568423545215952571561942087301595136
  | 29 => 107011098460189612172783807308262014976
  | 30 => 1841399442710409111581509438712840192
  | 31 => 214673454991161758914177579251115491328
  | 32 => 43305728264514417546893068255883165696
  | 33 => 173466408455951909403930491661940948992
  | 34 => 51342942416321928897488300570321092608
  | 35 => 193166880273472088270122497297736531968
  | 36 => 215430450274389408667944816155429961728
  | 37 => 127940227905860918847023487857962516480
  | 38 => 85902687725429227470821299815576502272
  | 39 => 109007425049043433311766447038918557696
  | 40 => 87736278440442230690442493474965028864
  | 41 => 172218791805809686939893916454115868672
  | 42 => 335744906988129188106665639362428928
  | 43 => 129442033854360905889021742572294373376
  | 44 => 130361237728200800487105893913679888384
  | 45 => 127619197926654320281268169465407733760
  | 46 => 106349486298532576235834717549390462976
  | 47 => 213099210416762331130226433757154377728
  | 48 => 129599856354089320431061338047654133760
  | 49 => 173547517811956912433954730819926884352
  | 50 => 88483416452795483992112673560977211392
  | 51 => 1331834285419060670417010196394016768
  | 52 => 170563158992273506966312429936183345152
  | 53 => 168881483564805633784996787833012224
  | 54 => 21267739203406706102256279243815124992
  | 55 => 130764938808951883335224140003276750848
  | 56 => 193491398787516433739773484521540812800
  | 57 => 23106248363207049142847067560744058880
  | 58 => 24763777582273586536434105605509087232
  | 59 => 173547370764487285959344157202355060736
  | 60 => 45859182221566144594915907456536150016
  | 61 => 2831632319934052035078571635221987328
  | 62 => 85073553041264911523989885750173761536
  | 63 => 215336887815993372940752399062527901696
  | _ => 0

def rowCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 262144
  | 2 => 525314
  | 3 => 68719476736
  | 4 => 18014398509481984
  | 5 => 9223372036854775808
  | 6 => 134217728
  | 7 => 1237940039285380274899124224
  | 8 => 633825300114114700748351602688
  | 9 => 324518553658426726783156020576256
  | 10 => 35184372088832
  | 11 => 43556142965880123323311949751266331066368
  | 12 => 11417981541647679048466287755595961091061972992
  | 13 => 5846006549323611672814739330865132078623730171904
  | 14 => 2993155353253689176481146537402947624255349848014848
  | 15 => 4722366482869645213696
  | 16 => 784637716923335095479473677900958302012794430558004314112
  | 17 => 2417851639229258349412352
  | 18 => 105312291668557186697918027683670432318895095400549111254310977536
  | 19 => 27606985387162255149739023449108101809804435888681546220650096895197184
  | 20 => 14134776518227074636666380005943348126619871175004951664972849610340958208
  | 21 => 3705346855594118253554271520278013051304639509300498049262642688253220148477952
  | 22 => 1897137590064188545819787018382342682267975428761855001222473056385648716020711424
  | 23 => 971334446112864535459730953411759453321203419526069760625906204869452142602604249088
  | 24 => 166153499473114484112975882535043072
  | 25 => 254629497041810760783555711051172270131433549208242031329517556169297662470417088272924672
  | 26 => 85070591730234615865843651857942052864
  | 27 => 34175792574734561318320347298712833833643272357706444319152665725155515612490248800367393390985216
  | 28 => 17498005798264095394980017816940970922825355447145699491406164851279623993595007385788105416184430592
  | 29 => 22300745198530623141535718272648361505980416
  | 30 => 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934976
  | 31 => 615656346818663737691860001564743965704370926101022604186692084441339402679643915803347910232576806887603562348544
  | 32 => 315216049571155833698232320801148910440637914163723573343586347233965774171977684891314130039079325126453023922454528
  | 33 => 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651304964410605948901503127919788032
  | 34 => 42307582002575910332922579714097346549017899709713998034217522897561970639123926132812109468141778230245837569601494931472384
  | 35 => 21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047688590453885868835635965404913860608
  | 36 => 1532495540865888858358347027150309183618739122183602176
  | 37 => 2907354897182427562197295231552018137414565442749272241125960796722557152453591693304764202855054262243050086425064711734138406514458624
  | 38 => 1488565707357402911845015158554633286356257506687627387456491927921949262056238946972039271861787782268441644249633132407878864135402815488
  | 39 => 762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235344521442121855812163792833978437326241529856
  | 40 => 401734511064747568885490523085290650630550748445698208825344
  | 41 => 199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154228923591770023865308670443474450259602571264
  | 42 => 205688069665150755269371147819668813122841983204197482918576128
  | 43 => 26815615859885194199148049996411692254958731641184786755447122887443528060147093953603748596333806855380063716372972101707507765623893139892867298012168192
  | 44 => 13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782961716074243975999433287625148056582230114304
  | 45 => 53919893334301279589334030174039261347274288845081144962207220498432
  | 46 => 1842755090244893238399196572748178169393027939656465052918069482541808673043041431682679065028153695088607604995490158642466105776330465152617887818082371115063181312
  | 47 => 3685510180489786476798393145496356338829463458447574221155108254363338583373662405684510631334526756890120750655118136814270936467547734534039148189042148299971231744
  | 48 => 943490606205385338060388645247067222729230305104110107094051575061406040598037213021531681294414691885367093757690961224942646157481198158140358562858174010912348831744
  | 49 => 483067190377157293086918986366498418037365916213304374832154406431439892786195053067024220822740322245307952003937772147170634832630373456967863584183385093587122601852928
  | 50 => 7237005577332262213973186563042994240829374041602535252466099000494570602496
  | 51 => 483069036731406032910206207523789752311839931022991667029391868742247888515683486025812512703875360905974286423233170911310788113668052797302190463349757291299584178651138
  | 52 => 1890666736650419806627577840683542342496512892332091008285519309327298059067971149660853083073423055720897406221511576323633407760961697483432327661786306403032745115650
  | 53 => 3692708456344334722028702045190019941386516623993375897198059946669481684729549141984940351820410039063307083444276723927413763326176834680500388921529793124709696512
  | 54 => 967079721313886044137765930815634205509936492062250100783217501091040358344146348660177510234107844057435473059768562327782258603083498130615871807884699909540747080106498
  | 55 => 484956014344672038251700718310694282155964526602075433016548201478330724408611213016695328703971009741255893328082979151169312152535175966843013746835922841862476742787584
  | 56 => 1842755104028172164629913491528745600493006555238059724249645586489387011097283971521323817645455950425114610874818852555363812431264663630573016957556650272964476929
  | 57 => 497323236409786642155382248146820840100456150797347717440463976893159497012533375533056
  | 58 => 3685517237555464901622371066353595179705125643207297696394299149576181627315425469323567562855232504820386325184749587340105966140646327973116628465447208798363059202
  | 59 => 7212348662988168876427134117627451814703427142796312080823721930788907720514356842849589459264248952313925244038148390398530158015479293641364328434060869398692864
  | 60 => 966138073476843738896211691282674277495278564986488532885059312199585063256637114493479209847366067989069697851523012767173216872360467630344738607735156506123774957453314
  | 61 => 130370302485407109521180524058200202307293977194619920040712988758680403184853549195737432064
  | 62 => 966134387952590413906467342765721610332562858466757057484879875113869841993787890340458519785367210831575586578088035411762932619856526259360915358772481254869367275913729
  | 63 => 967077871374579077224696642985224424610896605392596243596705053230130760614002981807029096378650894772271515541764391598796363562184075828953981462184275220827621877351425
  | _ => 0

def columnCode (i : Fin 64) : ℕ :=
  match i.val with
  | 0 => 483070875887337782873395784759643914393704702269183687762260242570404976403541139149887586180870378552698129219147763127487919764841926118548473582711815443198084038787585
  | 1 => 3685510180489786476798393145496356338786055879312930105836138965083617346086082863365358130056307390177215209990980317284932211552660930307714078288741285414102368770
  | 2 => 947176116385875124537187038392563579068016360983423037199887714026489657944123295884897039424470999275544308967681941542227578369033859414234274481950232181352349827073
  | 3 => 26815615859885194199148049996411692254958731641184786755447122887443528060147093953603748596333806855380063716417573592104893532936507822548969923423503360
  | 4 => 3599131035634557106248430806148785487095757694641533306480604458089470064537190296255232548883112685719936728506816716143168103242105724381953011514979210693181441
  | 5 => 390218568789499028922699653724145788218574767833121393857394619953171467352470702515038262882936496417279111589031603384852561669680773633934338
  | 6 => 7029552803973744348141466418259346654483901747346744739219930582205996219799199797373501072037329464296751422864876443231503313423260889093038124990531226305026
  | 7 => 13729595320261219429963801598162786434538870600286610818788926918371086366795312104245119281322909109954592622782984016819443156928570685195978943118520091136
  | 8 => 11090678776483259438313656736572334813745748301503266300681918322458485231222502492159942225906955374272149095484068452558285308929
  | 9 => 42307582002575910332922579714097346549017899709713998034217522897561970639123926155112854666673670265157535858932688044949504
  | 10 => 52374249726338269920211035149241586435466272736689036631732661889538140742474792878132321477214466514414186968341706335328405244549588758933866708730882
  | 11 => 102293456496754433437912178025862473506770063938845774671352855253004181137646079840102190385184504910965253480476649604804118772673977894130453316096
  | 12 => 199791907220223502808422222706762643567910281130558153654986045416023791284464999687699590596063486154251224336968554488452624031833142322180129794
  | 13 => 4586997231980143023221641790604173881593129978336562247475177678773845752501490645678551627171316126188544
  | 14 => 17498005798264095394980017816940970922825355447145699491406164851279949148452273310795916973837385729
  | 15 => 762145642166990290864647761179972242614403843424065222377723867096038022172794340849684107193235389122932519241578243298449037798471324664320
  | 16 => 130370302485407109521180524058200202307293977194619920040712988758682821054939557849741656577
  | 17 => 1488565707357402911845015158554633286356257506687627387456491927921949262056238946972039271861810083013640174875250548204722273184280216064
  | 18 => 2907354897182427562197295231552018137414565442749272241125960796722557152453591693304764202855054262243375241279903340369755035247051777
  | 19 => 5678427533559428832416592249125035424637823130369672345949142181098744438385921275985867583701277855944726093429647674899403338940930
  | 20 => 14134776518227074636666380005965648871818726319178448471772125842515165698
  | 21 => 21661481985318866090456360813617841433097164651373566993519371723551728967231450179999800047689240127296793178147223197251011072
  | 22 => 205688069665150755313972638217379730340948238956990524941140992
  | 23 => 784637716923379696969871064300863107732745085298797445121
  | 24 => 82631996098781074868989413504096379978550585370535152410581099409300723904538918228148651305598238323923878805240195055617
  | 25 => 5846006549323611673448569471414115163232878460930
  | 26 => 161390617380431786853494948250188242145606612051826469551916209783790476376052574664352835215074281932963003664842096642
  | 27 => 315216049571155833698232320801148910440637914163723573343586347233965774194278430090169906799940919898230931217973760
  | 28 => 166802539056316156950564940820774914
  | 29 => 615656346818663737691860001564743965704370926101022604186692084441339402679643916453653908517003370802859139400193
  | 30 => 1202453802380202612679414065556140558016349465041059773802132977424535622349076584300939743815290491717558468608
  | 31 => 2348542582773833227889480596789337027375682548908319870707290971576810515512319996982994891555988919799514114
  | 32 => 325152383798966504475011036742656
  | 33 => 8958978968711216842229769122273777112486581988938598139599956403855167810509328760682681859813001920514
  | 34 => 44601490397711553516873319165578457651610624
  | 35 => 44601490397711552281355872332619131230618114
  | 36 => 34175792574734561318320347298712833833643272357706444341453410924011292375764991291600578862384130
  | 37 => 66749594872528440074844428317798503581334516323645399060845050568964162869536674293103548433409
  | 38 => 649670932621689934820436221100033
  | 39 => 633827717984200674080679002625
  | 40 => 254629497041810760783555711051172270131433549252843521727227840802466426622973821692411905
  | 41 => 1267655435931507895335347290114
  | 42 => 497323236409786642155382248146820840100456195398838115151383673306790192761191287226368
  | 43 => 971334446112864535459730953411759453321203419526069761259736350140801710081397752833
  | 44 => 325154859683785870447968509756417
  | 45 => 1897137590064188545819787018382342682267975428762179519778558797931370943390680065
  | 46 => 3705346855594118253554271520278013095906129907012051570966961212480892111421953
  | 47 => 7237005577332262213973186563043038842319771428637503303071039591096394974210
  | 48 => 325787442198694241565065196078081
  | 49 => 325154854838619412279776249905154
  | 50 => 27606985387162255149739023449108101810129590743524897222784779645091841
  | 51 => 53919893334301279589334030174039261996311396171379331494258686296064
  | 52 => 105312291668557186697918027683670432953958340285539082437153259522
  | 53 => 650305995866565701384191678087168
  | 54 => 401734511064747568885490523734328995887443487392285149102592
  | 55 => 325154859679045057256278246556673
  | 56 => 650305998274981830984700792930818
  | 57 => 1532495540865888858358348297279207360504944938341892608
  | 58 => 2993155353253689177130184885082423592356608089260544
  | 59 => 1267650600228229436818782683138
  | 60 => 324521034374208576002360225039360
  | 61 => 11462583032045066083431920508897357550457978880
  | 62 => 43556142967147776350836551347760674111489
  | 63 => 85070916248793114718215376400575104002
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

private theorem literal_column_block_00 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (0+z.val)=
      digit i ⟨0+z.val,by omega⟩ := by
  decide +kernel

private theorem literal_column_block_01 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (8+z.val)=
      digit i ⟨8+z.val,by omega⟩ := by
  decide +kernel

private theorem literal_column_block_02 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (16+z.val)=
      digit i ⟨16+z.val,by omega⟩ := by
  decide +kernel

private theorem literal_column_block_03 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (24+z.val)=
      digit i ⟨24+z.val,by omega⟩ := by
  decide +kernel

private theorem literal_column_block_04 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (32+z.val)=
      digit i ⟨32+z.val,by omega⟩ := by
  decide +kernel

private theorem literal_column_block_05 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (40+z.val)=
      digit i ⟨40+z.val,by omega⟩ := by
  decide +kernel

private theorem literal_column_block_06 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (48+z.val)=
      digit i ⟨48+z.val,by omega⟩ := by
  decide +kernel

private theorem literal_column_block_07 :
    ∀ (z : Fin 8) (i : Fin 64),rawDigit rows2 i.val (56+z.val)=
      digit i ⟨56+z.val,by omega⟩ := by
  decide +kernel

theorem literal_column_binding (j i : Fin 64) :
    rawDigit rows2 i.val j.val=digit i j := by
  by_cases h00 : j.val<8
  · let z : Fin 8 := ⟨j.val-0,by omega⟩
    have he : 0+z.val=j.val := by dsimp [z]; omega
    have hh := literal_column_block_00 z i
    simpa only [he,Fin.eta] using hh
  by_cases h01 : j.val<16
  · let z : Fin 8 := ⟨j.val-8,by omega⟩
    have he : 8+z.val=j.val := by dsimp [z]; omega
    have hh := literal_column_block_01 z i
    simpa only [he,Fin.eta] using hh
  by_cases h02 : j.val<24
  · let z : Fin 8 := ⟨j.val-16,by omega⟩
    have he : 16+z.val=j.val := by dsimp [z]; omega
    have hh := literal_column_block_02 z i
    simpa only [he,Fin.eta] using hh
  by_cases h03 : j.val<32
  · let z : Fin 8 := ⟨j.val-24,by omega⟩
    have he : 24+z.val=j.val := by dsimp [z]; omega
    have hh := literal_column_block_03 z i
    simpa only [he,Fin.eta] using hh
  by_cases h04 : j.val<40
  · let z : Fin 8 := ⟨j.val-32,by omega⟩
    have he : 32+z.val=j.val := by dsimp [z]; omega
    have hh := literal_column_block_04 z i
    simpa only [he,Fin.eta] using hh
  by_cases h05 : j.val<48
  · let z : Fin 8 := ⟨j.val-40,by omega⟩
    have he : 40+z.val=j.val := by dsimp [z]; omega
    have hh := literal_column_block_05 z i
    simpa only [he,Fin.eta] using hh
  by_cases h06 : j.val<56
  · let z : Fin 8 := ⟨j.val-48,by omega⟩
    have he : 48+z.val=j.val := by dsimp [z]; omega
    have hh := literal_column_block_06 z i
    simpa only [he,Fin.eta] using hh
  let z : Fin 8 := ⟨j.val-56,by omega⟩
  have he : 56+z.val=j.val := by dsimp [z]; omega
  have hh := literal_column_block_07 z i
  simpa only [he,Fin.eta] using hh

theorem literal_source_binding :
    CFSG.Models.MatrixData.matrix 3 64 rows2=data.matrix 3 := by
  ext i j
  change (rawDigit rows2 i.val j.val : ZMod 3)=(digit i j : ZMod 3)
  exact congrArg (fun z : ℕ => (z : ZMod 3)) (literal_column_binding j i)

end SymmetricSubgroupAsymptotics.CFSGSuzPackedBrayCacheB
