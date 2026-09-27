import SymmetricSubgroupAsymptotics.FiniteCayleyGroup
import SymmetricSubgroupAsymptotics.FinitePermutationEncoding
import Mathlib.Order.Fin.Basic

/-!
# Literal c=1 high action certificate 12T85

Generated from certificates/data/primitive_rank.jsonl.gz by export_lean_c1_degree_twelve.py.
Selected transitive row 259; raw-line SHA256 f5ec93ecd97c47c3abdcce787d1c381e1cc77b7df45b30328ad02eb7ec3fd54a.
All finite equations use Lean's kernel. BFS parents establish actual group
membership; numeric permutation codes establish faithfulness. This proves the literal selected action only;
high-pair coverage and earlier-owner acceptance remain separate theorems.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section

namespace SymmetricSubgroupAsymptotics.TernaryOwnerCayley12T85

private def generator0 : Equiv.Perm (Fin 12) where
  toFun x := (#[9,1,11,6,4,8,3,7,5,0,10,2] : Array (Fin 12))[x.val]!
  invFun x := (#[9,1,11,6,4,8,3,7,5,0,10,2] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator1 : Equiv.Perm (Fin 12) where
  toFun x := (#[6,4,5,3,10,8,9,7,2,0,1,11] : Array (Fin 12))[x.val]!
  invFun x := (#[9,10,8,3,1,2,0,7,5,6,4,11] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generator2 : Equiv.Perm (Fin 12) where
  toFun x := (#[4,5,6,7,8,9,10,11,0,1,2,3] : Array (Fin 12))[x.val]!
  invFun x := (#[8,9,10,11,0,1,2,3,4,5,6,7] : Array (Fin 12))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def generators (j : Fin 3) : Equiv.Perm (Fin 12) :=
  (if j.val < 1 then generator0 else (if j.val < 2 then generator1 else generator2))

private def codes (i : Fin 144) : Fin (12^12) :=
  Fin.ofNat 8916100448256 (((if (i.val) / 32 < 2 then (if (i.val) / 32 < 1 then 780996724990344441779583312134080270323564399056800859541441082340225949982494745562585573369309405105738226536314084185332940139291549786041205412640538988703993231220585997101504004202969103256222715489430127363260830823185044077580794639195529199980250302730117577430753129506134044060575183217187928217693707332329588155588970232827038569355635414849578440336824681067661555662427758522322283450718877195731511443831854 else 1597549092821921152983445465702373981496382343270036756037690572761185989058286044819319538252957343888844295433852662245030383487872750240902431267486568191315044036432002903194539770256673207382145266355287148484801855890157275363299892334998061902707348697142105749246032366916921726021404307743277178819406911272568542434244231289252982959795701535760395565616023331009199911794859603004897859164946881369954441415666592) else (if (i.val) / 32 < 3 then 2341632212501994675865418378492405889221313553085582559589722330284698328789394943064451261214013593791492507230177372762770197719093768365298132182417654701517818275988233189307853354328109972329563753286375629334408575821573656779567360681562713927000671832306807775279975652257302727408915701233456759870828677860699274337760812979737949503755398468305106342855303076405901444962537669989070084714701174753914172685333829 else (if (i.val) / 32 < 4 then 3152434778162208562288107716492274897134220225203932233272859156089178307113506917158065925845203462756184232216511701747956757081800535011652874288399597232963701485059121318286575994504691333679186287579806042500153041963150420012208837957554428764501560570222965616416932504306127313609322596543206896787602924363438383797794678403172788347413802596553314008895407288939164813028477883681733181357409660099700096465331015 else 42302688225182784902994839727534837896676450122557771037508100234938696581425479366129367489705569655546020868023655257169012236591437405305932329970256173887878793892696626163911630755599978871396814930765001185))) : ℕ) / 2 ^ (44 * ((i.val) % 32)) % 2 ^ 44)
private def ranks (i : Fin 144) : ℕ :=
  (((if (i.val) / 32 < 2 then (if (i.val) / 32 < 1 then 38200200116627451092654015189930478056113016706774569563381167185852832373529 else 7479108791049466456846030878620530950382856404069031136545158422307475882286) else (if (i.val) / 32 < 3 then 22653396281869954998052470273386462551566431761944924994616664601600457082989 else (if (i.val) / 32 < 4 then 45869975702905754867017151214491940711418181595507342947441280184997684513671 else 552459979014551080502660987452475416))) : ℕ) / 2 ^ (8 * ((i.val) % 32)) % 2 ^ 8)
private def parents (i : Fin 144) : Fin 144 :=
  Fin.ofNat 144 (((if (i.val) / 32 < 2 then (if (i.val) / 32 < 1 then 8693047013538610120486965359867118922798134178856134538582500255514713531745 else 27705074448849698562180464157717811499229152218410008081428439662147004567424) else (if (i.val) / 32 < 3 then 34897017093276201123757736631315907589262939017406198871847373360498761602185 else (if (i.val) / 32 < 4 then 8239167219932129832556010860515639507482552766812021721753890356590772886143 else 190365548853572571177512078337711820634))) : ℕ) / 2 ^ (8 * ((i.val) % 32)) % 2 ^ 8)
private def letters (i : Fin 144) : Fin 3 :=
  Fin.ofNat 3 (((if (i.val) / 32 < 2 then (if (i.val) / 32 < 1 then 12221240699337834898 else 5911703074855294626) else (if (i.val) / 32 < 3 then 12297829033483216552 else (if (i.val) / 32 < 4 then 42863774241824930 else 715762072))) : ℕ) / 2 ^ (2 * ((i.val) % 32)) % 2 ^ 2)
private def nextRow (i : Fin 144) (j : Fin 3) : Fin 144 :=
  Fin.ofNat 144 (((if (i.val * 3 + j.val) / 32 < 7 then (if (i.val * 3 + j.val) / 32 < 3 then (if (i.val * 3 + j.val) / 32 < 1 then 3829627245123144396111512288174612050622854463506719350163169271385761254218 else (if (i.val * 3 + j.val) / 32 < 2 then 42632399221819861276261191323841856477615441129000807846659540563389703204119 else 3681063212662594299545596127683354451353551301180586309803435320590894973453)) else (if (i.val * 3 + j.val) / 32 < 5 then (if (i.val * 3 + j.val) / 32 < 4 then 18297841929679644161709678441290648626132678288344546332148998465082983586698 else 6845155411507525394222159239750532107771194216394012169320712856313323802754) else (if (i.val * 3 + j.val) / 32 < 6 then 49876519074658376690141646748842582011109266493951646568673798633955316218928 else 37090504524439730685971992617387992539123069699710873337065096953176967954057))) else (if (i.val * 3 + j.val) / 32 < 10 then (if (i.val * 3 + j.val) / 32 < 8 then 6573293564268811231708099094574354732553078556020584800670658129629618832654 else (if (i.val * 3 + j.val) / 32 < 9 then 12822413017952852918540383817368313007814760048311661127587568924289551309407 else 45028362492724039679547225956414515254345695867928398401042721659731846784645)) else (if (i.val * 3 + j.val) / 32 < 12 then (if (i.val * 3 + j.val) / 32 < 11 then 21351347158884838751618629835499138371686250040945667797287441032815784838482 else 43634181081719319678019863538175338776459166031830747075805591442917306816366) else (if (i.val * 3 + j.val) / 32 < 13 then 62023920585387637174743019920480467244902915474717641928894506811514366755418 else 48538260792655582426225627762149638729)))) : ℕ) / 2 ^ (8 * ((i.val * 3 + j.val) % 32)) % 2 ^ 8)
private def prevRow (i : Fin 144) (j : Fin 3) : Fin 144 :=
  Fin.ofNat 144 (((if (i.val * 3 + j.val) / 32 < 7 then (if (i.val * 3 + j.val) / 32 < 3 then (if (i.val * 3 + j.val) / 32 < 1 then 2019948104281203984321941009748142354791747402723488492603323920666956202826 else (if (i.val * 3 + j.val) / 32 < 2 then 42593473370004247881852648806027868148868863531231018956686847176290737335581 else 8645901982945931404379749012459698395861292135575270106675430401648567070484)) else (if (i.val * 3 + j.val) / 32 < 5 then (if (i.val * 3 + j.val) / 32 < 4 then 21012022886698218034474523920157728896528268573237813428885568732724673386890 else 6989995446228602926422664289015738291896930215132918361957123818546398580763) else (if (i.val * 3 + j.val) / 32 < 6 then 41268443490710230958784982381900806228312112851676124954976653169667201060922 else 34376731066978828088000655842064180178129545096820637781596963843754594026633))) else (if (i.val * 3 + j.val) / 32 < 10 then (if (i.val * 3 + j.val) / 32 < 8 then 6410771243720061280360528131290536364858572401537102014941697434115488941416 else (if (i.val * 3 + j.val) / 32 < 9 then 34978672703630458969842477933078178013069369131025689633503748390935697313369 else 47290071537489227070672806203422959558685892156465253275564642186463547450501)) else (if (i.val * 3 + j.val) / 32 < 12 then (if (i.val * 3 + j.val) / 32 < 11 then 21319599138644659431103962137262329800694821551624979252633280356019058590998 else 53593896503815204303834420563935652872867616380528364819709734540099609312626) else (if (i.val * 3 + j.val) / 32 < 13 then 60214986806202694689813628026242902748074548804548562633636680308649215556186 else 120337345712025936532084953375123653243)))) : ℕ) / 2 ^ (8 * ((i.val * 3 + j.val) % 32)) % 2 ^ 8)

private theorem parent_lt_checked : ∀ i : Fin 144,
    i ≠ 143 → ranks (parents i) < ranks i := (Fin.addCases (m := 72) (n := 72) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))))
private theorem parent_next_checked : ∀ i : Fin 144,
    i ≠ 143 → nextRow (parents i) (letters i) = i := (Fin.addCases (m := 72) (n := 72) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))))

def certificate : EncodedCayleyCertificate
    (permutationGeneratorEncoding generators) 144 where
  rows := codes
  identity := 143
  identity_eq := by decide +kernel
  next := nextRow
  next_eq := (Fin.addCases (m := 72) (n := 72) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))))
  rank := ranks
  parent i _ := parents i
  letter i _ := letters i
  parent_lt := parent_lt_checked
  parent_next := parent_next_checked

private theorem codes_strict : StrictMono codes :=
  Fin.strictMono_iff_lt_succ.mpr (Fin.addCases (m := 71) (n := 72) (Fin.addCases (m := 35) (n := 36) (Fin.addCases (m := 17) (n := 18) (Fin.addCases (m := 8) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))))

theorem rows_injective : Function.Injective certificate.rows := codes_strict.injective

theorem exact_card : Nat.card (Subgroup.closure (Set.range generators)) = 144 :=
  certificate.card_closure rows_injective

private theorem prev_checked : ∀ i j, certificate.next (prevRow i j) j = i :=
  (Fin.addCases (m := 72) (n := 72) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 36) (n := 36) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 18) (n := 18) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 9) (n := 9) (by decide +kernel) (by decide +kernel)))))

/-- Executable multiplication and inverse, with laws proved by faithfulness. -/
@[reducible] def group : Group (FiniteGroupRow 144) :=
  certificate.rowGroup rows_injective prevRow prev_checked

/-- Exact identification with the original literal permutation subgroup. -/
def originalEquiv : letI := group
    FiniteGroupRow 144 ≃* Subgroup.closure (Set.range generators) :=
  certificate.rowEquiv rows_injective prevRow prev_checked

/-- Exact one-based image lists bind the selected original source tuple. -/
theorem sourceGenerator_images : ∀ j : Fin 3, ∀ x : Fin 12,
    (generators j x).val + 1 =
      ((#[#[10,2,12,7,5,9,4,8,6,1,11,3],#[7,5,6,4,11,9,10,8,3,1,2,12],#[5,6,7,8,9,10,11,12,1,2,3,4]] : Array (Array ℕ))[j.val]!)[x.val]! := by
  decide +kernel

end SymmetricSubgroupAsymptotics.TernaryOwnerCayley12T85
