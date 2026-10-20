import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow27TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow27TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow27TopCertificate.ambient
def topRepresentative : Fin 33 → Source := PrimitiveAffineSixteenFrameRow27TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow27TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow27TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow27TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 61 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow27TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 61 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow27TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 61,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow27TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow27TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 61 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 61 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445607145448674080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636072142180 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8522270792435480970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441558094781092400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3603289158257064090 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7238934962662547760 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468314856592346010 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11208016700206559520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721306558411280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7445629005949017000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7445629006266546570 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531480116623899885 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12157976127921795360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459166223564415280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378229401535893470 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18297129491811148560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701378097680 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996023258868415950 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714808103440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12149306830704922365 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613160526210165 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1162867995727141560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306394160383805015 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311302392485437135 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946949744215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9987837171964588320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311269535231638765 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (221500999984261560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378229401287188175 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920133061863609120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086204348217365040 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229770992864675415 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (157985963896463055 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938491900195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1162867995977820555 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849648592710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9987837171680482050 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311302391731441630 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2526647372088125835 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (157985963647750110 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938744550145 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13369500854745623775 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2526647372338797240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311302392232803565 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221884843561730 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059598922709616215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920118566127808770 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531480117125238750 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (157985964149112045 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258224378625 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903524962595 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 61) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 61) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 61) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 61) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow27TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow27TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow27TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow27TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow27TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 61) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 61) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 61 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 7 then 6
    else if x.index.val = 9 then 7
    else if x.index.val = 11 then 8
    else if x.index.val = 24 then 9
    else if x.index.val = 39 then 10
    else if x.index.val = 48 then 11
    else if x.index.val = 64 then 12
    else if x.index.val = 84 then 13
    else if x.index.val = 117 then 14
    else if x.index.val = 121 then 15
    else if x.index.val = 129 then 16
    else if x.index.val = 144 then 17
    else if x.index.val = 191 then 18
    else if x.index.val = 228 then 19
    else if x.index.val = 250 then 20
    else if x.index.val = 414 then 21
    else if x.index.val = 433 then 22
    else if x.index.val = 487 then 23
    else if x.index.val = 502 then 24
    else if x.index.val = 510 then 25
    else if x.index.val = 518 then 26
    else if x.index.val = 538 then 27
    else if x.index.val = 547 then 28
    else if x.index.val = 583 then 29
    else if x.index.val = 618 then 30
    else if x.index.val = 621 then 31
    else if x.index.val = 629 then 32
    else if x.index.val = 664 then 33
    else if x.index.val = 693 then 34
    else if x.index.val = 771 then 35
    else if x.index.val = 781 then 36
    else if x.index.val = 795 then 37
    else if x.index.val = 816 then 38
    else if x.index.val = 817 then 39
    else if x.index.val = 825 then 40
    else if x.index.val = 827 then 41
    else if x.index.val = 840 then 42
    else if x.index.val = 863 then 43
    else if x.index.val = 867 then 44
    else if x.index.val = 993 then 45
    else if x.index.val = 1000 then 46
    else if x.index.val = 1011 then 47
    else if x.index.val = 1074 then 48
    else if x.index.val = 1075 then 49
    else if x.index.val = 1085 then 50
    else if x.index.val = 1110 then 51
    else if x.index.val = 1141 then 52
    else if x.index.val = 1218 then 53
    else if x.index.val = 1252 then 54
    else if x.index.val = 1291 then 55
    else if x.index.val = 1332 then 56
    else if x.index.val = 1338 then 57
    else if x.index.val = 1494 then 58
    else if x.index.val = 1534 then 59
    else if x.index.val = 1535 then 60
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 61,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 61) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 9 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state0Used : Fin 9 → Fin 61 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state1Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state1Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state2Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨629⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state2Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state3Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨24⟩ : Source)) (Fin.cases ((⟨629⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state3Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (9) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state4Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨664⟩ : Source)) (Fin.cases ((⟨547⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state4Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (33) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state5Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨827⟩ : Source)) (Fin.cases ((⟨817⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state5Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (41) (Fin.cases (39) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state6Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨629⟩ : Source)) (Fin.cases ((⟨664⟩ : Source)) (Fin.cases ((⟨547⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state6Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (32) (Fin.cases (33) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state7Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨629⟩ : Source)) (Fin.cases ((⟨827⟩ : Source)) (Fin.cases ((⟨817⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state7Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (32) (Fin.cases (41) (Fin.cases (39) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state8Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨84⟩ : Source)) (Fin.cases ((⟨1291⟩ : Source)) (Fin.cases ((⟨618⟩ : Source)) (Fin.cases ((⟨867⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state8Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (13) (Fin.cases (55) (Fin.cases (30) (Fin.cases (44) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state9Generators : Fin 9 → Source :=
  (Fin.cases ((⟨840⟩ : Source)) (Fin.cases ((⟨825⟩ : Source)) (Fin.cases ((⟨1141⟩ : Source)) (Fin.cases ((⟨64⟩ : Source)) (Fin.cases ((⟨502⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state9Used : Fin 9 → Fin 61 :=
  (Fin.cases (42) (Fin.cases (40) (Fin.cases (52) (Fin.cases (12) (Fin.cases (24) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state10Generators : Fin 9 → Source :=
  (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨816⟩ : Source)) (Fin.cases ((⟨693⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state10Used : Fin 9 → Fin 61 :=
  (Fin.cases (19) (Fin.cases (20) (Fin.cases (38) (Fin.cases (34) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state11Generators : Fin 9 → Source :=
  (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨816⟩ : Source)) (Fin.cases ((⟨693⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state11Used : Fin 9 → Fin 61 :=
  (Fin.cases (19) (Fin.cases (20) (Fin.cases (38) (Fin.cases (34) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state12Generators : Fin 9 → Source :=
  (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨816⟩ : Source)) (Fin.cases ((⟨693⟩ : Source)) (Fin.cases ((⟨433⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state12Used : Fin 9 → Fin 61 :=
  (Fin.cases (19) (Fin.cases (20) (Fin.cases (38) (Fin.cases (34) (Fin.cases (22) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state13Generators : Fin 9 → Source :=
  (Fin.cases ((⟨518⟩ : Source)) (Fin.cases ((⟨538⟩ : Source)) (Fin.cases ((⟨693⟩ : Source)) (Fin.cases ((⟨781⟩ : Source)) (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state13Used : Fin 9 → Fin 61 :=
  (Fin.cases (26) (Fin.cases (27) (Fin.cases (34) (Fin.cases (36) (Fin.cases (20) (Fin.cases (19) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state14Generators : Fin 9 → Source :=
  (Fin.cases ((⟨518⟩ : Source)) (Fin.cases ((⟨538⟩ : Source)) (Fin.cases ((⟨693⟩ : Source)) (Fin.cases ((⟨781⟩ : Source)) (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state14Used : Fin 9 → Fin 61 :=
  (Fin.cases (26) (Fin.cases (27) (Fin.cases (34) (Fin.cases (36) (Fin.cases (20) (Fin.cases (19) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state15Generators : Fin 9 → Source :=
  (Fin.cases ((⟨518⟩ : Source)) (Fin.cases ((⟨538⟩ : Source)) (Fin.cases ((⟨693⟩ : Source)) (Fin.cases ((⟨781⟩ : Source)) (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨433⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state15Used : Fin 9 → Fin 61 :=
  (Fin.cases (26) (Fin.cases (27) (Fin.cases (34) (Fin.cases (36) (Fin.cases (20) (Fin.cases (19) (Fin.cases (22) (Fin.cases (11) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state16Generators : Fin 9 → Source :=
  (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨771⟩ : Source)) (Fin.cases ((⟨1332⟩ : Source)) (Fin.cases ((⟨547⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state16Used : Fin 9 → Fin 61 :=
  (Fin.cases (20) (Fin.cases (19) (Fin.cases (35) (Fin.cases (56) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state17Generators : Fin 9 → Source :=
  (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨771⟩ : Source)) (Fin.cases ((⟨1332⟩ : Source)) (Fin.cases ((⟨547⟩ : Source)) (Fin.cases ((⟨1535⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state17Used : Fin 9 → Fin 61 :=
  (Fin.cases (20) (Fin.cases (19) (Fin.cases (35) (Fin.cases (56) (Fin.cases (28) (Fin.cases (60) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state18Generators : Fin 9 → Source :=
  (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨771⟩ : Source)) (Fin.cases ((⟨1332⟩ : Source)) (Fin.cases ((⟨547⟩ : Source)) (Fin.cases ((⟨1535⟩ : Source)) (Fin.cases ((⟨795⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state18Used : Fin 9 → Fin 61 :=
  (Fin.cases (20) (Fin.cases (19) (Fin.cases (35) (Fin.cases (56) (Fin.cases (28) (Fin.cases (60) (Fin.cases (37) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state19Generators : Fin 9 → Source :=
  (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (Fin.cases ((⟨771⟩ : Source)) (Fin.cases ((⟨1332⟩ : Source)) (Fin.cases ((⟨547⟩ : Source)) (Fin.cases ((⟨1535⟩ : Source)) (Fin.cases ((⟨433⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state19Used : Fin 9 → Fin 61 :=
  (Fin.cases (20) (Fin.cases (19) (Fin.cases (35) (Fin.cases (56) (Fin.cases (28) (Fin.cases (60) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state20Generators : Fin 9 → Source :=
  (Fin.cases ((⟨1218⟩ : Source)) (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨1085⟩ : Source)) (Fin.cases ((⟨518⟩ : Source)) (Fin.cases ((⟨538⟩ : Source)) (Fin.cases ((⟨693⟩ : Source)) (Fin.cases ((⟨781⟩ : Source)) (Fin.cases ((⟨250⟩ : Source)) (Fin.cases ((⟨228⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state20Used : Fin 9 → Fin 61 :=
  (Fin.cases (53) (Fin.cases (1) (Fin.cases (50) (Fin.cases (26) (Fin.cases (27) (Fin.cases (34) (Fin.cases (36) (Fin.cases (20) (Fin.cases (19) (fun i => Fin.elim0 i))))))))))

private def state21Generators : Fin 9 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state21Used : Fin 9 → Fin 61 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

def stateGenerators : Fin 22 → Fin 9 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (Fin.cases (state14Generators) (Fin.cases (state15Generators) (Fin.cases (state16Generators) (Fin.cases (state17Generators) (Fin.cases (state18Generators) (Fin.cases (state19Generators) (Fin.cases (state20Generators) (Fin.cases (state21Generators) (fun i => Fin.elim0 i)))))))))))))))))))))))

def stateUsed : Fin 22 → Fin 9 → Fin 61 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (Fin.cases (state14Used) (Fin.cases (state15Used) (Fin.cases (state16Used) (Fin.cases (state17Used) (Fin.cases (state18Used) (Fin.cases (state19Used) (Fin.cases (state20Used) (Fin.cases (state21Used) (fun i => Fin.elim0 i)))))))))))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 22) (k : Fin 9),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 33 → Fin 61 :=
  (Fin.cases (0) (Fin.cases (19) (Fin.cases (38) (Fin.cases (27) (Fin.cases (41) (Fin.cases (33) (Fin.cases (50) (Fin.cases (1) (Fin.cases (15) (Fin.cases (45) (Fin.cases (43) (Fin.cases (47) (Fin.cases (53) (Fin.cases (32) (Fin.cases (59) (Fin.cases (52) (Fin.cases (58) (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (9) (Fin.cases (49) (Fin.cases (46) (Fin.cases (48) (Fin.cases (17) (Fin.cases (57) (Fin.cases (21) (Fin.cases (31) (Fin.cases (29) (Fin.cases (10) (Fin.cases (54) (Fin.cases (25) (Fin.cases (51) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 33,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 61 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 22 → Fin 33 → Fin 22 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (10) (Fin.cases (1) (Fin.cases (13) (Fin.cases (5) (Fin.cases (4) (Fin.cases (16) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (11) (Fin.cases (2) (Fin.cases (11) (Fin.cases (7) (Fin.cases (14) (Fin.cases (6) (Fin.cases (17) (Fin.cases (12) (Fin.cases (3) (Fin.cases (12) (Fin.cases (15) (Fin.cases (8) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (10) (Fin.cases (1) (Fin.cases (13) (Fin.cases (5) (Fin.cases (4) (Fin.cases (16) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (11) (Fin.cases (2) (Fin.cases (11) (Fin.cases (7) (Fin.cases (14) (Fin.cases (6) (Fin.cases (17) (Fin.cases (12) (Fin.cases (3) (Fin.cases (12) (Fin.cases (15) (Fin.cases (8) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (11) (Fin.cases (2) (Fin.cases (14) (Fin.cases (7) (Fin.cases (6) (Fin.cases (17) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (11) (Fin.cases (2) (Fin.cases (11) (Fin.cases (7) (Fin.cases (14) (Fin.cases (6) (Fin.cases (17) (Fin.cases (12) (Fin.cases (3) (Fin.cases (12) (Fin.cases (15) (Fin.cases (8) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (12) (Fin.cases (3) (Fin.cases (15) (Fin.cases (9) (Fin.cases (8) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (12) (Fin.cases (3) (Fin.cases (12) (Fin.cases (9) (Fin.cases (15) (Fin.cases (8) (Fin.cases (19) (Fin.cases (12) (Fin.cases (3) (Fin.cases (12) (Fin.cases (15) (Fin.cases (8) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (13) (Fin.cases (4) (Fin.cases (13) (Fin.cases (13) (Fin.cases (4) (Fin.cases (16) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (14) (Fin.cases (6) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (6) (Fin.cases (17) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (13) (Fin.cases (5) (Fin.cases (13) (Fin.cases (5) (Fin.cases (13) (Fin.cases (16) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (14) (Fin.cases (6) (Fin.cases (14) (Fin.cases (14) (Fin.cases (6) (Fin.cases (17) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (14) (Fin.cases (6) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (6) (Fin.cases (17) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (17) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (8) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (8) (Fin.cases (19) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (8) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (9) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (16) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (16) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (17) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (19) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (17) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (Fin.cases (18) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (19) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (20) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (Fin.cases (21) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))) (fun i => Fin.elim0 i)))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow27NormalCore

end
