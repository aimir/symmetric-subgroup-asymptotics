import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow29TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow29TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow29TopCertificate.ambient
def topRepresentative : Fin 44 → Source := PrimitiveAffineSixteenFrameRow29TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow29TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow29TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow29TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 84 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow29TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 84 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow29TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 84,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow29TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow29TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 84 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 84 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12158009242403746080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445625764131902240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636072142180 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8522270792435480970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666726715920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086237463236055600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16067869003347949140 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (86242896007510170 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459166224069697840 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18288610184228595540 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468331284842253210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11208016700490658080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17076898230972195600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18225353306602051770 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271907029520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3463984622817566460 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306394160889091910 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2378931444346511100 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3607586341253830260 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11000940532048098630 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9924280127446611270 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714808103440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2378915144696913660 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370496159035920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257444880 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1167148750724683380 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12364653680013374790 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986825941520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311269535231638765 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741987141493505 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758543924863745 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758543672213795 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701946290945 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (225647872261283580 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378229401034554605 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370495843471410 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531480116623899885 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721306558411280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758543672226320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758544493052195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (82079143755011700 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267904093168385 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229752374970832710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13441276847248405830 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1310750464579788540 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666158514945 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939060105985 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311318949331729645 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (225647872008642300 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531496416273497325 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509020840705 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158002520995396845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370495843480080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758544240423440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986825932850 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951606362640 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986573296385 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2378931444599152380 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2522483877784344180 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284460939457040 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158018819894934765 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158035376993860845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1310701051482398460 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271654388240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284461192098320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (225631573361745660 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951921918480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618713987261185 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758544493056050 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370496411673345 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509020844560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509020835890 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938491900195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714239906320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903524962595 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1310701051229757180 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938744550145 : Fin (16 ^ 16))) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 84) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 84) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 84) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 84) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow29TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow29TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow29TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow29TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow29TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 84) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 84) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 84 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 6 then 6
    else if x.index.val = 7 then 7
    else if x.index.val = 8 then 8
    else if x.index.val = 10 then 9
    else if x.index.val = 11 then 10
    else if x.index.val = 12 then 11
    else if x.index.val = 18 then 12
    else if x.index.val = 23 then 13
    else if x.index.val = 37 then 14
    else if x.index.val = 107 then 15
    else if x.index.val = 145 then 16
    else if x.index.val = 158 then 17
    else if x.index.val = 293 then 18
    else if x.index.val = 343 then 19
    else if x.index.val = 381 then 20
    else if x.index.val = 479 then 21
    else if x.index.val = 619 then 22
    else if x.index.val = 698 then 23
    else if x.index.val = 704 then 24
    else if x.index.val = 711 then 25
    else if x.index.val = 749 then 26
    else if x.index.val = 791 then 27
    else if x.index.val = 816 then 28
    else if x.index.val = 885 then 29
    else if x.index.val = 1014 then 30
    else if x.index.val = 1055 then 31
    else if x.index.val = 1095 then 32
    else if x.index.val = 1274 then 33
    else if x.index.val = 1296 then 34
    else if x.index.val = 1301 then 35
    else if x.index.val = 1364 then 36
    else if x.index.val = 1371 then 37
    else if x.index.val = 1499 then 38
    else if x.index.val = 1517 then 39
    else if x.index.val = 1536 then 40
    else if x.index.val = 1537 then 41
    else if x.index.val = 1564 then 42
    else if x.index.val = 1652 then 43
    else if x.index.val = 1873 then 44
    else if x.index.val = 1913 then 45
    else if x.index.val = 1953 then 46
    else if x.index.val = 1958 then 47
    else if x.index.val = 2108 then 48
    else if x.index.val = 2232 then 49
    else if x.index.val = 2332 then 50
    else if x.index.val = 2605 then 51
    else if x.index.val = 2668 then 52
    else if x.index.val = 2671 then 53
    else if x.index.val = 2893 then 54
    else if x.index.val = 2912 then 55
    else if x.index.val = 3022 then 56
    else if x.index.val = 3041 then 57
    else if x.index.val = 3074 then 58
    else if x.index.val = 3097 then 59
    else if x.index.val = 3595 then 60
    else if x.index.val = 3759 then 61
    else if x.index.val = 3891 then 62
    else if x.index.val = 3931 then 63
    else if x.index.val = 3958 then 64
    else if x.index.val = 4072 then 65
    else if x.index.val = 4287 then 66
    else if x.index.val = 4398 then 67
    else if x.index.val = 4425 then 68
    else if x.index.val = 4567 then 69
    else if x.index.val = 4986 then 70
    else if x.index.val = 4993 then 71
    else if x.index.val = 5021 then 72
    else if x.index.val = 5124 then 73
    else if x.index.val = 5303 then 74
    else if x.index.val = 5413 then 75
    else if x.index.val = 5677 then 76
    else if x.index.val = 5800 then 77
    else if x.index.val = 5836 then 78
    else if x.index.val = 5863 then 79
    else if x.index.val = 5923 then 80
    else if x.index.val = 5930 then 81
    else if x.index.val = 5998 then 82
    else if x.index.val = 6012 then 83
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 84,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 84) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 11 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state0Used : Fin 11 → Fin 84 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state1Generators : Fin 11 → Source :=
  (Fin.cases ((⟨5836⟩ : Source)) (Fin.cases ((⟨5863⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state1Used : Fin 11 → Fin 84 :=
  (Fin.cases (78) (Fin.cases (79) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state2Generators : Fin 11 → Source :=
  (Fin.cases ((⟨5836⟩ : Source)) (Fin.cases ((⟨5863⟩ : Source)) (Fin.cases ((⟨2912⟩ : Source)) (Fin.cases ((⟨107⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state2Used : Fin 11 → Fin 84 :=
  (Fin.cases (78) (Fin.cases (79) (Fin.cases (55) (Fin.cases (15) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state3Generators : Fin 11 → Source :=
  (Fin.cases ((⟨5836⟩ : Source)) (Fin.cases ((⟨1517⟩ : Source)) (Fin.cases ((⟨1274⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state3Used : Fin 11 → Fin 84 :=
  (Fin.cases (78) (Fin.cases (39) (Fin.cases (33) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state4Generators : Fin 11 → Source :=
  (Fin.cases ((⟨5836⟩ : Source)) (Fin.cases ((⟨1517⟩ : Source)) (Fin.cases ((⟨1274⟩ : Source)) (Fin.cases ((⟨3759⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state4Used : Fin 11 → Fin 84 :=
  (Fin.cases (78) (Fin.cases (39) (Fin.cases (33) (Fin.cases (61) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state5Generators : Fin 11 → Source :=
  (Fin.cases ((⟨5836⟩ : Source)) (Fin.cases ((⟨1095⟩ : Source)) (Fin.cases ((⟨1537⟩ : Source)) (Fin.cases ((⟨1301⟩ : Source)) (Fin.cases ((⟨3595⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state5Used : Fin 11 → Fin 84 :=
  (Fin.cases (78) (Fin.cases (32) (Fin.cases (41) (Fin.cases (35) (Fin.cases (60) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state6Generators : Fin 11 → Source :=
  (Fin.cases ((⟨6012⟩ : Source)) (Fin.cases ((⟨1095⟩ : Source)) (Fin.cases ((⟨3759⟩ : Source)) (Fin.cases ((⟨1301⟩ : Source)) (Fin.cases ((⟨704⟩ : Source)) (Fin.cases ((⟨3595⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state6Used : Fin 11 → Fin 84 :=
  (Fin.cases (83) (Fin.cases (32) (Fin.cases (61) (Fin.cases (35) (Fin.cases (24) (Fin.cases (60) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state7Generators : Fin 11 → Source :=
  (Fin.cases ((⟨6012⟩ : Source)) (Fin.cases ((⟨1095⟩ : Source)) (Fin.cases ((⟨3759⟩ : Source)) (Fin.cases ((⟨1301⟩ : Source)) (Fin.cases ((⟨704⟩ : Source)) (Fin.cases ((⟨3595⟩ : Source)) (Fin.cases ((⟨4398⟩ : Source)) (Fin.cases ((⟨1953⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state7Used : Fin 11 → Fin 84 :=
  (Fin.cases (83) (Fin.cases (32) (Fin.cases (61) (Fin.cases (35) (Fin.cases (24) (Fin.cases (60) (Fin.cases (67) (Fin.cases (46) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state8Generators : Fin 11 → Source :=
  (Fin.cases ((⟨6012⟩ : Source)) (Fin.cases ((⟨1095⟩ : Source)) (Fin.cases ((⟨3759⟩ : Source)) (Fin.cases ((⟨1301⟩ : Source)) (Fin.cases ((⟨704⟩ : Source)) (Fin.cases ((⟨3595⟩ : Source)) (Fin.cases ((⟨1499⟩ : Source)) (Fin.cases ((⟨293⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state8Used : Fin 11 → Fin 84 :=
  (Fin.cases (83) (Fin.cases (32) (Fin.cases (61) (Fin.cases (35) (Fin.cases (24) (Fin.cases (60) (Fin.cases (38) (Fin.cases (18) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state9Generators : Fin 11 → Source :=
  (Fin.cases ((⟨3097⟩ : Source)) (Fin.cases ((⟨1564⟩ : Source)) (Fin.cases ((⟨5677⟩ : Source)) (Fin.cases ((⟨4072⟩ : Source)) (Fin.cases ((⟨5021⟩ : Source)) (Fin.cases ((⟨4567⟩ : Source)) (Fin.cases ((⟨3022⟩ : Source)) (Fin.cases ((⟨5800⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state9Used : Fin 11 → Fin 84 :=
  (Fin.cases (59) (Fin.cases (42) (Fin.cases (76) (Fin.cases (65) (Fin.cases (72) (Fin.cases (69) (Fin.cases (56) (Fin.cases (77) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state10Generators : Fin 11 → Source :=
  (Fin.cases ((⟨293⟩ : Source)) (Fin.cases ((⟨1499⟩ : Source)) (Fin.cases ((⟨5303⟩ : Source)) (Fin.cases ((⟨1652⟩ : Source)) (Fin.cases ((⟨5413⟩ : Source)) (Fin.cases ((⟨4986⟩ : Source)) (Fin.cases ((⟨749⟩ : Source)) (Fin.cases ((⟨3074⟩ : Source)) (Fin.cases ((⟨145⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state10Used : Fin 11 → Fin 84 :=
  (Fin.cases (18) (Fin.cases (38) (Fin.cases (74) (Fin.cases (43) (Fin.cases (75) (Fin.cases (70) (Fin.cases (26) (Fin.cases (58) (Fin.cases (16) (Fin.cases (5) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

private def state11Generators : Fin 11 → Source :=
  (Fin.cases ((⟨3958⟩ : Source)) (Fin.cases ((⟨293⟩ : Source)) (Fin.cases ((⟨1499⟩ : Source)) (Fin.cases ((⟨5303⟩ : Source)) (Fin.cases ((⟨1652⟩ : Source)) (Fin.cases ((⟨5413⟩ : Source)) (Fin.cases ((⟨4986⟩ : Source)) (Fin.cases ((⟨749⟩ : Source)) (Fin.cases ((⟨3074⟩ : Source)) (Fin.cases ((⟨145⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state11Used : Fin 11 → Fin 84 :=
  (Fin.cases (64) (Fin.cases (18) (Fin.cases (38) (Fin.cases (74) (Fin.cases (43) (Fin.cases (75) (Fin.cases (70) (Fin.cases (26) (Fin.cases (58) (Fin.cases (16) (Fin.cases (5) (fun i => Fin.elim0 i))))))))))))

private def state12Generators : Fin 11 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))))

private def state12Used : Fin 11 → Fin 84 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))))

def stateGenerators : Fin 13 → Fin 11 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (fun i => Fin.elim0 i))))))))))))))

def stateUsed : Fin 13 → Fin 11 → Fin 84 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (fun i => Fin.elim0 i))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 13) (k : Fin 11),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 44 → Fin 84 :=
  (Fin.cases (0) (Fin.cases (5) (Fin.cases (23) (Fin.cases (80) (Fin.cases (27) (Fin.cases (30) (Fin.cases (42) (Fin.cases (51) (Fin.cases (55) (Fin.cases (34) (Fin.cases (49) (Fin.cases (83) (Fin.cases (50) (Fin.cases (73) (Fin.cases (62) (Fin.cases (36) (Fin.cases (45) (Fin.cases (79) (Fin.cases (81) (Fin.cases (38) (Fin.cases (66) (Fin.cases (31) (Fin.cases (52) (Fin.cases (54) (Fin.cases (57) (Fin.cases (40) (Fin.cases (64) (Fin.cases (28) (Fin.cases (20) (Fin.cases (44) (Fin.cases (25) (Fin.cases (17) (Fin.cases (48) (Fin.cases (37) (Fin.cases (71) (Fin.cases (68) (Fin.cases (63) (Fin.cases (82) (Fin.cases (19) (Fin.cases (53) (Fin.cases (21) (Fin.cases (47) (Fin.cases (22) (Fin.cases (29) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 44,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 84 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 13 → Fin 44 → Fin 13 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (9) (Fin.cases (5) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (3) (Fin.cases (2) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (9) (Fin.cases (1) (Fin.cases (5) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (9) (Fin.cases (5) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (3) (Fin.cases (2) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (9) (Fin.cases (1) (Fin.cases (5) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (9) (Fin.cases (5) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (5) (Fin.cases (2) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (2) (Fin.cases (5) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (9) (Fin.cases (5) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (3) (Fin.cases (5) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (9) (Fin.cases (3) (Fin.cases (5) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (6) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (9) (Fin.cases (4) (Fin.cases (6) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (9) (Fin.cases (5) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (5) (Fin.cases (5) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (6) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (10) (Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (10) (Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (7) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (10) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))) (fun i => Fin.elim0 i))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow29NormalCore

end
