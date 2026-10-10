import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow11TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow11TopCertificate.group

def topAmbient : Fin 5 → Source := PrimitiveAffineSixteenFrameRow11TopCertificate.ambient
def topRepresentative : Fin 36 → Source := PrimitiveAffineSixteenFrameRow11TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow11TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow11TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow11TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 63 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow11TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 63 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow11TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 63,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow11TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow11TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 63 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 63 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445608240663368480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8526492917087123850 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636070175845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758544240414770 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468314856607091610 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18288572946863122245 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445635568821620 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086055326557976970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714808103440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223825642000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1298159213916494475 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11216268758328074220 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311268505194462445 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086055325737130920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1298126099718638490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387390104505164080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5000969291085756810 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229752374968870260 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378197576081854430 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306394160385775175 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441357339419777960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258477019905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531495385229680335 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613160528176500 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996074734287388110 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136240708629853285 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136273564845565300 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306412779286259060 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311268504438500860 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311268504943779535 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311287123121732845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1298109671468742825 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531495384979012845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701125456400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271654384385 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378197575831186940 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158036408035700220 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136222089946621300 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158036408290311405 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986573291570 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13369552330164595935 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271338832400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531495385734966780 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531495385484283870 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311319980126825980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158036407785017310 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158036408540978895 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12149358306123894525 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951353721360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1298142785666591160 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311268504689168350 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378197575325900495 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666474070785 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666158518800 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378197575576583405 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 63) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 63) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 63) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 63) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow11TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow11TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow11TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow11TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow11TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 63) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 63) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 63 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 7 then 6
    else if x.index.val = 8 then 7
    else if x.index.val = 15 then 8
    else if x.index.val = 21 then 9
    else if x.index.val = 22 then 10
    else if x.index.val = 42 then 11
    else if x.index.val = 74 then 12
    else if x.index.val = 111 then 13
    else if x.index.val = 124 then 14
    else if x.index.val = 126 then 15
    else if x.index.val = 131 then 16
    else if x.index.val = 165 then 17
    else if x.index.val = 191 then 18
    else if x.index.val = 206 then 19
    else if x.index.val = 210 then 20
    else if x.index.val = 216 then 21
    else if x.index.val = 219 then 22
    else if x.index.val = 237 then 23
    else if x.index.val = 242 then 24
    else if x.index.val = 281 then 25
    else if x.index.val = 308 then 26
    else if x.index.val = 333 then 27
    else if x.index.val = 345 then 28
    else if x.index.val = 356 then 29
    else if x.index.val = 390 then 30
    else if x.index.val = 396 then 31
    else if x.index.val = 403 then 32
    else if x.index.val = 423 then 33
    else if x.index.val = 437 then 34
    else if x.index.val = 440 then 35
    else if x.index.val = 500 then 36
    else if x.index.val = 521 then 37
    else if x.index.val = 527 then 38
    else if x.index.val = 539 then 39
    else if x.index.val = 545 then 40
    else if x.index.val = 556 then 41
    else if x.index.val = 559 then 42
    else if x.index.val = 570 then 43
    else if x.index.val = 571 then 44
    else if x.index.val = 578 then 45
    else if x.index.val = 589 then 46
    else if x.index.val = 594 then 47
    else if x.index.val = 597 then 48
    else if x.index.val = 612 then 49
    else if x.index.val = 615 then 50
    else if x.index.val = 616 then 51
    else if x.index.val = 630 then 52
    else if x.index.val = 643 then 53
    else if x.index.val = 661 then 54
    else if x.index.val = 668 then 55
    else if x.index.val = 672 then 56
    else if x.index.val = 702 then 57
    else if x.index.val = 720 then 58
    else if x.index.val = 729 then 59
    else if x.index.val = 747 then 60
    else if x.index.val = 758 then 61
    else if x.index.val = 763 then 62
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 63,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 63) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 8 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state0Used : Fin 8 → Fin 63 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state1Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state1Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state2Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨672⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state2Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (56) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state3Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state3Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (61) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state4Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state4Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state5Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state5Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (61) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state6Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨612⟩ : Source)) (Fin.cases ((⟨403⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state6Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (49) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state7Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨630⟩ : Source)) (Fin.cases ((⟨396⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state7Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (52) (Fin.cases (31) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state8Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨237⟩ : Source)) (Fin.cases ((⟨219⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state8Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (23) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state9Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state9Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (58) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state10Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨672⟩ : Source)) (Fin.cases ((⟨612⟩ : Source)) (Fin.cases ((⟨403⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state10Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (56) (Fin.cases (49) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state11Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨672⟩ : Source)) (Fin.cases ((⟨630⟩ : Source)) (Fin.cases ((⟨396⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state11Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (56) (Fin.cases (52) (Fin.cases (31) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state12Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨672⟩ : Source)) (Fin.cases ((⟨237⟩ : Source)) (Fin.cases ((⟨219⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state12Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (56) (Fin.cases (23) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state13Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨672⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state13Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (56) (Fin.cases (58) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state14Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨612⟩ : Source)) (Fin.cases ((⟨403⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state14Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (61) (Fin.cases (49) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state15Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨630⟩ : Source)) (Fin.cases ((⟨396⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state15Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (61) (Fin.cases (52) (Fin.cases (31) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state16Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨237⟩ : Source)) (Fin.cases ((⟨219⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state16Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (61) (Fin.cases (23) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state17Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state17Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (61) (Fin.cases (58) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state18Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨612⟩ : Source)) (Fin.cases ((⟨403⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state18Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (10) (Fin.cases (49) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state19Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨630⟩ : Source)) (Fin.cases ((⟨396⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state19Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (10) (Fin.cases (52) (Fin.cases (31) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state20Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨237⟩ : Source)) (Fin.cases ((⟨219⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state20Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (10) (Fin.cases (23) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state21Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state21Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (10) (Fin.cases (58) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state22Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨437⟩ : Source)) (Fin.cases ((⟨570⟩ : Source)) (Fin.cases ((⟨281⟩ : Source)) (Fin.cases ((⟨440⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state22Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (34) (Fin.cases (43) (Fin.cases (25) (Fin.cases (35) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state23Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨15⟩ : Source)) (Fin.cases ((⟨21⟩ : Source)) (Fin.cases ((⟨615⟩ : Source)) (Fin.cases ((⟨390⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state23Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (8) (Fin.cases (9) (Fin.cases (50) (Fin.cases (30) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state24Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨191⟩ : Source)) (Fin.cases ((⟨423⟩ : Source)) (Fin.cases ((⟨242⟩ : Source)) (Fin.cases ((⟨216⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state24Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (18) (Fin.cases (33) (Fin.cases (24) (Fin.cases (21) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state25Generators : Fin 8 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state25Used : Fin 8 → Fin 63 :=
  (Fin.cases (16) (Fin.cases (54) (Fin.cases (10) (Fin.cases (61) (Fin.cases (58) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state26Generators : Fin 8 → Source :=
  (Fin.cases ((⟨539⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨578⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state26Used : Fin 8 → Fin 63 :=
  (Fin.cases (39) (Fin.cases (47) (Fin.cases (54) (Fin.cases (45) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state27Generators : Fin 8 → Source :=
  (Fin.cases ((⟨539⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨578⟩ : Source)) (Fin.cases ((⟨111⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state27Used : Fin 8 → Fin 63 :=
  (Fin.cases (39) (Fin.cases (47) (Fin.cases (54) (Fin.cases (45) (Fin.cases (13) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state28Generators : Fin 8 → Source :=
  (Fin.cases ((⟨539⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨578⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state28Used : Fin 8 → Fin 63 :=
  (Fin.cases (39) (Fin.cases (47) (Fin.cases (54) (Fin.cases (45) (Fin.cases (5) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state29Generators : Fin 8 → Source :=
  (Fin.cases ((⟨539⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨578⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state29Used : Fin 8 → Fin 63 :=
  (Fin.cases (39) (Fin.cases (47) (Fin.cases (54) (Fin.cases (45) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state30Generators : Fin 8 → Source :=
  (Fin.cases ((⟨539⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨578⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state30Used : Fin 8 → Fin 63 :=
  (Fin.cases (39) (Fin.cases (47) (Fin.cases (54) (Fin.cases (45) (Fin.cases (5) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state31Generators : Fin 8 → Source :=
  (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state31Used : Fin 8 → Fin 63 :=
  (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state32Generators : Fin 8 → Source :=
  (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨111⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state32Used : Fin 8 → Fin 63 :=
  (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (13) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state33Generators : Fin 8 → Source :=
  (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state33Used : Fin 8 → Fin 63 :=
  (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (5) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state34Generators : Fin 8 → Source :=
  (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state34Used : Fin 8 → Fin 63 :=
  (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (11) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state35Generators : Fin 8 → Source :=
  (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state35Used : Fin 8 → Fin 63 :=
  (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (5) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))

private def state36Generators : Fin 8 → Source :=
  (Fin.cases ((⟨668⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state36Used : Fin 8 → Fin 63 :=
  (Fin.cases (55) (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state37Generators : Fin 8 → Source :=
  (Fin.cases ((⟨668⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨111⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state37Used : Fin 8 → Fin 63 :=
  (Fin.cases (55) (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))

private def state38Generators : Fin 8 → Source :=
  (Fin.cases ((⟨668⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state38Used : Fin 8 → Fin 63 :=
  (Fin.cases (55) (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))

private def state39Generators : Fin 8 → Source :=
  (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨668⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨616⟩ : Source)) (Fin.cases ((⟨594⟩ : Source)) (Fin.cases ((⟨521⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state39Used : Fin 8 → Fin 63 :=
  (Fin.cases (11) (Fin.cases (55) (Fin.cases (28) (Fin.cases (58) (Fin.cases (12) (Fin.cases (51) (Fin.cases (47) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))

private def state40Generators : Fin 8 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state40Used : Fin 8 → Fin 63 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

def stateGenerators : Fin 41 → Fin 8 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (Fin.cases (state14Generators) (Fin.cases (state15Generators) (Fin.cases (state16Generators) (Fin.cases (state17Generators) (Fin.cases (state18Generators) (Fin.cases (state19Generators) (Fin.cases (state20Generators) (Fin.cases (state21Generators) (Fin.cases (state22Generators) (Fin.cases (state23Generators) (Fin.cases (state24Generators) (Fin.cases (state25Generators) (Fin.cases (state26Generators) (Fin.cases (state27Generators) (Fin.cases (state28Generators) (Fin.cases (state29Generators) (Fin.cases (state30Generators) (Fin.cases (state31Generators) (Fin.cases (state32Generators) (Fin.cases (state33Generators) (Fin.cases (state34Generators) (Fin.cases (state35Generators) (Fin.cases (state36Generators) (Fin.cases (state37Generators) (Fin.cases (state38Generators) (Fin.cases (state39Generators) (Fin.cases (state40Generators) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))

def stateUsed : Fin 41 → Fin 8 → Fin 63 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (Fin.cases (state14Used) (Fin.cases (state15Used) (Fin.cases (state16Used) (Fin.cases (state17Used) (Fin.cases (state18Used) (Fin.cases (state19Used) (Fin.cases (state20Used) (Fin.cases (state21Used) (Fin.cases (state22Used) (Fin.cases (state23Used) (Fin.cases (state24Used) (Fin.cases (state25Used) (Fin.cases (state26Used) (Fin.cases (state27Used) (Fin.cases (state28Used) (Fin.cases (state29Used) (Fin.cases (state30Used) (Fin.cases (state31Used) (Fin.cases (state32Used) (Fin.cases (state33Used) (Fin.cases (state34Used) (Fin.cases (state35Used) (Fin.cases (state36Used) (Fin.cases (state37Used) (Fin.cases (state38Used) (Fin.cases (state39Used) (Fin.cases (state40Used) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 41) (k : Fin 8),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 36 → Fin 63 :=
  (Fin.cases (0) (Fin.cases (37) (Fin.cases (54) (Fin.cases (58) (Fin.cases (49) (Fin.cases (52) (Fin.cases (23) (Fin.cases (55) (Fin.cases (36) (Fin.cases (11) (Fin.cases (10) (Fin.cases (60) (Fin.cases (34) (Fin.cases (27) (Fin.cases (53) (Fin.cases (59) (Fin.cases (15) (Fin.cases (19) (Fin.cases (5) (Fin.cases (61) (Fin.cases (26) (Fin.cases (33) (Fin.cases (48) (Fin.cases (42) (Fin.cases (41) (Fin.cases (46) (Fin.cases (57) (Fin.cases (13) (Fin.cases (56) (Fin.cases (40) (Fin.cases (17) (Fin.cases (38) (Fin.cases (44) (Fin.cases (62) (Fin.cases (29) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 36,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 5 → Fin 63 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (fun i => Fin.elim0 i))))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 5,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 41 → Fin 36 → Fin 41 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (26) (Fin.cases (1) (Fin.cases (9) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (36) (Fin.cases (36) (Fin.cases (29) (Fin.cases (4) (Fin.cases (29) (Fin.cases (18) (Fin.cases (21) (Fin.cases (20) (Fin.cases (19) (Fin.cases (39) (Fin.cases (39) (Fin.cases (28) (Fin.cases (3) (Fin.cases (28) (Fin.cases (15) (Fin.cases (16) (Fin.cases (17) (Fin.cases (14) (Fin.cases (38) (Fin.cases (38) (Fin.cases (27) (Fin.cases (2) (Fin.cases (27) (Fin.cases (12) (Fin.cases (11) (Fin.cases (10) (Fin.cases (13) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (26) (Fin.cases (1) (Fin.cases (9) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (36) (Fin.cases (36) (Fin.cases (29) (Fin.cases (4) (Fin.cases (29) (Fin.cases (18) (Fin.cases (21) (Fin.cases (20) (Fin.cases (19) (Fin.cases (39) (Fin.cases (39) (Fin.cases (28) (Fin.cases (3) (Fin.cases (28) (Fin.cases (15) (Fin.cases (16) (Fin.cases (17) (Fin.cases (14) (Fin.cases (38) (Fin.cases (38) (Fin.cases (27) (Fin.cases (2) (Fin.cases (27) (Fin.cases (12) (Fin.cases (11) (Fin.cases (10) (Fin.cases (13) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (27) (Fin.cases (2) (Fin.cases (13) (Fin.cases (10) (Fin.cases (11) (Fin.cases (12) (Fin.cases (37) (Fin.cases (37) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (22) (Fin.cases (25) (Fin.cases (23) (Fin.cases (24) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (24) (Fin.cases (23) (Fin.cases (25) (Fin.cases (22) (Fin.cases (40) (Fin.cases (40) (Fin.cases (27) (Fin.cases (2) (Fin.cases (27) (Fin.cases (12) (Fin.cases (11) (Fin.cases (10) (Fin.cases (13) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (28) (Fin.cases (3) (Fin.cases (17) (Fin.cases (14) (Fin.cases (15) (Fin.cases (16) (Fin.cases (38) (Fin.cases (38) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (22) (Fin.cases (25) (Fin.cases (23) (Fin.cases (24) (Fin.cases (40) (Fin.cases (40) (Fin.cases (28) (Fin.cases (3) (Fin.cases (28) (Fin.cases (15) (Fin.cases (16) (Fin.cases (17) (Fin.cases (14) (Fin.cases (38) (Fin.cases (38) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (23) (Fin.cases (24) (Fin.cases (22) (Fin.cases (25) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (29) (Fin.cases (4) (Fin.cases (21) (Fin.cases (18) (Fin.cases (19) (Fin.cases (20) (Fin.cases (39) (Fin.cases (39) (Fin.cases (29) (Fin.cases (4) (Fin.cases (29) (Fin.cases (18) (Fin.cases (21) (Fin.cases (20) (Fin.cases (19) (Fin.cases (39) (Fin.cases (39) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (24) (Fin.cases (23) (Fin.cases (25) (Fin.cases (22) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (23) (Fin.cases (24) (Fin.cases (22) (Fin.cases (25) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (30) (Fin.cases (5) (Fin.cases (25) (Fin.cases (22) (Fin.cases (24) (Fin.cases (23) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (22) (Fin.cases (25) (Fin.cases (23) (Fin.cases (24) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (24) (Fin.cases (23) (Fin.cases (25) (Fin.cases (22) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (5) (Fin.cases (30) (Fin.cases (23) (Fin.cases (24) (Fin.cases (22) (Fin.cases (25) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (31) (Fin.cases (6) (Fin.cases (31) (Fin.cases (6) (Fin.cases (31) (Fin.cases (31) (Fin.cases (36) (Fin.cases (36) (Fin.cases (34) (Fin.cases (18) (Fin.cases (34) (Fin.cases (18) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (33) (Fin.cases (14) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (14) (Fin.cases (38) (Fin.cases (38) (Fin.cases (32) (Fin.cases (10) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (10) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (31) (Fin.cases (7) (Fin.cases (31) (Fin.cases (31) (Fin.cases (7) (Fin.cases (31) (Fin.cases (36) (Fin.cases (36) (Fin.cases (34) (Fin.cases (19) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (19) (Fin.cases (39) (Fin.cases (39) (Fin.cases (33) (Fin.cases (15) (Fin.cases (33) (Fin.cases (15) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (32) (Fin.cases (11) (Fin.cases (32) (Fin.cases (32) (Fin.cases (11) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (31) (Fin.cases (8) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (8) (Fin.cases (36) (Fin.cases (36) (Fin.cases (34) (Fin.cases (20) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (20) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (33) (Fin.cases (16) (Fin.cases (33) (Fin.cases (33) (Fin.cases (16) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (32) (Fin.cases (12) (Fin.cases (32) (Fin.cases (12) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (31) (Fin.cases (9) (Fin.cases (9) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (36) (Fin.cases (36) (Fin.cases (34) (Fin.cases (21) (Fin.cases (34) (Fin.cases (34) (Fin.cases (21) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (33) (Fin.cases (17) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (17) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (32) (Fin.cases (13) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (13) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (32) (Fin.cases (10) (Fin.cases (32) (Fin.cases (10) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (22) (Fin.cases (40) (Fin.cases (40) (Fin.cases (32) (Fin.cases (10) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (10) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (32) (Fin.cases (11) (Fin.cases (32) (Fin.cases (32) (Fin.cases (11) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (24) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (32) (Fin.cases (11) (Fin.cases (32) (Fin.cases (32) (Fin.cases (11) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (32) (Fin.cases (12) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (12) (Fin.cases (37) (Fin.cases (37) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (32) (Fin.cases (12) (Fin.cases (32) (Fin.cases (12) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (32) (Fin.cases (13) (Fin.cases (13) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (32) (Fin.cases (13) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (13) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (14) (Fin.cases (33) (Fin.cases (14) (Fin.cases (33) (Fin.cases (14) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (33) (Fin.cases (14) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (14) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (15) (Fin.cases (33) (Fin.cases (15) (Fin.cases (33) (Fin.cases (33) (Fin.cases (15) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (24) (Fin.cases (40) (Fin.cases (40) (Fin.cases (33) (Fin.cases (15) (Fin.cases (33) (Fin.cases (15) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (16) (Fin.cases (33) (Fin.cases (16) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (16) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (33) (Fin.cases (16) (Fin.cases (33) (Fin.cases (33) (Fin.cases (16) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (17) (Fin.cases (33) (Fin.cases (17) (Fin.cases (17) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (33) (Fin.cases (17) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (17) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (18) (Fin.cases (34) (Fin.cases (18) (Fin.cases (34) (Fin.cases (18) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (34) (Fin.cases (18) (Fin.cases (34) (Fin.cases (18) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (22) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (19) (Fin.cases (34) (Fin.cases (19) (Fin.cases (34) (Fin.cases (34) (Fin.cases (19) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (34) (Fin.cases (19) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (19) (Fin.cases (39) (Fin.cases (39) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (20) (Fin.cases (34) (Fin.cases (20) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (20) (Fin.cases (39) (Fin.cases (39) (Fin.cases (34) (Fin.cases (20) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (20) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (21) (Fin.cases (34) (Fin.cases (21) (Fin.cases (21) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (34) (Fin.cases (21) (Fin.cases (34) (Fin.cases (34) (Fin.cases (21) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (22) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (22) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (22) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (23) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (23) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (23) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (24) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (24) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (24) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (25) (Fin.cases (35) (Fin.cases (25) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (25) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (25) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (26) (Fin.cases (26) (Fin.cases (26) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (36) (Fin.cases (36) (Fin.cases (29) (Fin.cases (29) (Fin.cases (29) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (28) (Fin.cases (28) (Fin.cases (28) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (27) (Fin.cases (27) (Fin.cases (27) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (27) (Fin.cases (27) (Fin.cases (27) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (27) (Fin.cases (27) (Fin.cases (27) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (28) (Fin.cases (28) (Fin.cases (28) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (28) (Fin.cases (28) (Fin.cases (28) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (29) (Fin.cases (29) (Fin.cases (29) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (29) (Fin.cases (29) (Fin.cases (29) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (30) (Fin.cases (30) (Fin.cases (30) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (31) (Fin.cases (36) (Fin.cases (36) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (32) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (33) (Fin.cases (38) (Fin.cases (38) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (34) (Fin.cases (39) (Fin.cases (39) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (35) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (36) (Fin.cases (36) (Fin.cases (36) (Fin.cases (36) (Fin.cases (36) (Fin.cases (36) (Fin.cases (36) (Fin.cases (36) (Fin.cases (36) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (Fin.cases (37) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (38) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (39) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (Fin.cases (40) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow11NormalCore

end
