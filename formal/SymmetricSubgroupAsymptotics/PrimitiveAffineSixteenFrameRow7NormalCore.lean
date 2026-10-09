import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow7TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow7TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow7TopCertificate.ambient
def topRepresentative : Fin 17 → Source := PrimitiveAffineSixteenFrameRow7TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow7TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow7TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow7TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 24 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow7TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 24 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow7TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 24,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow7TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow7TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 24 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 24 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445575125964165920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8526492917087123850 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636070175845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5140522453682364720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468281741907889050 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11005203506634036000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531514004418198765 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229752374467523685 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666158518800 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6217201477468430640 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613160528176500 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920134157078303520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951353721360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310748318804156720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360538632908247840 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306412779068999510 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136273565129659975 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136222090163865430 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229770992866645575 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387352866854609200 : Fin (16 ^ 16))) (fun i => Fin.elim0 i)))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 24) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 24) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 24) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 24) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow7TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow7TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow7TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow7TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow7TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 24) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 24) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 24 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 6 then 6
    else if x.index.val = 8 then 7
    else if x.index.val = 10 then 8
    else if x.index.val = 15 then 9
    else if x.index.val = 16 then 10
    else if x.index.val = 19 then 11
    else if x.index.val = 44 then 12
    else if x.index.val = 45 then 13
    else if x.index.val = 48 then 14
    else if x.index.val = 82 then 15
    else if x.index.val = 88 then 16
    else if x.index.val = 91 then 17
    else if x.index.val = 94 then 18
    else if x.index.val = 106 then 19
    else if x.index.val = 110 then 20
    else if x.index.val = 128 then 21
    else if x.index.val = 130 then 22
    else if x.index.val = 135 then 23
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 24,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 24) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 6 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state0Used : Fin 6 → Fin 24 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state1Generators : Fin 6 → Source :=
  (Fin.cases ((⟨88⟩ : Source)) (Fin.cases ((⟨82⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state1Used : Fin 6 → Fin 24 :=
  (Fin.cases (16) (Fin.cases (15) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state2Generators : Fin 6 → Source :=
  (Fin.cases ((⟨88⟩ : Source)) (Fin.cases ((⟨82⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state2Used : Fin 6 → Fin 24 :=
  (Fin.cases (16) (Fin.cases (15) (Fin.cases (14) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state3Generators : Fin 6 → Source :=
  (Fin.cases ((⟨88⟩ : Source)) (Fin.cases ((⟨82⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state3Used : Fin 6 → Fin 24 :=
  (Fin.cases (16) (Fin.cases (15) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state4Generators : Fin 6 → Source :=
  (Fin.cases ((⟨88⟩ : Source)) (Fin.cases ((⟨82⟩ : Source)) (Fin.cases ((⟨16⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state4Used : Fin 6 → Fin 24 :=
  (Fin.cases (16) (Fin.cases (15) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state5Generators : Fin 6 → Source :=
  (Fin.cases ((⟨88⟩ : Source)) (Fin.cases ((⟨82⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨16⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state5Used : Fin 6 → Fin 24 :=
  (Fin.cases (16) (Fin.cases (15) (Fin.cases (4) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state6Generators : Fin 6 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state6Used : Fin 6 → Fin 24 :=
  (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state7Generators : Fin 6 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state7Used : Fin 6 → Fin 24 :=
  (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (14) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state8Generators : Fin 6 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state8Used : Fin 6 → Fin 24 :=
  (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (4) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state9Generators : Fin 6 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨16⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state9Used : Fin 6 → Fin 24 :=
  (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (10) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state10Generators : Fin 6 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨16⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state10Used : Fin 6 → Fin 24 :=
  (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (4) (Fin.cases (10) (fun i => Fin.elim0 i)))))))

private def state11Generators : Fin 6 → Source :=
  (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state11Used : Fin 6 → Fin 24 :=
  (Fin.cases (5) (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state12Generators : Fin 6 → Source :=
  (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state12Used : Fin 6 → Fin 24 :=
  (Fin.cases (5) (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (14) (fun i => Fin.elim0 i)))))))

private def state13Generators : Fin 6 → Source :=
  (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state13Used : Fin 6 → Fin 24 :=
  (Fin.cases (5) (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (Fin.cases (4) (fun i => Fin.elim0 i)))))))

private def state14Generators : Fin 6 → Source :=
  (Fin.cases ((⟨16⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨128⟩ : Source)) (Fin.cases ((⟨130⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state14Used : Fin 6 → Fin 24 :=
  (Fin.cases (10) (Fin.cases (5) (Fin.cases (2) (Fin.cases (21) (Fin.cases (22) (Fin.cases (8) (fun i => Fin.elim0 i)))))))

private def state15Generators : Fin 6 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state15Used : Fin 6 → Fin 24 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

def stateGenerators : Fin 16 → Fin 6 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (Fin.cases (state14Generators) (Fin.cases (state15Generators) (fun i => Fin.elim0 i)))))))))))))))))

def stateUsed : Fin 16 → Fin 6 → Fin 24 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (Fin.cases (state14Used) (Fin.cases (state15Used) (fun i => Fin.elim0 i)))))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 16) (k : Fin 6),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 17 → Fin 24 :=
  (Fin.cases (0) (Fin.cases (4) (Fin.cases (10) (Fin.cases (14) (Fin.cases (17) (Fin.cases (11) (Fin.cases (23) (Fin.cases (5) (Fin.cases (13) (Fin.cases (7) (Fin.cases (18) (Fin.cases (1) (Fin.cases (15) (Fin.cases (12) (Fin.cases (20) (Fin.cases (9) (Fin.cases (19) (fun i => Fin.elim0 i))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 17,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 24 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 16 → Fin 17 → Fin 16 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (3) (Fin.cases (4) (Fin.cases (2) (Fin.cases (14) (Fin.cases (13) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (1) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (9) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (3) (Fin.cases (4) (Fin.cases (2) (Fin.cases (14) (Fin.cases (13) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (1) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (9) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (2) (Fin.cases (15) (Fin.cases (15) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (2) (Fin.cases (7) (Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (5) (Fin.cases (5) (Fin.cases (15) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (15) (Fin.cases (3) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (5) (Fin.cases (4) (Fin.cases (5) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (14) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (14) (Fin.cases (4) (Fin.cases (9) (Fin.cases (10) (Fin.cases (10) (Fin.cases (9) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (5) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (8) (Fin.cases (9) (Fin.cases (7) (Fin.cases (14) (Fin.cases (13) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (9) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (Fin.cases (7) (Fin.cases (15) (Fin.cases (15) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (15) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (15) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (10) (Fin.cases (9) (Fin.cases (10) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (14) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (14) (Fin.cases (9) (Fin.cases (9) (Fin.cases (10) (Fin.cases (10) (Fin.cases (9) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (13) (Fin.cases (14) (Fin.cases (12) (Fin.cases (14) (Fin.cases (13) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (13) (Fin.cases (14) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (13) (Fin.cases (15) (Fin.cases (13) (Fin.cases (15) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (14) (Fin.cases (15) (Fin.cases (14) (Fin.cases (15) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (14) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (14) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i))))))))))))))))))) (fun i => Fin.elim0 i)))))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow7NormalCore

end
