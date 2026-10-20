import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow21TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow21TopCertificate.group

def topAmbient : Fin 5 → Source := PrimitiveAffineSixteenFrameRow21TopCertificate.ambient
def topRepresentative : Fin 16 → Source := PrimitiveAffineSixteenFrameRow21TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow21TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow21TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow21TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 31 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow21TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 31 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow21TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 31,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow21TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow21TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 31 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 31 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445592649428767520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636072142180 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8522270792435480970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721306305761330 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18297112935027778320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6288940358659875120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7238972199744905520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14906726159964840720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310748252107745465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136222090165835590 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920133061863609120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441539476097868035 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059580304531670615 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920099947160482050 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (157985963896463055 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229785231470647110 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938491900195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387352800659540635 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7297954248655957965 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459128985913860400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17076881673873269520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951606362640 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16126957421119349520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445625764131909890 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5068783572490920240 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 31) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 31) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 31) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 31) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow21TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow21TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow21TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow21TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow21TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 31) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 31) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 31 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 10 then 6
    else if x.index.val = 11 then 7
    else if x.index.val = 25 then 8
    else if x.index.val = 26 then 9
    else if x.index.val = 42 then 10
    else if x.index.val = 56 then 11
    else if x.index.val = 87 then 12
    else if x.index.val = 93 then 13
    else if x.index.val = 116 then 14
    else if x.index.val = 149 then 15
    else if x.index.val = 191 then 16
    else if x.index.val = 201 then 17
    else if x.index.val = 203 then 18
    else if x.index.val = 225 then 19
    else if x.index.val = 227 then 20
    else if x.index.val = 239 then 21
    else if x.index.val = 256 then 22
    else if x.index.val = 337 then 23
    else if x.index.val = 344 then 24
    else if x.index.val = 351 then 25
    else if x.index.val = 355 then 26
    else if x.index.val = 360 then 27
    else if x.index.val = 371 then 28
    else if x.index.val = 377 then 29
    else if x.index.val = 380 then 30
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 31,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 31) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 7 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state0Used : Fin 7 → Fin 31 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state1Generators : Fin 7 → Source :=
  (Fin.cases ((⟨201⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 31 :=
  (Fin.cases (17) (Fin.cases (29) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨201⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 31 :=
  (Fin.cases (17) (Fin.cases (29) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨201⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨351⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 31 :=
  (Fin.cases (17) (Fin.cases (29) (Fin.cases (25) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨87⟩ : Source)) (Fin.cases ((⟨203⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨227⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 31 :=
  (Fin.cases (12) (Fin.cases (18) (Fin.cases (29) (Fin.cases (20) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state5Generators : Fin 7 → Source :=
  (Fin.cases ((⟨87⟩ : Source)) (Fin.cases ((⟨203⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨227⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state5Used : Fin 7 → Fin 31 :=
  (Fin.cases (12) (Fin.cases (18) (Fin.cases (29) (Fin.cases (20) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state6Generators : Fin 7 → Source :=
  (Fin.cases ((⟨87⟩ : Source)) (Fin.cases ((⟨203⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨227⟩ : Source)) (Fin.cases ((⟨351⟩ : Source)) (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state6Used : Fin 7 → Fin 31 :=
  (Fin.cases (12) (Fin.cases (18) (Fin.cases (29) (Fin.cases (20) (Fin.cases (25) (Fin.cases (10) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state7Generators : Fin 7 → Source :=
  (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨371⟩ : Source)) (Fin.cases ((⟨256⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state7Used : Fin 7 → Fin 31 :=
  (Fin.cases (13) (Fin.cases (28) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state8Generators : Fin 7 → Source :=
  (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨371⟩ : Source)) (Fin.cases ((⟨256⟩ : Source)) (Fin.cases ((⟨191⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state8Used : Fin 7 → Fin 31 :=
  (Fin.cases (13) (Fin.cases (28) (Fin.cases (22) (Fin.cases (16) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state9Generators : Fin 7 → Source :=
  (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨371⟩ : Source)) (Fin.cases ((⟨256⟩ : Source)) (Fin.cases ((⟨191⟩ : Source)) (Fin.cases ((⟨344⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state9Used : Fin 7 → Fin 31 :=
  (Fin.cases (13) (Fin.cases (28) (Fin.cases (22) (Fin.cases (16) (Fin.cases (24) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state10Generators : Fin 7 → Source :=
  (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨371⟩ : Source)) (Fin.cases ((⟨256⟩ : Source)) (Fin.cases ((⟨191⟩ : Source)) (Fin.cases ((⟨351⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state10Used : Fin 7 → Fin 31 :=
  (Fin.cases (13) (Fin.cases (28) (Fin.cases (22) (Fin.cases (16) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state11Generators : Fin 7 → Source :=
  (Fin.cases ((⟨42⟩ : Source)) (Fin.cases ((⟨26⟩ : Source)) (Fin.cases ((⟨11⟩ : Source)) (Fin.cases ((⟨87⟩ : Source)) (Fin.cases ((⟨203⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨227⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state11Used : Fin 7 → Fin 31 :=
  (Fin.cases (10) (Fin.cases (9) (Fin.cases (7) (Fin.cases (12) (Fin.cases (18) (Fin.cases (29) (Fin.cases (20) (fun i => Fin.elim0 i))))))))

private def state12Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state12Used : Fin 7 → Fin 31 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 13 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (fun i => Fin.elim0 i))))))))))))))

def stateUsed : Fin 13 → Fin 7 → Fin 31 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (fun i => Fin.elim0 i))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 13) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 16 → Fin 31 :=
  (Fin.cases (0) (Fin.cases (27) (Fin.cases (10) (Fin.cases (26) (Fin.cases (6) (Fin.cases (23) (Fin.cases (7) (Fin.cases (8) (Fin.cases (30) (Fin.cases (17) (Fin.cases (14) (Fin.cases (3) (Fin.cases (19) (Fin.cases (15) (Fin.cases (11) (Fin.cases (21) (fun i => Fin.elim0 i)))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 16,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 5 → Fin 31 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (fun i => Fin.elim0 i))))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 5,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 13 → Fin 16 → Fin 13 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (3) (Fin.cases (2) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (1) (Fin.cases (11) (Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (3) (Fin.cases (2) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (1) (Fin.cases (11) (Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (3) (Fin.cases (2) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (2) (Fin.cases (11) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (12) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (3) (Fin.cases (12) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (4) (Fin.cases (11) (Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (12) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (10) (Fin.cases (8) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (11) (Fin.cases (7) (Fin.cases (10) (Fin.cases (8) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (11) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (fun i => Fin.elim0 i))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow21NormalCore

end
