import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow22TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow22TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow22TopCertificate.ambient
def topRepresentative : Fin 16 → Source := PrimitiveAffineSixteenFrameRow22TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow22TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow22TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow22TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 27 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow22TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 27 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow22TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 27,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow22TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow22TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 27 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 27 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445592649428767520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229770993654068580 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6081866316104186250 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18297112935027778320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6288940358659875120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7238972199744905520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14906726159964840720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387373609776097465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17148711520433122185 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310694586491374235 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946949744215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441539476097868035 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7238955642140692995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8526625510496604720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360521110229098515 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459128985913860400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16126957421119349520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311269535231638765 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306394160889091910 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5068783572490920240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951606362640 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 27) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 27) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 27) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 27) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow22TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow22TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow22TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow22TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow22TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 27) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 27) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 27 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 8 then 5
    else if x.index.val = 9 then 6
    else if x.index.val = 17 then 7
    else if x.index.val = 18 then 8
    else if x.index.val = 19 then 9
    else if x.index.val = 29 then 10
    else if x.index.val = 38 then 11
    else if x.index.val = 67 then 12
    else if x.index.val = 75 then 13
    else if x.index.val = 98 then 14
    else if x.index.val = 109 then 15
    else if x.index.val = 141 then 16
    else if x.index.val = 143 then 17
    else if x.index.val = 172 then 18
    else if x.index.val = 181 then 19
    else if x.index.val = 219 then 20
    else if x.index.val = 247 then 21
    else if x.index.val = 306 then 22
    else if x.index.val = 344 then 23
    else if x.index.val = 349 then 24
    else if x.index.val = 364 then 25
    else if x.index.val = 375 then 26
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 27,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 27) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 7 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state0Used : Fin 7 → Fin 27 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state1Generators : Fin 7 → Source :=
  (Fin.cases ((⟨17⟩ : Source)) (Fin.cases ((⟨75⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 27 :=
  (Fin.cases (7) (Fin.cases (13) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨17⟩ : Source)) (Fin.cases ((⟨75⟩ : Source)) (Fin.cases ((⟨29⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 27 :=
  (Fin.cases (7) (Fin.cases (13) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨17⟩ : Source)) (Fin.cases ((⟨75⟩ : Source)) (Fin.cases ((⟨375⟩ : Source)) (Fin.cases ((⟨29⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 27 :=
  (Fin.cases (7) (Fin.cases (13) (Fin.cases (26) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨109⟩ : Source)) (Fin.cases ((⟨306⟩ : Source)) (Fin.cases ((⟨75⟩ : Source)) (Fin.cases ((⟨17⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 27 :=
  (Fin.cases (15) (Fin.cases (22) (Fin.cases (13) (Fin.cases (7) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state5Generators : Fin 7 → Source :=
  (Fin.cases ((⟨109⟩ : Source)) (Fin.cases ((⟨306⟩ : Source)) (Fin.cases ((⟨75⟩ : Source)) (Fin.cases ((⟨17⟩ : Source)) (Fin.cases ((⟨29⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state5Used : Fin 7 → Fin 27 :=
  (Fin.cases (15) (Fin.cases (22) (Fin.cases (13) (Fin.cases (7) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state6Generators : Fin 7 → Source :=
  (Fin.cases ((⟨109⟩ : Source)) (Fin.cases ((⟨306⟩ : Source)) (Fin.cases ((⟨75⟩ : Source)) (Fin.cases ((⟨17⟩ : Source)) (Fin.cases ((⟨375⟩ : Source)) (Fin.cases ((⟨29⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state6Used : Fin 7 → Fin 27 :=
  (Fin.cases (15) (Fin.cases (22) (Fin.cases (13) (Fin.cases (7) (Fin.cases (26) (Fin.cases (10) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state7Generators : Fin 7 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨67⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state7Used : Fin 7 → Fin 27 :=
  (Fin.cases (6) (Fin.cases (17) (Fin.cases (12) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state8Generators : Fin 7 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨67⟩ : Source)) (Fin.cases ((⟨181⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state8Used : Fin 7 → Fin 27 :=
  (Fin.cases (6) (Fin.cases (17) (Fin.cases (12) (Fin.cases (19) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state9Generators : Fin 7 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨67⟩ : Source)) (Fin.cases ((⟨181⟩ : Source)) (Fin.cases ((⟨172⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state9Used : Fin 7 → Fin 27 :=
  (Fin.cases (6) (Fin.cases (17) (Fin.cases (12) (Fin.cases (19) (Fin.cases (18) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state10Generators : Fin 7 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨67⟩ : Source)) (Fin.cases ((⟨181⟩ : Source)) (Fin.cases ((⟨375⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state10Used : Fin 7 → Fin 27 :=
  (Fin.cases (6) (Fin.cases (17) (Fin.cases (12) (Fin.cases (19) (Fin.cases (26) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state11Generators : Fin 7 → Source :=
  (Fin.cases ((⟨29⟩ : Source)) (Fin.cases ((⟨19⟩ : Source)) (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨109⟩ : Source)) (Fin.cases ((⟨306⟩ : Source)) (Fin.cases ((⟨75⟩ : Source)) (Fin.cases ((⟨17⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state11Used : Fin 7 → Fin 27 :=
  (Fin.cases (10) (Fin.cases (9) (Fin.cases (6) (Fin.cases (15) (Fin.cases (22) (Fin.cases (13) (Fin.cases (7) (fun i => Fin.elim0 i))))))))

private def state12Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state12Used : Fin 7 → Fin 27 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 13 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (fun i => Fin.elim0 i))))))))))))))

def stateUsed : Fin 13 → Fin 7 → Fin 27 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (fun i => Fin.elim0 i))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 13) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 16 → Fin 27 :=
  (Fin.cases (0) (Fin.cases (23) (Fin.cases (10) (Fin.cases (21) (Fin.cases (5) (Fin.cases (20) (Fin.cases (6) (Fin.cases (8) (Fin.cases (25) (Fin.cases (7) (Fin.cases (16) (Fin.cases (3) (Fin.cases (24) (Fin.cases (15) (Fin.cases (14) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 16,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 27 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 13 → Fin 16 → Fin 13 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (3) (Fin.cases (2) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (1) (Fin.cases (11) (Fin.cases (5) (Fin.cases (6) (Fin.cases (4) (Fin.cases (9) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (3) (Fin.cases (2) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (1) (Fin.cases (11) (Fin.cases (5) (Fin.cases (6) (Fin.cases (4) (Fin.cases (9) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (3) (Fin.cases (2) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (2) (Fin.cases (11) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (9) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (12) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (3) (Fin.cases (12) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (4) (Fin.cases (11) (Fin.cases (5) (Fin.cases (6) (Fin.cases (4) (Fin.cases (9) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (9) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (12) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (10) (Fin.cases (8) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (7) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (11) (Fin.cases (8) (Fin.cases (10) (Fin.cases (7) (Fin.cases (9) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (9) (Fin.cases (11) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (11) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (9) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (12) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))) (fun i => Fin.elim0 i))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow22NormalCore

end
