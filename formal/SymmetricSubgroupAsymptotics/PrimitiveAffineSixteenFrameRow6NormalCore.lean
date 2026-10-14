import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow6TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow6TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow6TopCertificate.ambient
def topRepresentative : Fin 9 → Source := PrimitiveAffineSixteenFrameRow6TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow6TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow6TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow6TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 25 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow6TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 25 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow6TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 25,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow6TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow6TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 25 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 25 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360489091245937440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8526492917087123850 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636070175845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986573291570 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445624668913283330 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849650554710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531481147413097980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378211813142490620 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059580303744267365 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613160528176500 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136240708629853285 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311319980126825980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310711081721798960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271338832400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920134157078303520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229785231184589925 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (157984933357940220 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306394160385775175 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701125456400 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 25) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 25) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 25) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 25) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow6TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow6TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow6TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow6TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow6TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 25) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 25) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 25 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 8 then 5
    else if x.index.val = 13 then 6
    else if x.index.val = 48 then 7
    else if x.index.val = 54 then 8
    else if x.index.val = 72 then 9
    else if x.index.val = 85 then 10
    else if x.index.val = 93 then 11
    else if x.index.val = 125 then 12
    else if x.index.val = 131 then 13
    else if x.index.val = 144 then 14
    else if x.index.val = 154 then 15
    else if x.index.val = 155 then 16
    else if x.index.val = 162 then 17
    else if x.index.val = 173 then 18
    else if x.index.val = 174 then 19
    else if x.index.val = 180 then 20
    else if x.index.val = 181 then 21
    else if x.index.val = 182 then 22
    else if x.index.val = 187 then 23
    else if x.index.val = 191 then 24
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 25,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 25) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 6 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state0Used : Fin 6 → Fin 25 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state1Generators : Fin 6 → Source :=
  (Fin.cases ((⟨144⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state1Used : Fin 6 → Fin 25 :=
  (Fin.cases (14) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state2Generators : Fin 6 → Source :=
  (Fin.cases ((⟨144⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨48⟩ : Source)) (Fin.cases ((⟨174⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state2Used : Fin 6 → Fin 25 :=
  (Fin.cases (14) (Fin.cases (11) (Fin.cases (7) (Fin.cases (19) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state3Generators : Fin 6 → Source :=
  (Fin.cases ((⟨144⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨180⟩ : Source)) (Fin.cases ((⟨85⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state3Used : Fin 6 → Fin 25 :=
  (Fin.cases (14) (Fin.cases (11) (Fin.cases (20) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state4Generators : Fin 6 → Source :=
  (Fin.cases ((⟨144⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨54⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state4Used : Fin 6 → Fin 25 :=
  (Fin.cases (14) (Fin.cases (11) (Fin.cases (8) (Fin.cases (3) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state5Generators : Fin 6 → Source :=
  (Fin.cases ((⟨144⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨154⟩ : Source)) (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state5Used : Fin 6 → Fin 25 :=
  (Fin.cases (14) (Fin.cases (11) (Fin.cases (15) (Fin.cases (13) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state6Generators : Fin 6 → Source :=
  (Fin.cases ((⟨191⟩ : Source)) (Fin.cases ((⟨162⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state6Used : Fin 6 → Fin 25 :=
  (Fin.cases (24) (Fin.cases (17) (Fin.cases (11) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state7Generators : Fin 6 → Source :=
  (Fin.cases ((⟨131⟩ : Source)) (Fin.cases ((⟨154⟩ : Source)) (Fin.cases ((⟨181⟩ : Source)) (Fin.cases ((⟨187⟩ : Source)) (Fin.cases ((⟨191⟩ : Source)) (Fin.cases ((⟨72⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state7Used : Fin 6 → Fin 25 :=
  (Fin.cases (13) (Fin.cases (15) (Fin.cases (21) (Fin.cases (23) (Fin.cases (24) (Fin.cases (9) (fun i => Fin.elim0 i)))))))

private def state8Generators : Fin 6 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state8Used : Fin 6 → Fin 25 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

def stateGenerators : Fin 9 → Fin 6 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (fun i => Fin.elim0 i))))))))))

def stateUsed : Fin 9 → Fin 6 → Fin 25 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (fun i => Fin.elim0 i))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 9) (k : Fin 6),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 9 → Fin 25 :=
  (Fin.cases (0) (Fin.cases (23) (Fin.cases (16) (Fin.cases (18) (Fin.cases (11) (Fin.cases (12) (Fin.cases (22) (Fin.cases (13) (Fin.cases (6) (fun i => Fin.elim0 i))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 9,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 25 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 9 → Fin 9 → Fin 9 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (5) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (5) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (7) (Fin.cases (8) (Fin.cases (8) (Fin.cases (2) (Fin.cases (7) (Fin.cases (2) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (7) (Fin.cases (8) (Fin.cases (8) (Fin.cases (3) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (7) (Fin.cases (8) (Fin.cases (8) (Fin.cases (4) (Fin.cases (4) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (7) (Fin.cases (8) (Fin.cases (8) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (5) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (8) (Fin.cases (8) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (fun i => Fin.elim0 i))))))))))) (fun i => Fin.elim0 i))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow6NormalCore

end
