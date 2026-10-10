import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow9TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow9TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow9TopCertificate.ambient
def topRepresentative : Fin 18 → Source := PrimitiveAffineSixteenFrameRow9TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow9TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow9TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow9TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 37 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow9TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 37 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow9TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 37,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow9TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow9TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 37 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 37 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445608240663368480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8526492917087123850 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636070175845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758544240414770 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310711081721798960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468314856607091610 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445635568821620 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714808103440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229752374467523685 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721306873954595 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920134157078303520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387390104505164080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310694523837423920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306394160385775175 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672508705284865 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849650554710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311301361694269135 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613160528176500 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136240708629853285 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311287123121732845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701125456400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059598923212932950 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271338832400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311319980126825980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059631779428652615 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986573291570 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311268504689168350 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059598922711586375 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946446427990 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059580303744267365 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666474070785 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 37) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 37) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 37) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 37) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow9TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow9TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow9TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow9TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow9TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 37) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 37) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 37 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 6 then 6
    else if x.index.val = 12 then 7
    else if x.index.val = 15 then 8
    else if x.index.val = 28 then 9
    else if x.index.val = 41 then 10
    else if x.index.val = 47 then 11
    else if x.index.val = 52 then 12
    else if x.index.val = 69 then 13
    else if x.index.val = 91 then 14
    else if x.index.val = 104 then 15
    else if x.index.val = 109 then 16
    else if x.index.val = 119 then 17
    else if x.index.val = 128 then 18
    else if x.index.val = 132 then 19
    else if x.index.val = 143 then 20
    else if x.index.val = 156 then 21
    else if x.index.val = 173 then 22
    else if x.index.val = 196 then 23
    else if x.index.val = 206 then 24
    else if x.index.val = 213 then 25
    else if x.index.val = 229 then 26
    else if x.index.val = 241 then 27
    else if x.index.val = 242 then 28
    else if x.index.val = 270 then 29
    else if x.index.val = 290 then 30
    else if x.index.val = 333 then 31
    else if x.index.val = 338 then 32
    else if x.index.val = 343 then 33
    else if x.index.val = 348 then 34
    else if x.index.val = 360 then 35
    else if x.index.val = 376 then 36
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 37,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 37) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 7 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state0Used : Fin 7 → Fin 37 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state1Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨119⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (17) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨173⟩ : Source)) (Fin.cases ((⟨348⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (22) (Fin.cases (34) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨132⟩ : Source)) (Fin.cases ((⟨213⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (19) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state5Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨241⟩ : Source)) (Fin.cases ((⟨270⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state5Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (27) (Fin.cases (29) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state6Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨333⟩ : Source)) (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state6Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (31) (Fin.cases (20) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state7Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨119⟩ : Source)) (Fin.cases ((⟨173⟩ : Source)) (Fin.cases ((⟨348⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state7Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (17) (Fin.cases (22) (Fin.cases (34) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state8Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨119⟩ : Source)) (Fin.cases ((⟨132⟩ : Source)) (Fin.cases ((⟨213⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state8Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (17) (Fin.cases (19) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state9Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨119⟩ : Source)) (Fin.cases ((⟨241⟩ : Source)) (Fin.cases ((⟨270⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state9Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (17) (Fin.cases (27) (Fin.cases (29) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state10Generators : Fin 7 → Source :=
  (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨69⟩ : Source)) (Fin.cases ((⟨119⟩ : Source)) (Fin.cases ((⟨333⟩ : Source)) (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state10Used : Fin 7 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (13) (Fin.cases (17) (Fin.cases (31) (Fin.cases (20) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state11Generators : Fin 7 → Source :=
  (Fin.cases ((⟨206⟩ : Source)) (Fin.cases ((⟨229⟩ : Source)) (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨290⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state11Used : Fin 7 → Fin 37 :=
  (Fin.cases (24) (Fin.cases (26) (Fin.cases (36) (Fin.cases (30) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state12Generators : Fin 7 → Source :=
  (Fin.cases ((⟨206⟩ : Source)) (Fin.cases ((⟨229⟩ : Source)) (Fin.cases ((⟨376⟩ : Source)) (Fin.cases ((⟨290⟩ : Source)) (Fin.cases ((⟨28⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state12Used : Fin 7 → Fin 37 :=
  (Fin.cases (24) (Fin.cases (26) (Fin.cases (36) (Fin.cases (30) (Fin.cases (9) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state13Generators : Fin 7 → Source :=
  (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨333⟩ : Source)) (Fin.cases ((⟨196⟩ : Source)) (Fin.cases ((⟨206⟩ : Source)) (Fin.cases ((⟨242⟩ : Source)) (Fin.cases ((⟨47⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state13Used : Fin 7 → Fin 37 :=
  (Fin.cases (20) (Fin.cases (31) (Fin.cases (23) (Fin.cases (24) (Fin.cases (28) (Fin.cases (11) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state14Generators : Fin 7 → Source :=
  (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨333⟩ : Source)) (Fin.cases ((⟨196⟩ : Source)) (Fin.cases ((⟨206⟩ : Source)) (Fin.cases ((⟨242⟩ : Source)) (Fin.cases ((⟨47⟩ : Source)) (Fin.cases ((⟨28⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state14Used : Fin 7 → Fin 37 :=
  (Fin.cases (20) (Fin.cases (31) (Fin.cases (23) (Fin.cases (24) (Fin.cases (28) (Fin.cases (11) (Fin.cases (9) (fun i => Fin.elim0 i))))))))

private def state15Generators : Fin 7 → Source :=
  (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨143⟩ : Source)) (Fin.cases ((⟨333⟩ : Source)) (Fin.cases ((⟨196⟩ : Source)) (Fin.cases ((⟨206⟩ : Source)) (Fin.cases ((⟨242⟩ : Source)) (Fin.cases ((⟨47⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state15Used : Fin 7 → Fin 37 :=
  (Fin.cases (5) (Fin.cases (20) (Fin.cases (31) (Fin.cases (23) (Fin.cases (24) (Fin.cases (28) (Fin.cases (11) (fun i => Fin.elim0 i))))))))

private def state16Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state16Used : Fin 7 → Fin 37 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 17 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (Fin.cases (state14Generators) (Fin.cases (state15Generators) (Fin.cases (state16Generators) (fun i => Fin.elim0 i))))))))))))))))))

def stateUsed : Fin 17 → Fin 7 → Fin 37 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (Fin.cases (state14Used) (Fin.cases (state15Used) (Fin.cases (state16Used) (fun i => Fin.elim0 i))))))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 17) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 18 → Fin 37 :=
  (Fin.cases (0) (Fin.cases (9) (Fin.cases (23) (Fin.cases (8) (Fin.cases (5) (Fin.cases (15) (Fin.cases (1) (Fin.cases (12) (Fin.cases (35) (Fin.cases (36) (Fin.cases (7) (Fin.cases (20) (Fin.cases (16) (Fin.cases (32) (Fin.cases (10) (Fin.cases (21) (Fin.cases (18) (Fin.cases (33) (fun i => Fin.elim0 i)))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 18,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 37 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 17 → Fin 18 → Fin 17 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (12) (Fin.cases (11) (Fin.cases (2) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (12) (Fin.cases (1) (Fin.cases (9) (Fin.cases (6) (Fin.cases (4) (Fin.cases (7) (Fin.cases (10) (Fin.cases (5) (Fin.cases (3) (Fin.cases (8) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (12) (Fin.cases (11) (Fin.cases (2) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (12) (Fin.cases (1) (Fin.cases (9) (Fin.cases (6) (Fin.cases (4) (Fin.cases (7) (Fin.cases (10) (Fin.cases (5) (Fin.cases (3) (Fin.cases (8) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (12) (Fin.cases (12) (Fin.cases (2) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (12) (Fin.cases (2) (Fin.cases (9) (Fin.cases (10) (Fin.cases (8) (Fin.cases (7) (Fin.cases (10) (Fin.cases (9) (Fin.cases (7) (Fin.cases (8) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (14) (Fin.cases (13) (Fin.cases (7) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (14) (Fin.cases (3) (Fin.cases (14) (Fin.cases (13) (Fin.cases (13) (Fin.cases (7) (Fin.cases (14) (Fin.cases (13) (Fin.cases (3) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (14) (Fin.cases (13) (Fin.cases (8) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (14) (Fin.cases (4) (Fin.cases (14) (Fin.cases (13) (Fin.cases (4) (Fin.cases (14) (Fin.cases (14) (Fin.cases (13) (Fin.cases (13) (Fin.cases (8) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (14) (Fin.cases (13) (Fin.cases (9) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (14) (Fin.cases (5) (Fin.cases (9) (Fin.cases (13) (Fin.cases (13) (Fin.cases (14) (Fin.cases (14) (Fin.cases (5) (Fin.cases (13) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (14) (Fin.cases (13) (Fin.cases (10) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (14) (Fin.cases (6) (Fin.cases (14) (Fin.cases (6) (Fin.cases (13) (Fin.cases (14) (Fin.cases (10) (Fin.cases (13) (Fin.cases (13) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (14) (Fin.cases (14) (Fin.cases (7) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (Fin.cases (14) (Fin.cases (7) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (14) (Fin.cases (14) (Fin.cases (8) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (14) (Fin.cases (8) (Fin.cases (14) (Fin.cases (14) (Fin.cases (8) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (8) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (14) (Fin.cases (14) (Fin.cases (9) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (14) (Fin.cases (9) (Fin.cases (9) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (9) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (14) (Fin.cases (10) (Fin.cases (14) (Fin.cases (10) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (12) (Fin.cases (11) (Fin.cases (12) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (12) (Fin.cases (11) (Fin.cases (14) (Fin.cases (13) (Fin.cases (13) (Fin.cases (14) (Fin.cases (14) (Fin.cases (13) (Fin.cases (13) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (14) (Fin.cases (13) (Fin.cases (14) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (14) (Fin.cases (13) (Fin.cases (14) (Fin.cases (13) (Fin.cases (13) (Fin.cases (14) (Fin.cases (14) (Fin.cases (13) (Fin.cases (13) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (15) (Fin.cases (16) (Fin.cases (15) (Fin.cases (16) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (16) (Fin.cases (15) (Fin.cases (16) (Fin.cases (15) (Fin.cases (15) (Fin.cases (16) (Fin.cases (16) (Fin.cases (15) (Fin.cases (15) (Fin.cases (16) (fun i => Fin.elim0 i)))))))))))))))))))) (Fin.cases ((Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (Fin.cases (16) (fun i => Fin.elim0 i)))))))))))))))))))) (fun i => Fin.elim0 i))))))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow9NormalCore

end
