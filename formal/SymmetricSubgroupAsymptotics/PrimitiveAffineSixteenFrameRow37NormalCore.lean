import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow37TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow37TopCertificate.group

def topAmbient : Fin 3 → Source := PrimitiveAffineSixteenFrameRow37TopCertificate.ambient
def topRepresentative : Fin 17 → Source := PrimitiveAffineSixteenFrameRow37TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow37TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow37TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow37TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 33 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow37TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 33 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow37TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 33,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow37TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow37TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 33 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 33 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16112567834934535200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17245448010592987920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951921914625 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11319144720916269120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14882784897259894065 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18042473609256290640 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (4796044659625012320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9529565590517545920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2761246010805860160 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8268155571539123280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6679543513824984720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5522247783433334400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15149132132877934320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13569983039165931120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16714764584102298000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14140148451679305600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6603550811139940320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12995947130039531670 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14317269079835989920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258477015090 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360674316629665605 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8526495043095935640 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13734924859407823440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12852418020535205520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8866710900049209885 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (81985529216486895 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13548822940167062520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16990133295032968965 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16067812629363036720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8132035696035162435 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3154049716624156425 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17136026465629577475 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 33) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 33) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 33) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 33) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow37TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow37TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow37TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow37TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow37TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 33) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 33) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 33 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 6 then 5
    else if x.index.val = 39 then 6
    else if x.index.val = 51 then 7
    else if x.index.val = 111 then 8
    else if x.index.val = 126 then 9
    else if x.index.val = 176 then 10
    else if x.index.val = 264 then 11
    else if x.index.val = 267 then 12
    else if x.index.val = 291 then 13
    else if x.index.val = 357 then 14
    else if x.index.val = 390 then 15
    else if x.index.val = 545 then 16
    else if x.index.val = 590 then 17
    else if x.index.val = 644 then 18
    else if x.index.val = 918 then 19
    else if x.index.val = 1429 then 20
    else if x.index.val = 1436 then 21
    else if x.index.val = 2165 then 22
    else if x.index.val = 2383 then 23
    else if x.index.val = 2873 then 24
    else if x.index.val = 3265 then 25
    else if x.index.val = 3340 then 26
    else if x.index.val = 3652 then 27
    else if x.index.val = 3729 then 28
    else if x.index.val = 3789 then 29
    else if x.index.val = 3924 then 30
    else if x.index.val = 4811 then 31
    else if x.index.val = 5103 then 32
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 33,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 33) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 7 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state0Used : Fin 7 → Fin 33 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state1Generators : Fin 7 → Source :=
  (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨1436⟩ : Source)) (Fin.cases ((⟨2165⟩ : Source)) (Fin.cases ((⟨1429⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 33 :=
  (Fin.cases (3) (Fin.cases (21) (Fin.cases (22) (Fin.cases (20) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨357⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨1429⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 33 :=
  (Fin.cases (14) (Fin.cases (3) (Fin.cases (20) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨39⟩ : Source)) (Fin.cases ((⟨176⟩ : Source)) (Fin.cases ((⟨918⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨1436⟩ : Source)) (Fin.cases ((⟨2165⟩ : Source)) (Fin.cases ((⟨3340⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 33 :=
  (Fin.cases (6) (Fin.cases (10) (Fin.cases (19) (Fin.cases (3) (Fin.cases (21) (Fin.cases (22) (Fin.cases (26) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨3265⟩ : Source)) (Fin.cases ((⟨3924⟩ : Source)) (Fin.cases ((⟨3652⟩ : Source)) (Fin.cases ((⟨126⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 33 :=
  (Fin.cases (25) (Fin.cases (30) (Fin.cases (27) (Fin.cases (9) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state5Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state5Used : Fin 7 → Fin 33 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 6 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (fun i => Fin.elim0 i)))))))

def stateUsed : Fin 6 → Fin 7 → Fin 33 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (fun i => Fin.elim0 i)))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 6) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 17 → Fin 33 :=
  (Fin.cases (0) (Fin.cases (3) (Fin.cases (7) (Fin.cases (24) (Fin.cases (31) (Fin.cases (11) (Fin.cases (29) (Fin.cases (32) (Fin.cases (12) (Fin.cases (23) (Fin.cases (28) (Fin.cases (16) (Fin.cases (13) (Fin.cases (18) (Fin.cases (17) (Fin.cases (1) (Fin.cases (8) (fun i => Fin.elim0 i))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 17,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 3 → Fin 33 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (fun i => Fin.elim0 i))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 3,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 6 → Fin 17 → Fin 6 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (1) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (1) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (fun i => Fin.elim0 i))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i))))))))))))))))))) (fun i => Fin.elim0 i)))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow37NormalCore

end
