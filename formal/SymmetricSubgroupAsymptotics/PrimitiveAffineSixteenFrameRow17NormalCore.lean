import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow17TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow17TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow17TopCertificate.ambient
def topRepresentative : Fin 14 → Source := PrimitiveAffineSixteenFrameRow17TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow17TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow17TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow17TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow17TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow17TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 19 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow17TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 19 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow17TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 19,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow17TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow17TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 19 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 19 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445592649428767520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229770993654068580 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7445629006266546570 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18297112935027778320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6288940358659875120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7238972199744905520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14906726159964840720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387373609776097465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5140538944302128010 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441539476097868035 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946949744215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311269535231638765 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849648592710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086222966900596995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 19) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 19) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 19) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 19) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow17TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow17TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow17TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow17TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow17TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow17TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 19) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 19) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 19 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 8 then 5
    else if x.index.val = 9 then 6
    else if x.index.val = 17 then 7
    else if x.index.val = 18 then 8
    else if x.index.val = 29 then 9
    else if x.index.val = 37 then 10
    else if x.index.val = 57 then 11
    else if x.index.val = 74 then 12
    else if x.index.val = 90 then 13
    else if x.index.val = 98 then 14
    else if x.index.val = 112 then 15
    else if x.index.val = 116 then 16
    else if x.index.val = 153 then 17
    else if x.index.val = 190 then 18
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 19,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 19) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 6 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state0Used : Fin 6 → Fin 19 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state1Generators : Fin 6 → Source :=
  (Fin.cases ((⟨112⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state1Used : Fin 6 → Fin 19 :=
  (Fin.cases (15) (Fin.cases (18) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state2Generators : Fin 6 → Source :=
  (Fin.cases ((⟨112⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨29⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state2Used : Fin 6 → Fin 19 :=
  (Fin.cases (15) (Fin.cases (18) (Fin.cases (9) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state3Generators : Fin 6 → Source :=
  (Fin.cases ((⟨90⟩ : Source)) (Fin.cases ((⟨98⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨112⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state3Used : Fin 6 → Fin 19 :=
  (Fin.cases (13) (Fin.cases (14) (Fin.cases (18) (Fin.cases (15) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state4Generators : Fin 6 → Source :=
  (Fin.cases ((⟨90⟩ : Source)) (Fin.cases ((⟨98⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨112⟩ : Source)) (Fin.cases ((⟨29⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state4Used : Fin 6 → Fin 19 :=
  (Fin.cases (13) (Fin.cases (14) (Fin.cases (18) (Fin.cases (15) (Fin.cases (9) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state5Generators : Fin 6 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨90⟩ : Source)) (Fin.cases ((⟨98⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨112⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state5Used : Fin 6 → Fin 19 :=
  (Fin.cases (6) (Fin.cases (13) (Fin.cases (14) (Fin.cases (18) (Fin.cases (15) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state6Generators : Fin 6 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨90⟩ : Source)) (Fin.cases ((⟨98⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨112⟩ : Source)) (Fin.cases ((⟨8⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state6Used : Fin 6 → Fin 19 :=
  (Fin.cases (6) (Fin.cases (13) (Fin.cases (14) (Fin.cases (18) (Fin.cases (15) (Fin.cases (5) (fun i => Fin.elim0 i)))))))

private def state7Generators : Fin 6 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨90⟩ : Source)) (Fin.cases ((⟨98⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨112⟩ : Source)) (Fin.cases ((⟨29⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state7Used : Fin 6 → Fin 19 :=
  (Fin.cases (6) (Fin.cases (13) (Fin.cases (14) (Fin.cases (18) (Fin.cases (15) (Fin.cases (9) (fun i => Fin.elim0 i)))))))

private def state8Generators : Fin 6 → Source :=
  (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨90⟩ : Source)) (Fin.cases ((⟨98⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨112⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state8Used : Fin 6 → Fin 19 :=
  (Fin.cases (8) (Fin.cases (6) (Fin.cases (13) (Fin.cases (14) (Fin.cases (18) (Fin.cases (15) (fun i => Fin.elim0 i)))))))

private def state9Generators : Fin 6 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state9Used : Fin 6 → Fin 19 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

def stateGenerators : Fin 10 → Fin 6 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (fun i => Fin.elim0 i)))))))))))

def stateUsed : Fin 10 → Fin 6 → Fin 19 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (fun i => Fin.elim0 i)))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 10) (k : Fin 6),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 14 → Fin 19 :=
  (Fin.cases (0) (Fin.cases (9) (Fin.cases (5) (Fin.cases (8) (Fin.cases (6) (Fin.cases (7) (Fin.cases (15) (Fin.cases (12) (Fin.cases (17) (Fin.cases (3) (Fin.cases (13) (Fin.cases (10) (Fin.cases (11) (Fin.cases (16) (fun i => Fin.elim0 i)))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 14,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 19 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 10 → Fin 14 → Fin 10 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (2) (Fin.cases (6) (Fin.cases (8) (Fin.cases (5) (Fin.cases (7) (Fin.cases (1) (Fin.cases (6) (Fin.cases (8) (Fin.cases (4) (Fin.cases (3) (Fin.cases (8) (Fin.cases (6) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (2) (Fin.cases (6) (Fin.cases (8) (Fin.cases (5) (Fin.cases (7) (Fin.cases (1) (Fin.cases (6) (Fin.cases (8) (Fin.cases (4) (Fin.cases (3) (Fin.cases (8) (Fin.cases (6) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (2) (Fin.cases (9) (Fin.cases (9) (Fin.cases (7) (Fin.cases (7) (Fin.cases (2) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (4) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (4) (Fin.cases (6) (Fin.cases (8) (Fin.cases (5) (Fin.cases (7) (Fin.cases (3) (Fin.cases (6) (Fin.cases (8) (Fin.cases (4) (Fin.cases (3) (Fin.cases (8) (Fin.cases (6) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (9) (Fin.cases (9) (Fin.cases (7) (Fin.cases (7) (Fin.cases (4) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (4) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (7) (Fin.cases (6) (Fin.cases (8) (Fin.cases (5) (Fin.cases (7) (Fin.cases (5) (Fin.cases (6) (Fin.cases (8) (Fin.cases (7) (Fin.cases (5) (Fin.cases (8) (Fin.cases (6) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (6) (Fin.cases (9) (Fin.cases (6) (Fin.cases (6) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (9) (Fin.cases (9) (Fin.cases (8) (Fin.cases (8) (Fin.cases (9) (Fin.cases (8) (Fin.cases (9) (Fin.cases (8) (Fin.cases (9) (Fin.cases (8) (Fin.cases (8) (Fin.cases (9) (Fin.cases (8) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))) (fun i => Fin.elim0 i)))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow17NormalCore

end
