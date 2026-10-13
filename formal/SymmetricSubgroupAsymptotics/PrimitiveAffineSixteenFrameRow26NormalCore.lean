import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow26TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow26TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow26TopCertificate.ambient
def topRepresentative : Fin 19 → Source := PrimitiveAffineSixteenFrameRow26TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow26TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow26TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow26TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 37 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow26TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 37 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow26TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 37,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow26TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow26TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 37 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 37 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12158027861086974240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360521110229095200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946949756260 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8522237678237628810 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5001151428016476720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2391673070674086810 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378188770929815840 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459149666465489200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12364653679729264245 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951353712690 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12364635061831485045 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636072130135 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (225647872261291230 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721306558411280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509020844560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2378915144696921310 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284461192094465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3464017479566097630 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531480116872601295 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11000940531763988085 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378196544787373775 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1310717608328690910 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3607553227304691015 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741987141493505 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714239902465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370495843471410 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11000921913866208885 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311302391984086735 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938491900195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1167181865171248455 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))

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
      (((PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow26TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow26TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow26TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow26TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow26TopCertificate.certificate.encode_elements (usedSource k).index
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
    else if x.index.val = 20 then 8
    else if x.index.val = 38 then 9
    else if x.index.val = 113 then 10
    else if x.index.val = 148 then 11
    else if x.index.val = 185 then 12
    else if x.index.val = 191 then 13
    else if x.index.val = 217 then 14
    else if x.index.val = 234 then 15
    else if x.index.val = 274 then 16
    else if x.index.val = 288 then 17
    else if x.index.val = 294 then 18
    else if x.index.val = 314 then 19
    else if x.index.val = 324 then 20
    else if x.index.val = 416 then 21
    else if x.index.val = 421 then 22
    else if x.index.val = 502 then 23
    else if x.index.val = 511 then 24
    else if x.index.val = 567 then 25
    else if x.index.val = 601 then 26
    else if x.index.val = 609 then 27
    else if x.index.val = 651 then 28
    else if x.index.val = 688 then 29
    else if x.index.val = 698 then 30
    else if x.index.val = 716 then 31
    else if x.index.val = 717 then 32
    else if x.index.val = 724 then 33
    else if x.index.val = 760 then 34
    else if x.index.val = 762 then 35
    else if x.index.val = 765 then 36
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 37,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 37) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 8 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state0Used : Fin 8 → Fin 37 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state1Generators : Fin 8 → Source :=
  (Fin.cases ((⟨765⟩ : Source)) (Fin.cases ((⟨760⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state1Used : Fin 8 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (34) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state2Generators : Fin 8 → Source :=
  (Fin.cases ((⟨765⟩ : Source)) (Fin.cases ((⟨760⟩ : Source)) (Fin.cases ((⟨234⟩ : Source)) (Fin.cases ((⟨113⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state2Used : Fin 8 → Fin 37 :=
  (Fin.cases (36) (Fin.cases (34) (Fin.cases (15) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state3Generators : Fin 8 → Source :=
  (Fin.cases ((⟨38⟩ : Source)) (Fin.cases ((⟨716⟩ : Source)) (Fin.cases ((⟨688⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state3Used : Fin 8 → Fin 37 :=
  (Fin.cases (9) (Fin.cases (31) (Fin.cases (29) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state4Generators : Fin 8 → Source :=
  (Fin.cases ((⟨324⟩ : Source)) (Fin.cases ((⟨185⟩ : Source)) (Fin.cases ((⟨38⟩ : Source)) (Fin.cases ((⟨113⟩ : Source)) (Fin.cases ((⟨217⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state4Used : Fin 8 → Fin 37 :=
  (Fin.cases (20) (Fin.cases (12) (Fin.cases (9) (Fin.cases (10) (Fin.cases (14) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state5Generators : Fin 8 → Source :=
  (Fin.cases ((⟨288⟩ : Source)) (Fin.cases ((⟨601⟩ : Source)) (Fin.cases ((⟨716⟩ : Source)) (Fin.cases ((⟨421⟩ : Source)) (Fin.cases ((⟨314⟩ : Source)) (Fin.cases ((⟨324⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state5Used : Fin 8 → Fin 37 :=
  (Fin.cases (17) (Fin.cases (26) (Fin.cases (31) (Fin.cases (22) (Fin.cases (19) (Fin.cases (20) (Fin.cases (5) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state6Generators : Fin 8 → Source :=
  (Fin.cases ((⟨762⟩ : Source)) (Fin.cases ((⟨288⟩ : Source)) (Fin.cases ((⟨601⟩ : Source)) (Fin.cases ((⟨716⟩ : Source)) (Fin.cases ((⟨421⟩ : Source)) (Fin.cases ((⟨314⟩ : Source)) (Fin.cases ((⟨324⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state6Used : Fin 8 → Fin 37 :=
  (Fin.cases (35) (Fin.cases (17) (Fin.cases (26) (Fin.cases (31) (Fin.cases (22) (Fin.cases (19) (Fin.cases (20) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))

private def state7Generators : Fin 8 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state7Used : Fin 8 → Fin 37 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

def stateGenerators : Fin 8 → Fin 8 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (fun i => Fin.elim0 i)))))))))

def stateUsed : Fin 8 → Fin 8 → Fin 37 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (fun i => Fin.elim0 i)))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 8) (k : Fin 8),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 19 → Fin 37 :=
  (Fin.cases (0) (Fin.cases (5) (Fin.cases (12) (Fin.cases (9) (Fin.cases (36) (Fin.cases (30) (Fin.cases (26) (Fin.cases (33) (Fin.cases (24) (Fin.cases (35) (Fin.cases (28) (Fin.cases (21) (Fin.cases (18) (Fin.cases (27) (Fin.cases (23) (Fin.cases (32) (Fin.cases (16) (Fin.cases (25) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 19,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 37 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 8 → Fin 19 → Fin 8 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (4) (Fin.cases (2) (Fin.cases (3) (Fin.cases (1) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (3) (Fin.cases (1) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow26NormalCore

end
