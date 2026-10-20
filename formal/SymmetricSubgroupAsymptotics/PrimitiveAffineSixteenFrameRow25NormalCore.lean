import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow25TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow25TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow25TopCertificate.ambient
def topRepresentative : Fin 24 → Source := PrimitiveAffineSixteenFrameRow25TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow25TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow25TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow25TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 44 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow25TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 44 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow25TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 44,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow25TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow25TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 44 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 44 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12158027861086974240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360521110229095200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613161031497060 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7445595892319369610 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5001151428016476720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2391673070423411610 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378212843935624700 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378188770929815840 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136222090449941860 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11000921913080764260 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (82079143502370420 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12364635061046040420 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714239902465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849364501860 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158035377246498300 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459149666465489200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2522483877531702900 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531463559524969980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701378097680 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12364653680514717540 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370495843471410 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1310717608079977935 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1310750465081142735 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306412778782946660 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721306558411280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (225647872509996495 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11000940532549441380 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531496416526134780 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (225615015508831695 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158002521248034300 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509020844560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378179987937160700 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3463984623318920655 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3464017479317384655 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284461192094465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258224378625 : Fin (16 ^ 16))) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 44) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 44) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 44) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 44) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow25TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow25TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow25TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow25TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow25TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 44) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 44) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 44 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 6 then 6
    else if x.index.val = 12 then 7
    else if x.index.val = 17 then 8
    else if x.index.val = 18 then 9
    else if x.index.val = 19 then 10
    else if x.index.val = 21 then 11
    else if x.index.val = 34 then 12
    else if x.index.val = 37 then 13
    else if x.index.val = 38 then 14
    else if x.index.val = 76 then 15
    else if x.index.val = 96 then 16
    else if x.index.val = 114 then 17
    else if x.index.val = 116 then 18
    else if x.index.val = 129 then 19
    else if x.index.val = 181 then 20
    else if x.index.val = 182 then 21
    else if x.index.val = 245 then 22
    else if x.index.val = 260 then 23
    else if x.index.val = 285 then 24
    else if x.index.val = 289 then 25
    else if x.index.val = 297 then 26
    else if x.index.val = 317 then 27
    else if x.index.val = 355 then 28
    else if x.index.val = 389 then 29
    else if x.index.val = 395 then 30
    else if x.index.val = 435 then 31
    else if x.index.val = 453 then 32
    else if x.index.val = 459 then 33
    else if x.index.val = 507 then 34
    else if x.index.val = 517 then 35
    else if x.index.val = 537 then 36
    else if x.index.val = 541 then 37
    else if x.index.val = 576 then 38
    else if x.index.val = 578 then 39
    else if x.index.val = 625 then 40
    else if x.index.val = 713 then 41
    else if x.index.val = 725 then 42
    else if x.index.val = 764 then 43
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 44,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 44) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 8 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state0Used : Fin 8 → Fin 44 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state1Generators : Fin 8 → Source :=
  (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state1Used : Fin 8 → Fin 44 :=
  (Fin.cases (9) (Fin.cases (29) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state2Generators : Fin 8 → Source :=
  (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨576⟩ : Source)) (Fin.cases ((⟨21⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state2Used : Fin 8 → Fin 44 :=
  (Fin.cases (9) (Fin.cases (29) (Fin.cases (38) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state3Generators : Fin 8 → Source :=
  (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨114⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state3Used : Fin 8 → Fin 44 :=
  (Fin.cases (9) (Fin.cases (29) (Fin.cases (18) (Fin.cases (17) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state4Generators : Fin 8 → Source :=
  (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨181⟩ : Source)) (Fin.cases ((⟨260⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state4Used : Fin 8 → Fin 44 :=
  (Fin.cases (9) (Fin.cases (29) (Fin.cases (20) (Fin.cases (23) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state5Generators : Fin 8 → Source :=
  (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨114⟩ : Source)) (Fin.cases ((⟨181⟩ : Source)) (Fin.cases ((⟨260⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state5Used : Fin 8 → Fin 44 :=
  (Fin.cases (9) (Fin.cases (29) (Fin.cases (18) (Fin.cases (17) (Fin.cases (20) (Fin.cases (23) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state6Generators : Fin 8 → Source :=
  (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨182⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨181⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state6Used : Fin 8 → Fin 44 :=
  (Fin.cases (9) (Fin.cases (29) (Fin.cases (21) (Fin.cases (18) (Fin.cases (20) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state7Generators : Fin 8 → Source :=
  (Fin.cases ((⟨297⟩ : Source)) (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state7Used : Fin 8 → Fin 44 :=
  (Fin.cases (26) (Fin.cases (9) (Fin.cases (29) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state8Generators : Fin 8 → Source :=
  (Fin.cases ((⟨297⟩ : Source)) (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨576⟩ : Source)) (Fin.cases ((⟨395⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state8Used : Fin 8 → Fin 44 :=
  (Fin.cases (26) (Fin.cases (9) (Fin.cases (29) (Fin.cases (38) (Fin.cases (30) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state9Generators : Fin 8 → Source :=
  (Fin.cases ((⟨297⟩ : Source)) (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨389⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨114⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state9Used : Fin 8 → Fin 44 :=
  (Fin.cases (26) (Fin.cases (9) (Fin.cases (29) (Fin.cases (18) (Fin.cases (17) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state10Generators : Fin 8 → Source :=
  (Fin.cases ((⟨541⟩ : Source)) (Fin.cases ((⟨435⟩ : Source)) (Fin.cases ((⟨260⟩ : Source)) (Fin.cases ((⟨764⟩ : Source)) (Fin.cases ((⟨713⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state10Used : Fin 8 → Fin 44 :=
  (Fin.cases (37) (Fin.cases (31) (Fin.cases (23) (Fin.cases (43) (Fin.cases (41) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state11Generators : Fin 8 → Source :=
  (Fin.cases ((⟨114⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨297⟩ : Source)) (Fin.cases ((⟨725⟩ : Source)) (Fin.cases ((⟨435⟩ : Source)) (Fin.cases ((⟨541⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state11Used : Fin 8 → Fin 44 :=
  (Fin.cases (17) (Fin.cases (18) (Fin.cases (26) (Fin.cases (42) (Fin.cases (31) (Fin.cases (37) (Fin.cases (5) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state12Generators : Fin 8 → Source :=
  (Fin.cases ((⟨182⟩ : Source)) (Fin.cases ((⟨114⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨297⟩ : Source)) (Fin.cases ((⟨725⟩ : Source)) (Fin.cases ((⟨435⟩ : Source)) (Fin.cases ((⟨541⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state12Used : Fin 8 → Fin 44 :=
  (Fin.cases (21) (Fin.cases (17) (Fin.cases (18) (Fin.cases (26) (Fin.cases (42) (Fin.cases (31) (Fin.cases (37) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))

private def state13Generators : Fin 8 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state13Used : Fin 8 → Fin 44 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

def stateGenerators : Fin 14 → Fin 8 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (fun i => Fin.elim0 i)))))))))))))))

def stateUsed : Fin 14 → Fin 8 → Fin 44 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (fun i => Fin.elim0 i)))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 14) (k : Fin 8),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 24 → Fin 44 :=
  (Fin.cases (0) (Fin.cases (5) (Fin.cases (24) (Fin.cases (13) (Fin.cases (29) (Fin.cases (16) (Fin.cases (18) (Fin.cases (22) (Fin.cases (38) (Fin.cases (36) (Fin.cases (34) (Fin.cases (8) (Fin.cases (21) (Fin.cases (14) (Fin.cases (27) (Fin.cases (40) (Fin.cases (32) (Fin.cases (28) (Fin.cases (39) (Fin.cases (35) (Fin.cases (25) (Fin.cases (33) (Fin.cases (15) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 24,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 44 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 14 → Fin 24 → Fin 14 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (10) (Fin.cases (4) (Fin.cases (7) (Fin.cases (1) (Fin.cases (10) (Fin.cases (3) (Fin.cases (11) (Fin.cases (2) (Fin.cases (8) (Fin.cases (5) (Fin.cases (9) (Fin.cases (6) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (10) (Fin.cases (4) (Fin.cases (7) (Fin.cases (1) (Fin.cases (10) (Fin.cases (3) (Fin.cases (11) (Fin.cases (2) (Fin.cases (8) (Fin.cases (5) (Fin.cases (9) (Fin.cases (6) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (11) (Fin.cases (5) (Fin.cases (8) (Fin.cases (2) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (2) (Fin.cases (8) (Fin.cases (5) (Fin.cases (11) (Fin.cases (6) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (11) (Fin.cases (5) (Fin.cases (9) (Fin.cases (3) (Fin.cases (11) (Fin.cases (3) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (9) (Fin.cases (6) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (10) (Fin.cases (4) (Fin.cases (10) (Fin.cases (4) (Fin.cases (10) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (6) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (5) (Fin.cases (11) (Fin.cases (6) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (12) (Fin.cases (6) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (10) (Fin.cases (9) (Fin.cases (11) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (11) (Fin.cases (11) (Fin.cases (9) (Fin.cases (9) (Fin.cases (11) (Fin.cases (9) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (12) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (fun i => Fin.elim0 i)))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow25NormalCore

end
