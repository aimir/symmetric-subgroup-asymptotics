import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow34TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow34TopCertificate.group

def topAmbient : Fin 5 → Source := PrimitiveAffineSixteenFrameRow34TopCertificate.ambient
def topRepresentative : Fin 16 → Source := PrimitiveAffineSixteenFrameRow34TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow34TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow34TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow34TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 29 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow34TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 29 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow34TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 29,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow34TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow34TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 29 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 29 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6297404386287555360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (4017038152435091520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3935146449642519120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6229774303365960240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951921914625 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229636341007917360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1861591382891318400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2009893429389582240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5077191743279530545 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2787292743612029265 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223573000720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2850043857071369025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12364896506851107600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8450720815125246210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8357316065928252420 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5077224600564798240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6742441952650594500 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2804180985809570880 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (4321082199392153250 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920265588280751700 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360674316629665605 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9924471220835057970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905864995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9924487649903846160 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12364912934783484210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (86224148506717080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (81985529216486895 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11005351623184766070 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 29) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 29) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 29) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 29) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow34TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow34TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow34TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow34TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow34TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 29) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 29) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 29 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 6 then 6
    else if x.index.val = 7 then 7
    else if x.index.val = 8 then 8
    else if x.index.val = 10 then 9
    else if x.index.val = 14 then 10
    else if x.index.val = 15 then 11
    else if x.index.val = 17 then 12
    else if x.index.val = 18 then 13
    else if x.index.val = 20 then 14
    else if x.index.val = 21 then 15
    else if x.index.val = 31 then 16
    else if x.index.val = 36 then 17
    else if x.index.val = 43 then 18
    else if x.index.val = 45 then 19
    else if x.index.val = 54 then 20
    else if x.index.val = 55 then 21
    else if x.index.val = 58 then 22
    else if x.index.val = 61 then 23
    else if x.index.val = 132 then 24
    else if x.index.val = 276 then 25
    else if x.index.val = 284 then 26
    else if x.index.val = 287 then 27
    else if x.index.val = 487 then 28
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 29,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 29) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 7 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state0Used : Fin 7 → Fin 29 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state1Generators : Fin 7 → Source :=
  (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 29 :=
  (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 29 :=
  (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (2) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨15⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 29 :=
  (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (11) (Fin.cases (2) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state5Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨18⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state5Used : Fin 7 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (13) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state6Generators : Fin 7 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state6Used : Fin 7 → Fin 29 :=
  (Fin.cases (2) (Fin.cases (1) (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state7Generators : Fin 7 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨132⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state7Used : Fin 7 → Fin 29 :=
  (Fin.cases (2) (Fin.cases (1) (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (24) (fun i => Fin.elim0 i))))))))

private def state8Generators : Fin 7 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (Fin.cases ((⟨18⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state8Used : Fin 7 → Fin 29 :=
  (Fin.cases (2) (Fin.cases (1) (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (Fin.cases (13) (fun i => Fin.elim0 i))))))))

private def state9Generators : Fin 7 → Source :=
  (Fin.cases ((⟨15⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨287⟩ : Source)) (Fin.cases ((⟨55⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨61⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state9Used : Fin 7 → Fin 29 :=
  (Fin.cases (11) (Fin.cases (2) (Fin.cases (1) (Fin.cases (27) (Fin.cases (21) (Fin.cases (5) (Fin.cases (23) (fun i => Fin.elim0 i))))))))

private def state10Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state10Used : Fin 7 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 11 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (fun i => Fin.elim0 i))))))))))))

def stateUsed : Fin 11 → Fin 7 → Fin 29 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (fun i => Fin.elim0 i))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 11) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 16 → Fin 29 :=
  (Fin.cases (0) (Fin.cases (23) (Fin.cases (28) (Fin.cases (1) (Fin.cases (2) (Fin.cases (7) (Fin.cases (17) (Fin.cases (11) (Fin.cases (20) (Fin.cases (16) (Fin.cases (13) (Fin.cases (22) (Fin.cases (18) (Fin.cases (24) (Fin.cases (25) (Fin.cases (26) (fun i => Fin.elim0 i)))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 16,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 5 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (fun i => Fin.elim0 i))))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 5,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 11 → Fin 16 → Fin 11 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (1) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (6) (Fin.cases (6) (Fin.cases (3) (Fin.cases (3) (Fin.cases (9) (Fin.cases (5) (Fin.cases (5) (Fin.cases (8) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (1) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (6) (Fin.cases (6) (Fin.cases (3) (Fin.cases (3) (Fin.cases (9) (Fin.cases (5) (Fin.cases (5) (Fin.cases (8) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (6) (Fin.cases (2) (Fin.cases (6) (Fin.cases (6) (Fin.cases (3) (Fin.cases (3) (Fin.cases (9) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (9) (Fin.cases (3) (Fin.cases (9) (Fin.cases (9) (Fin.cases (3) (Fin.cases (3) (Fin.cases (9) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (5) (Fin.cases (5) (Fin.cases (8) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (5) (Fin.cases (5) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i)))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i)))))))))))))))))) (fun i => Fin.elim0 i))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow34NormalCore

end
