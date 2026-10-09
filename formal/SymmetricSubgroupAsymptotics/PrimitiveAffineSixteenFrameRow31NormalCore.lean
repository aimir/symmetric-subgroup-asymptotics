import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow31TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow31TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow31TopCertificate.ambient
def topRepresentative : Fin 14 → Source := PrimitiveAffineSixteenFrameRow31TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow31TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow31TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow31TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 27 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow31TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 27 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow31TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 27,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow31TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow31TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 27 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 27 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6297404386287555360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (4017038152435091520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3935146449642519120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951921914625 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229636341007917360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1861591382891318400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2009893429389582240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5077191743279530545 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14511680412402711120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2787292743612029265 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223573000720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2850043857071369025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8357316065928252420 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7190321770564529925 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5670432786557853600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5077224600564798240 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6742441952650594500 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360674316629665605 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9787083821219554800 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059480698564059440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258477015090 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905864995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16436949216743978250 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8659660252489996815 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086069757079886010 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11005351623184766070 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))

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
      (((PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow31TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow31TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow31TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow31TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow31TopCertificate.certificate.encode_elements (usedSource k).index
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
    else if x.index.val = 5 then 5
    else if x.index.val = 6 then 6
    else if x.index.val = 7 then 7
    else if x.index.val = 8 then 8
    else if x.index.val = 9 then 9
    else if x.index.val = 11 then 10
    else if x.index.val = 12 then 11
    else if x.index.val = 13 then 12
    else if x.index.val = 15 then 13
    else if x.index.val = 16 then 14
    else if x.index.val = 20 then 15
    else if x.index.val = 23 then 16
    else if x.index.val = 26 then 17
    else if x.index.val = 36 then 18
    else if x.index.val = 45 then 19
    else if x.index.val = 48 then 20
    else if x.index.val = 50 then 21
    else if x.index.val = 62 then 22
    else if x.index.val = 84 then 23
    else if x.index.val = 146 then 24
    else if x.index.val = 174 then 25
    else if x.index.val = 277 then 26
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 27,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 27) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 6 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state0Used : Fin 6 → Fin 27 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state1Generators : Fin 6 → Source :=
  (Fin.cases ((⟨36⟩ : Source)) (Fin.cases ((⟨174⟩ : Source)) (Fin.cases ((⟨50⟩ : Source)) (Fin.cases ((⟨62⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state1Used : Fin 6 → Fin 27 :=
  (Fin.cases (18) (Fin.cases (25) (Fin.cases (21) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state2Generators : Fin 6 → Source :=
  (Fin.cases ((⟨36⟩ : Source)) (Fin.cases ((⟨174⟩ : Source)) (Fin.cases ((⟨50⟩ : Source)) (Fin.cases ((⟨62⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state2Used : Fin 6 → Fin 27 :=
  (Fin.cases (18) (Fin.cases (25) (Fin.cases (21) (Fin.cases (22) (Fin.cases (2) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state3Generators : Fin 6 → Source :=
  (Fin.cases ((⟨36⟩ : Source)) (Fin.cases ((⟨174⟩ : Source)) (Fin.cases ((⟨50⟩ : Source)) (Fin.cases ((⟨62⟩ : Source)) (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state3Used : Fin 6 → Fin 27 :=
  (Fin.cases (18) (Fin.cases (25) (Fin.cases (21) (Fin.cases (22) (Fin.cases (11) (Fin.cases (2) (fun i => Fin.elim0 i)))))))

private def state4Generators : Fin 6 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨36⟩ : Source)) (Fin.cases ((⟨174⟩ : Source)) (Fin.cases ((⟨50⟩ : Source)) (Fin.cases ((⟨62⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state4Used : Fin 6 → Fin 27 :=
  (Fin.cases (1) (Fin.cases (18) (Fin.cases (25) (Fin.cases (21) (Fin.cases (22) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state5Generators : Fin 6 → Source :=
  (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨36⟩ : Source)) (Fin.cases ((⟨174⟩ : Source)) (Fin.cases ((⟨50⟩ : Source)) (Fin.cases ((⟨62⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state5Used : Fin 6 → Fin 27 :=
  (Fin.cases (2) (Fin.cases (1) (Fin.cases (18) (Fin.cases (25) (Fin.cases (21) (Fin.cases (22) (fun i => Fin.elim0 i)))))))

private def state6Generators : Fin 6 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state6Used : Fin 6 → Fin 27 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

def stateGenerators : Fin 7 → Fin 6 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (fun i => Fin.elim0 i))))))))

def stateUsed : Fin 7 → Fin 6 → Fin 27 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (fun i => Fin.elim0 i))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 7) (k : Fin 6),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 14 → Fin 27 :=
  (Fin.cases (0) (Fin.cases (11) (Fin.cases (5) (Fin.cases (20) (Fin.cases (1) (Fin.cases (16) (Fin.cases (9) (Fin.cases (19) (Fin.cases (15) (Fin.cases (4) (Fin.cases (14) (Fin.cases (24) (Fin.cases (23) (Fin.cases (26) (fun i => Fin.elim0 i)))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 14,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 27 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 7 → Fin 14 → Fin 7 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (3) (Fin.cases (4) (Fin.cases (6) (Fin.cases (4) (Fin.cases (6) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (1) (Fin.cases (3) (Fin.cases (5) (Fin.cases (5) (Fin.cases (1) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (3) (Fin.cases (4) (Fin.cases (6) (Fin.cases (4) (Fin.cases (6) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (1) (Fin.cases (3) (Fin.cases (5) (Fin.cases (5) (Fin.cases (1) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (3) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (6) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (2) (Fin.cases (3) (Fin.cases (5) (Fin.cases (5) (Fin.cases (2) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (3) (Fin.cases (6) (Fin.cases (6) (Fin.cases (3) (Fin.cases (3) (Fin.cases (6) (Fin.cases (6) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (6) (Fin.cases (4) (Fin.cases (6) (Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (4) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (fun i => Fin.elim0 i)))))))))))))))) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow31NormalCore

end
