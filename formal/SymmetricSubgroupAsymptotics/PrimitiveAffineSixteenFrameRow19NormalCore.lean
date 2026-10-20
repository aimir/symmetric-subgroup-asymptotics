import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow19TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow19TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow19TopCertificate.ambient
def topRepresentative : Fin 11 → Source := PrimitiveAffineSixteenFrameRow19TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow19TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow19TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow19TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow19TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow19TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 21 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow19TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 21 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow19TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 21,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow19TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow19TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 21 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 21 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11208016699985375520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445607144943391520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136222090449941860 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8522237677986953610 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16126957421119349520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7238972199523721520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12158009242119647520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6288940358881059120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996056115368230350 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803850153870935 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6217201539336931995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17076881673873269520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311318949584359390 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370495843471410 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741987141493505 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271907016995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310711014741293480 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 21) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 21) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 21) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 21) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow19TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow19TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow19TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow19TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow19TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow19TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 21) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 21) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 21 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 9 then 6
    else if x.index.val = 10 then 7
    else if x.index.val = 19 then 8
    else if x.index.val = 20 then 9
    else if x.index.val = 24 then 10
    else if x.index.val = 39 then 11
    else if x.index.val = 45 then 12
    else if x.index.val = 48 then 13
    else if x.index.val = 69 then 14
    else if x.index.val = 73 then 15
    else if x.index.val = 74 then 16
    else if x.index.val = 84 then 17
    else if x.index.val = 122 then 18
    else if x.index.val = 137 then 19
    else if x.index.val = 159 then 20
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 21,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 21) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 6 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state0Used : Fin 6 → Fin 21 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state1Generators : Fin 6 → Source :=
  (Fin.cases ((⟨137⟩ : Source)) (Fin.cases ((⟨19⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state1Used : Fin 6 → Fin 21 :=
  (Fin.cases (19) (Fin.cases (8) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state2Generators : Fin 6 → Source :=
  (Fin.cases ((⟨137⟩ : Source)) (Fin.cases ((⟨19⟩ : Source)) (Fin.cases ((⟨73⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state2Used : Fin 6 → Fin 21 :=
  (Fin.cases (19) (Fin.cases (8) (Fin.cases (15) (Fin.cases (3) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state3Generators : Fin 6 → Source :=
  (Fin.cases ((⟨137⟩ : Source)) (Fin.cases ((⟨19⟩ : Source)) (Fin.cases ((⟨39⟩ : Source)) (Fin.cases ((⟨73⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state3Used : Fin 6 → Fin 21 :=
  (Fin.cases (19) (Fin.cases (8) (Fin.cases (11) (Fin.cases (15) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state4Generators : Fin 6 → Source :=
  (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨84⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state4Used : Fin 6 → Fin 21 :=
  (Fin.cases (5) (Fin.cases (17) (Fin.cases (16) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state5Generators : Fin 6 → Source :=
  (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨73⟩ : Source)) (Fin.cases ((⟨122⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state5Used : Fin 6 → Fin 21 :=
  (Fin.cases (3) (Fin.cases (15) (Fin.cases (18) (Fin.cases (16) (Fin.cases (5) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

private def state6Generators : Fin 6 → Source :=
  (Fin.cases ((⟨39⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨73⟩ : Source)) (Fin.cases ((⟨122⟩ : Source)) (Fin.cases ((⟨74⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state6Used : Fin 6 → Fin 21 :=
  (Fin.cases (11) (Fin.cases (3) (Fin.cases (15) (Fin.cases (18) (Fin.cases (16) (Fin.cases (5) (fun i => Fin.elim0 i)))))))

private def state7Generators : Fin 6 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))

private def state7Used : Fin 6 → Fin 21 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))

def stateGenerators : Fin 8 → Fin 6 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (fun i => Fin.elim0 i)))))))))

def stateUsed : Fin 8 → Fin 6 → Fin 21 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (fun i => Fin.elim0 i)))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 8) (k : Fin 6),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 11 → Fin 21 :=
  (Fin.cases (0) (Fin.cases (5) (Fin.cases (6) (Fin.cases (14) (Fin.cases (10) (Fin.cases (7) (Fin.cases (19) (Fin.cases (3) (Fin.cases (12) (Fin.cases (20) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 11,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 21 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 8 → Fin 11 → Fin 8 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (4) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (3) (Fin.cases (1) (Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (4) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (3) (Fin.cases (1) (Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (3) (Fin.cases (2) (Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (6) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow19NormalCore

end
