import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow10TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow10TopCertificate.group

def topAmbient : Fin 3 → Source := PrimitiveAffineSixteenFrameRow10TopCertificate.ambient
def topRepresentative : Fin 14 → Source := PrimitiveAffineSixteenFrameRow10TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow10TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow10TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow10TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 29 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow10TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 29 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow10TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 29,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow10TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow10TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 29 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 29 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445608240663368480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5001018833786157450 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059631779712758885 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310711081721798960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468314855821642650 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284460371259920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714808103440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920134157078303520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306427017386947685 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310694523837423920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666474070785 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284460623892530 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387390104505164080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271338832400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306412779069003335 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672508705284865 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378211813393165820 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059580304028358215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059631779211404660 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370496411664675 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364704749206831395 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306427016885593460 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986825941520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721307126604545 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938744541475 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))

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
      (((PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow10TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow10TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow10TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow10TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow10TopCertificate.certificate.encode_elements (usedSource k).index
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
    else if x.index.val = 8 then 6
    else if x.index.val = 12 then 7
    else if x.index.val = 13 then 8
    else if x.index.val = 21 then 9
    else if x.index.val = 37 then 10
    else if x.index.val = 46 then 11
    else if x.index.val = 74 then 12
    else if x.index.val = 76 then 13
    else if x.index.val = 98 then 14
    else if x.index.val = 101 then 15
    else if x.index.val = 102 then 16
    else if x.index.val = 121 then 17
    else if x.index.val = 127 then 18
    else if x.index.val = 190 then 19
    else if x.index.val = 207 then 20
    else if x.index.val = 267 then 21
    else if x.index.val = 274 then 22
    else if x.index.val = 292 then 23
    else if x.index.val = 317 then 24
    else if x.index.val = 341 then 25
    else if x.index.val = 345 then 26
    else if x.index.val = 369 then 27
    else if x.index.val = 377 then 28
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
  (Fin.cases ((⟨369⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 29 :=
  (Fin.cases (27) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨369⟩ : Source)) (Fin.cases ((⟨377⟩ : Source)) (Fin.cases ((⟨101⟩ : Source)) (Fin.cases ((⟨102⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 29 :=
  (Fin.cases (27) (Fin.cases (28) (Fin.cases (15) (Fin.cases (16) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨292⟩ : Source)) (Fin.cases ((⟨127⟩ : Source)) (Fin.cases ((⟨13⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 29 :=
  (Fin.cases (23) (Fin.cases (18) (Fin.cases (8) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨101⟩ : Source)) (Fin.cases ((⟨8⟩ : Source)) (Fin.cases ((⟨127⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 29 :=
  (Fin.cases (7) (Fin.cases (15) (Fin.cases (6) (Fin.cases (18) (Fin.cases (13) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state5Generators : Fin 7 → Source :=
  (Fin.cases ((⟨37⟩ : Source)) (Fin.cases ((⟨190⟩ : Source)) (Fin.cases ((⟨274⟩ : Source)) (Fin.cases ((⟨345⟩ : Source)) (Fin.cases ((⟨8⟩ : Source)) (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨341⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state5Used : Fin 7 → Fin 29 :=
  (Fin.cases (10) (Fin.cases (19) (Fin.cases (22) (Fin.cases (26) (Fin.cases (6) (Fin.cases (7) (Fin.cases (25) (fun i => Fin.elim0 i))))))))

private def state6Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state6Used : Fin 7 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 7 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (fun i => Fin.elim0 i))))))))

def stateUsed : Fin 7 → Fin 7 → Fin 29 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (fun i => Fin.elim0 i))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 7) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 14 → Fin 29 :=
  (Fin.cases (0) (Fin.cases (7) (Fin.cases (16) (Fin.cases (8) (Fin.cases (4) (Fin.cases (11) (Fin.cases (1) (Fin.cases (9) (Fin.cases (12) (Fin.cases (28) (Fin.cases (24) (Fin.cases (21) (Fin.cases (17) (Fin.cases (20) (fun i => Fin.elim0 i)))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 14,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 3 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (fun i => Fin.elim0 i))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 3,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 7 → Fin 14 → Fin 7 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (4) (Fin.cases (2) (Fin.cases (3) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (4) (Fin.cases (1) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (3) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (4) (Fin.cases (1) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (4) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (4) (Fin.cases (3) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (fun i => Fin.elim0 i)))))))))))))))) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow10NormalCore

end
