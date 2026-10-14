import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow5TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow5TopCertificate.group

def topAmbient : Fin 3 → Source := PrimitiveAffineSixteenFrameRow5TopCertificate.ambient
def topRepresentative : Fin 10 → Source := PrimitiveAffineSixteenFrameRow5TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow5TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow5TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow5TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 15 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow5TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 15 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow5TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 15,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow5TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow5TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 15 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 15 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445575125964165920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441406881614903690 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229770993652102245 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5140522453682364720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230666158518800 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920134157078303520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946947782215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311287123121732845 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310748318804156720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136222089946621300 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849650554710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938744541475 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 15) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 15) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 15) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 15) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow5TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow5TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow5TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow5TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow5TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 15) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 15) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 15 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 11 then 5
    else if x.index.val = 27 then 6
    else if x.index.val = 30 then 7
    else if x.index.val = 34 then 8
    else if x.index.val = 52 then 9
    else if x.index.val = 59 then 10
    else if x.index.val = 72 then 11
    else if x.index.val = 88 then 12
    else if x.index.val = 92 then 13
    else if x.index.val = 93 then 14
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 15,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 15) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 5 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state0Used : Fin 5 → Fin 15 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))

private def state1Generators : Fin 5 → Source :=
  (Fin.cases ((⟨52⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state1Used : Fin 5 → Fin 15 :=
  (Fin.cases (9) (Fin.cases (14) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))

private def state2Generators : Fin 5 → Source :=
  (Fin.cases ((⟨52⟩ : Source)) (Fin.cases ((⟨93⟩ : Source)) (Fin.cases ((⟨11⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state2Used : Fin 5 → Fin 15 :=
  (Fin.cases (9) (Fin.cases (14) (Fin.cases (5) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))

private def state3Generators : Fin 5 → Source :=
  (Fin.cases ((⟨30⟩ : Source)) (Fin.cases ((⟨34⟩ : Source)) (Fin.cases ((⟨92⟩ : Source)) (Fin.cases ((⟨52⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state3Used : Fin 5 → Fin 15 :=
  (Fin.cases (7) (Fin.cases (8) (Fin.cases (13) (Fin.cases (9) (Fin.cases (0) (fun i => Fin.elim0 i))))))

private def state4Generators : Fin 5 → Source :=
  (Fin.cases ((⟨30⟩ : Source)) (Fin.cases ((⟨34⟩ : Source)) (Fin.cases ((⟨92⟩ : Source)) (Fin.cases ((⟨52⟩ : Source)) (Fin.cases ((⟨11⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state4Used : Fin 5 → Fin 15 :=
  (Fin.cases (7) (Fin.cases (8) (Fin.cases (13) (Fin.cases (9) (Fin.cases (5) (fun i => Fin.elim0 i))))))

private def state5Generators : Fin 5 → Source :=
  (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨30⟩ : Source)) (Fin.cases ((⟨34⟩ : Source)) (Fin.cases ((⟨92⟩ : Source)) (Fin.cases ((⟨52⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state5Used : Fin 5 → Fin 15 :=
  (Fin.cases (4) (Fin.cases (7) (Fin.cases (8) (Fin.cases (13) (Fin.cases (9) (fun i => Fin.elim0 i))))))

private def state6Generators : Fin 5 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state6Used : Fin 5 → Fin 15 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))

def stateGenerators : Fin 7 → Fin 5 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (fun i => Fin.elim0 i))))))))

def stateUsed : Fin 7 → Fin 5 → Fin 15 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (fun i => Fin.elim0 i))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 7) (k : Fin 5),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 10 → Fin 15 :=
  (Fin.cases (0) (Fin.cases (5) (Fin.cases (10) (Fin.cases (4) (Fin.cases (6) (Fin.cases (1) (Fin.cases (9) (Fin.cases (11) (Fin.cases (12) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 10,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 3 → Fin 15 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (fun i => Fin.elim0 i))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 3,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 7 → Fin 10 → Fin 7 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (2) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (1) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (2) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (1) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (2) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (2) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (4) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (3) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (5) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (fun i => Fin.elim0 i)))))))))))) (fun i => Fin.elim0 i))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow5NormalCore

end
