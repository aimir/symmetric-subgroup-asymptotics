import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow2TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow2TopCertificate.group

def topAmbient : Fin 3 → Source := PrimitiveAffineSixteenFrameRow2TopCertificate.ambient
def topRepresentative : Fin 8 → Source := PrimitiveAffineSixteenFrameRow2TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow2TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow2TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow2TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 11 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow2TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 11 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow2TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 11,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow2TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow2TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 11 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 11 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920134157078303520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5000969291085756810 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229785231184589925 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5140522453682364720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531481147413097980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306394160385775175 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059598923212932950 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136273564845565300 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 11) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 11) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 11) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 11) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow2TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow2TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow2TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow2TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow2TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 11) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 11) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 11 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 8 then 5
    else if x.index.val = 10 then 6
    else if x.index.val = 18 then 7
    else if x.index.val = 23 then 8
    else if x.index.val = 35 then 9
    else if x.index.val = 47 then 10
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 11,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 11) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 4 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))

private def state0Used : Fin 4 → Fin 11 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))

private def state1Generators : Fin 4 → Source :=
  (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨35⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))

private def state1Used : Fin 4 → Fin 11 :=
  (Fin.cases (6) (Fin.cases (9) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))

private def state2Generators : Fin 4 → Source :=
  (Fin.cases ((⟨23⟩ : Source)) (Fin.cases ((⟨8⟩ : Source)) (Fin.cases ((⟨10⟩ : Source)) (Fin.cases ((⟨35⟩ : Source)) (fun i => Fin.elim0 i)))))

private def state2Used : Fin 4 → Fin 11 :=
  (Fin.cases (8) (Fin.cases (5) (Fin.cases (6) (Fin.cases (9) (fun i => Fin.elim0 i)))))

private def state3Generators : Fin 4 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))

private def state3Used : Fin 4 → Fin 11 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (0) (fun i => Fin.elim0 i)))))

def stateGenerators : Fin 4 → Fin 4 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (fun i => Fin.elim0 i)))))

def stateUsed : Fin 4 → Fin 4 → Fin 11 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (fun i => Fin.elim0 i)))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 4) (k : Fin 4),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 8 → Fin 11 :=
  (Fin.cases (0) (Fin.cases (4) (Fin.cases (1) (Fin.cases (6) (Fin.cases (7) (Fin.cases (8) (Fin.cases (3) (Fin.cases (10) (fun i => Fin.elim0 i)))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 8,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 3 → Fin 11 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (fun i => Fin.elim0 i))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 3,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 4 → Fin 8 → Fin 4 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (3) (Fin.cases (3) (Fin.cases (1) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (fun i => Fin.elim0 i)))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (3) (Fin.cases (3) (Fin.cases (1) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (fun i => Fin.elim0 i)))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (3) (Fin.cases (3) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (fun i => Fin.elim0 i)))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))) (fun i => Fin.elim0 i)))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow2NormalCore

end
