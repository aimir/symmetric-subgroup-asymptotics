import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow15TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow15TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow15TopCertificate.ambient
def topRepresentative : Fin 10 → Source := PrimitiveAffineSixteenFrameRow15TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow15TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow15TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow15TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow15TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow15TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 16 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow15TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 16 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow15TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 16,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow15TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow15TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 16 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 16 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18297112935027778320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920133061863609120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059580303742301540 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5005207843419109770 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5140538944302128010 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6288940358659875120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938491900195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531496416273485790 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946949744215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306412779288224885 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12216935882818645245 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441539476097868035 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849648592710 : Fin (16 ^ 16))) (fun i => Fin.elim0 i)))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 16) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 16) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 16) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 16) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow15TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow15TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow15TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow15TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow15TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow15TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 16) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 16) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 16 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 7 then 5
    else if x.index.val = 9 then 6
    else if x.index.val = 14 then 7
    else if x.index.val = 15 then 8
    else if x.index.val = 17 then 9
    else if x.index.val = 24 then 10
    else if x.index.val = 44 then 11
    else if x.index.val = 48 then 12
    else if x.index.val = 60 then 13
    else if x.index.val = 80 then 14
    else if x.index.val = 90 then 15
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 16,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 16) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 5 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state0Used : Fin 5 → Fin 16 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))

private def state1Generators : Fin 5 → Source :=
  (Fin.cases ((⟨80⟩ : Source)) (Fin.cases ((⟨17⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state1Used : Fin 5 → Fin 16 :=
  (Fin.cases (14) (Fin.cases (9) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))

private def state2Generators : Fin 5 → Source :=
  (Fin.cases ((⟨24⟩ : Source)) (Fin.cases ((⟨15⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨80⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state2Used : Fin 5 → Fin 16 :=
  (Fin.cases (10) (Fin.cases (8) (Fin.cases (7) (Fin.cases (14) (Fin.cases (0) (fun i => Fin.elim0 i))))))

private def state3Generators : Fin 5 → Source :=
  (Fin.cases ((⟨9⟩ : Source)) (Fin.cases ((⟨24⟩ : Source)) (Fin.cases ((⟨15⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨80⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state3Used : Fin 5 → Fin 16 :=
  (Fin.cases (6) (Fin.cases (10) (Fin.cases (8) (Fin.cases (7) (Fin.cases (14) (fun i => Fin.elim0 i))))))

private def state4Generators : Fin 5 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))

private def state4Used : Fin 5 → Fin 16 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (fun i => Fin.elim0 i))))))

def stateGenerators : Fin 5 → Fin 5 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (fun i => Fin.elim0 i))))))

def stateUsed : Fin 5 → Fin 5 → Fin 16 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (fun i => Fin.elim0 i))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 5) (k : Fin 5),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 10 → Fin 16 :=
  (Fin.cases (0) (Fin.cases (1) (Fin.cases (6) (Fin.cases (14) (Fin.cases (13) (Fin.cases (10) (Fin.cases (5) (Fin.cases (12) (Fin.cases (15) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 10,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 16 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 5 → Fin 10 → Fin 5 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (4) (Fin.cases (3) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (4) (Fin.cases (2) (Fin.cases (2) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (4) (Fin.cases (3) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (4) (Fin.cases (2) (Fin.cases (2) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (4) (Fin.cases (3) (Fin.cases (2) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (4) (Fin.cases (2) (Fin.cases (2) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (fun i => Fin.elim0 i)))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (fun i => Fin.elim0 i)))))))))))) (fun i => Fin.elim0 i))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow15NormalCore

end
