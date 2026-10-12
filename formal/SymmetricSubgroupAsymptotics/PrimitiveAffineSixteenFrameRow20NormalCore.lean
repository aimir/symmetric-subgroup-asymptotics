import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow20TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow20TopCertificate.group

def topAmbient : Fin 5 → Source := PrimitiveAffineSixteenFrameRow20TopCertificate.ambient
def topRepresentative : Fin 12 → Source := PrimitiveAffineSixteenFrameRow20TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow20TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow20TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow20TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 29 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow20TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 29 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow20TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 29,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow20TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow20TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 29 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 29 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9920133061863609120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636072142180 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8522270792435480970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986825932850 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441506361647370800 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14906726159964840720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6288940358659875120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11005185982885343490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306412779288224885 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6217164301970480010 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672508705276195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7310711014741293480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8526625511064805635 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136254946949744215 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (157985963896463055 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378229401287188175 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059598923214903110 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613160526210165 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17076935468086010640 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701378097680 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459149666686673200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364704749206840065 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))

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
      (((PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow20TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow20TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow20TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow20TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow20TopCertificate.certificate.encode_elements (usedSource k).index
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
    else if x.index.val = 10 then 7
    else if x.index.val = 11 then 8
    else if x.index.val = 14 then 9
    else if x.index.val = 22 then 10
    else if x.index.val = 35 then 11
    else if x.index.val = 101 then 12
    else if x.index.val = 113 then 13
    else if x.index.val = 115 then 14
    else if x.index.val = 116 then 15
    else if x.index.val = 149 then 16
    else if x.index.val = 150 then 17
    else if x.index.val = 151 then 18
    else if x.index.val = 242 then 19
    else if x.index.val = 269 then 20
    else if x.index.val = 295 then 21
    else if x.index.val = 316 then 22
    else if x.index.val = 326 then 23
    else if x.index.val = 341 then 24
    else if x.index.val = 356 then 25
    else if x.index.val = 360 then 26
    else if x.index.val = 368 then 27
    else if x.index.val = 378 then 28
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
  (Fin.cases ((⟨151⟩ : Source)) (Fin.cases ((⟨356⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 29 :=
  (Fin.cases (18) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨151⟩ : Source)) (Fin.cases ((⟨356⟩ : Source)) (Fin.cases ((⟨150⟩ : Source)) (Fin.cases ((⟨316⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 29 :=
  (Fin.cases (18) (Fin.cases (25) (Fin.cases (17) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨151⟩ : Source)) (Fin.cases ((⟨356⟩ : Source)) (Fin.cases ((⟨242⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 29 :=
  (Fin.cases (18) (Fin.cases (25) (Fin.cases (19) (Fin.cases (10) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨341⟩ : Source)) (Fin.cases ((⟨295⟩ : Source)) (Fin.cases ((⟨368⟩ : Source)) (Fin.cases ((⟨356⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 29 :=
  (Fin.cases (24) (Fin.cases (21) (Fin.cases (27) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state5Generators : Fin 7 → Source :=
  (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨242⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨341⟩ : Source)) (Fin.cases ((⟨378⟩ : Source)) (Fin.cases ((⟨101⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state5Used : Fin 7 → Fin 29 :=
  (Fin.cases (10) (Fin.cases (19) (Fin.cases (15) (Fin.cases (24) (Fin.cases (28) (Fin.cases (12) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state6Generators : Fin 7 → Source :=
  (Fin.cases ((⟨11⟩ : Source)) (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨242⟩ : Source)) (Fin.cases ((⟨116⟩ : Source)) (Fin.cases ((⟨341⟩ : Source)) (Fin.cases ((⟨378⟩ : Source)) (Fin.cases ((⟨101⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state6Used : Fin 7 → Fin 29 :=
  (Fin.cases (8) (Fin.cases (10) (Fin.cases (19) (Fin.cases (15) (Fin.cases (24) (Fin.cases (28) (Fin.cases (12) (fun i => Fin.elim0 i))))))))

private def state7Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state7Used : Fin 7 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 8 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (fun i => Fin.elim0 i)))))))))

def stateUsed : Fin 8 → Fin 7 → Fin 29 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (fun i => Fin.elim0 i)))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 8) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 12 → Fin 29 :=
  (Fin.cases (0) (Fin.cases (28) (Fin.cases (23) (Fin.cases (7) (Fin.cases (26) (Fin.cases (18) (Fin.cases (14) (Fin.cases (3) (Fin.cases (20) (Fin.cases (16) (Fin.cases (13) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 12,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 5 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (fun i => Fin.elim0 i))))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 5,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 8 → Fin 12 → Fin 8 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (4) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (1) (Fin.cases (7) (Fin.cases (2) (Fin.cases (5) (Fin.cases (3) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (4) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (1) (Fin.cases (7) (Fin.cases (2) (Fin.cases (5) (Fin.cases (3) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (2) (Fin.cases (7) (Fin.cases (2) (Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (3) (Fin.cases (7) (Fin.cases (5) (Fin.cases (5) (Fin.cases (3) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (4) (Fin.cases (7) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (5) (Fin.cases (7) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i)))))))))))))) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow20NormalCore

end
