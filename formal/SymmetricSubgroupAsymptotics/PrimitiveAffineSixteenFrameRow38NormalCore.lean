import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow38TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow38TopCertificate.group

def topAmbient : Fin 3 → Source := PrimitiveAffineSixteenFrameRow38TopCertificate.ambient
def topRepresentative : Fin 19 → Source := PrimitiveAffineSixteenFrameRow38TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow38TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow38TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow38TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 29 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow38TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 29 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow38TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 29,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow38TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow38TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 29 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 29 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2792141846611548480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (4017038152435091520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951921914625 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10494203887533667200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (4012354489051367505 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8469752903858315040 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13194782621269191360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17408582805732230880 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11910762525573127920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5314795644889290960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2276501762783144160 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17761829944131066000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16618985467892319360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9508270198820095920 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (4893715502826510960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13085009053910811360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (16961527040778557520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8383057875703829040 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8063461640220016905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6591480428621802510 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10603976421142895520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14570793119482224480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5144704567294632195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11472330999134145120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258477015090 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1167088121787636990 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (5000967164508735915 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7441392450524785545 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))

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
      (((PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow38TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow38TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow38TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow38TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow38TopCertificate.certificate.encode_elements (usedSource k).index
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
    else if x.index.val = 6 then 5
    else if x.index.val = 37 then 6
    else if x.index.val = 81 then 7
    else if x.index.val = 85 then 8
    else if x.index.val = 194 then 9
    else if x.index.val = 214 then 10
    else if x.index.val = 221 then 11
    else if x.index.val = 237 then 12
    else if x.index.val = 340 then 13
    else if x.index.val = 464 then 14
    else if x.index.val = 503 then 15
    else if x.index.val = 553 then 16
    else if x.index.val = 671 then 17
    else if x.index.val = 699 then 18
    else if x.index.val = 867 then 19
    else if x.index.val = 1194 then 20
    else if x.index.val = 1313 then 21
    else if x.index.val = 1454 then 22
    else if x.index.val = 1609 then 23
    else if x.index.val = 1711 then 24
    else if x.index.val = 2615 then 25
    else if x.index.val = 2706 then 26
    else if x.index.val = 2722 then 27
    else if x.index.val = 2741 then 28
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
  (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨2706⟩ : Source)) (Fin.cases ((⟨2741⟩ : Source)) (Fin.cases ((⟨2615⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state1Used : Fin 7 → Fin 29 :=
  (Fin.cases (3) (Fin.cases (26) (Fin.cases (28) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state2Generators : Fin 7 → Source :=
  (Fin.cases ((⟨81⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨2615⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state2Used : Fin 7 → Fin 29 :=
  (Fin.cases (7) (Fin.cases (3) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

private def state3Generators : Fin 7 → Source :=
  (Fin.cases ((⟨221⟩ : Source)) (Fin.cases ((⟨699⟩ : Source)) (Fin.cases ((⟨85⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨2741⟩ : Source)) (Fin.cases ((⟨2722⟩ : Source)) (Fin.cases ((⟨2706⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state3Used : Fin 7 → Fin 29 :=
  (Fin.cases (11) (Fin.cases (18) (Fin.cases (8) (Fin.cases (3) (Fin.cases (28) (Fin.cases (27) (Fin.cases (26) (fun i => Fin.elim0 i))))))))

private def state4Generators : Fin 7 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))

private def state4Used : Fin 7 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))

def stateGenerators : Fin 5 → Fin 7 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (fun i => Fin.elim0 i))))))

def stateUsed : Fin 5 → Fin 7 → Fin 29 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (fun i => Fin.elim0 i))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 5) (k : Fin 7),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 19 → Fin 29 :=
  (Fin.cases (0) (Fin.cases (3) (Fin.cases (7) (Fin.cases (10) (Fin.cases (24) (Fin.cases (17) (Fin.cases (18) (Fin.cases (23) (Fin.cases (12) (Fin.cases (19) (Fin.cases (16) (Fin.cases (20) (Fin.cases (15) (Fin.cases (6) (Fin.cases (21) (Fin.cases (13) (Fin.cases (14) (Fin.cases (1) (Fin.cases (9) (fun i => Fin.elim0 i))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 19,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 3 → Fin 29 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (fun i => Fin.elim0 i))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 3,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 5 → Fin 19 → Fin 5 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (1) (Fin.cases (2) (Fin.cases (2) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (1) (Fin.cases (2) (Fin.cases (2) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (2) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (3) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (fun i => Fin.elim0 i))))))))))))))))))))) (fun i => Fin.elim0 i))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow38NormalCore

end
