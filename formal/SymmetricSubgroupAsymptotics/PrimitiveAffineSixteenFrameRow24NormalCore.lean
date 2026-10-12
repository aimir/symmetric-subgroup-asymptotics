import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow24TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow24TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow24TopCertificate.ambient
def topRepresentative : Fin 19 → Source := PrimitiveAffineSixteenFrameRow24TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow24TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow24TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow24TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 33 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow24TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 33 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow24TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 33,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow24TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow24TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 33 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 33 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360506614714471200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803850153882980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7445629006517221770 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086237463236055600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459149666686673200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (221467885786401690 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509020844560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9987822675944681760 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701378097680 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (86242895756827320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311318948830375420 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13369552329928670670 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11208016700490650370 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531463560026320380 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2526614257635662520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1162884681420479160 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3603256043808529080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158002520746683900 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996041877551644110 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059613160242115940 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714239902465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12158027860581683970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223572992050 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 33) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 33) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 33) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 33) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow24TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow24TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow24TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow24TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow24TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 33) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 33) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 33 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 9 then 6
    else if x.index.val = 11 then 7
    else if x.index.val = 14 then 8
    else if x.index.val = 19 then 9
    else if x.index.val = 32 then 10
    else if x.index.val = 71 then 11
    else if x.index.val = 108 then 12
    else if x.index.val = 141 then 13
    else if x.index.val = 185 then 14
    else if x.index.val = 245 then 15
    else if x.index.val = 270 then 16
    else if x.index.val = 285 then 17
    else if x.index.val = 297 then 18
    else if x.index.val = 334 then 19
    else if x.index.val = 336 then 20
    else if x.index.val = 375 then 21
    else if x.index.val = 379 then 22
    else if x.index.val = 396 then 23
    else if x.index.val = 412 then 24
    else if x.index.val = 419 then 25
    else if x.index.val = 495 then 26
    else if x.index.val = 539 then 27
    else if x.index.val = 555 then 28
    else if x.index.val = 635 then 29
    else if x.index.val = 661 then 30
    else if x.index.val = 741 then 31
    else if x.index.val = 746 then 32
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 33,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 33) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 8 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state0Used : Fin 8 → Fin 33 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state1Generators : Fin 8 → Source :=
  (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨412⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state1Used : Fin 8 → Fin 33 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state2Generators : Fin 8 → Source :=
  (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨412⟩ : Source)) (Fin.cases ((⟨555⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state2Used : Fin 8 → Fin 33 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (28) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state3Generators : Fin 8 → Source :=
  (Fin.cases ((⟨185⟩ : Source)) (Fin.cases ((⟨495⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨108⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state3Used : Fin 8 → Fin 33 :=
  (Fin.cases (14) (Fin.cases (26) (Fin.cases (11) (Fin.cases (12) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state4Generators : Fin 8 → Source :=
  (Fin.cases ((⟨19⟩ : Source)) (Fin.cases ((⟨661⟩ : Source)) (Fin.cases ((⟨555⟩ : Source)) (Fin.cases ((⟨412⟩ : Source)) (Fin.cases ((⟨746⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state4Used : Fin 8 → Fin 33 :=
  (Fin.cases (9) (Fin.cases (30) (Fin.cases (28) (Fin.cases (24) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state5Generators : Fin 8 → Source :=
  (Fin.cases ((⟨539⟩ : Source)) (Fin.cases ((⟨396⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨185⟩ : Source)) (Fin.cases ((⟨495⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨108⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state5Used : Fin 8 → Fin 33 :=
  (Fin.cases (27) (Fin.cases (23) (Fin.cases (8) (Fin.cases (14) (Fin.cases (26) (Fin.cases (11) (Fin.cases (12) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state6Generators : Fin 8 → Source :=
  (Fin.cases ((⟨270⟩ : Source)) (Fin.cases ((⟨539⟩ : Source)) (Fin.cases ((⟨396⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨185⟩ : Source)) (Fin.cases ((⟨495⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨108⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state6Used : Fin 8 → Fin 33 :=
  (Fin.cases (16) (Fin.cases (27) (Fin.cases (23) (Fin.cases (8) (Fin.cases (14) (Fin.cases (26) (Fin.cases (11) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))

private def state7Generators : Fin 8 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state7Used : Fin 8 → Fin 33 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

def stateGenerators : Fin 8 → Fin 8 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (fun i => Fin.elim0 i)))))))))

def stateUsed : Fin 8 → Fin 8 → Fin 33 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (fun i => Fin.elim0 i)))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 8) (k : Fin 8),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 19 → Fin 33 :=
  (Fin.cases (0) (Fin.cases (12) (Fin.cases (24) (Fin.cases (8) (Fin.cases (28) (Fin.cases (29) (Fin.cases (23) (Fin.cases (18) (Fin.cases (15) (Fin.cases (16) (Fin.cases (25) (Fin.cases (1) (Fin.cases (10) (Fin.cases (17) (Fin.cases (31) (Fin.cases (13) (Fin.cases (19) (Fin.cases (21) (Fin.cases (20) (fun i => Fin.elim0 i))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 19,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 33 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 8 → Fin 19 → Fin 8 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (3) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (3) (Fin.cases (1) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (2) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (3) (Fin.cases (3) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (fun i => Fin.elim0 i))))))))))))))))))))) (fun i => Fin.elim0 i)))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow24NormalCore

end
