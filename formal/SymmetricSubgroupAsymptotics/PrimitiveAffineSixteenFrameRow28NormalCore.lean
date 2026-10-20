import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow28TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow28NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow28TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow28TopCertificate.group

def topAmbient : Fin 4 → Source := PrimitiveAffineSixteenFrameRow28TopCertificate.ambient
def topRepresentative : Fin 29 → Source := PrimitiveAffineSixteenFrameRow28TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow28TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow28TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow28TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 44 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow28TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 44 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow28TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 44,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow28TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow28TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 44 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 44 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445607145448674080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803850153882980 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (7445629006517221770 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3603272730007156890 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468314856341670810 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509020844560 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258792579600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11208016700206559520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11216268758092140285 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11216235901592330220 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12157976127921795360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378212844436975100 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531463560026320380 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459166223564415280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229752374686741860 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531463559272332525 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12149358305887969260 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (86242895756827320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701378097680 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3603239615809297080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378212844188269805 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12149325449388150525 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258224378625 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9987837171964588320 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311318949584370925 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311318948830375420 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9987837171680482050 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221884843561730 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714808103440 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741986825932850 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741987141493505 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3603239615558625675 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938744550145 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938491900195 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (86242896007506315 : Fin (16 ^ 16))) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 44) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 44) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 44) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 44) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow28TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow28TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow28TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow28TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow28TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 44) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 44) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 44 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 7 then 5
    else if x.index.val = 11 then 6
    else if x.index.val = 14 then 7
    else if x.index.val = 19 then 8
    else if x.index.val = 35 then 9
    else if x.index.val = 72 then 10
    else if x.index.val = 79 then 11
    else if x.index.val = 162 then 12
    else if x.index.val = 171 then 13
    else if x.index.val = 179 then 14
    else if x.index.val = 208 then 15
    else if x.index.val = 216 then 16
    else if x.index.val = 256 then 17
    else if x.index.val = 313 then 18
    else if x.index.val = 346 then 19
    else if x.index.val = 423 then 20
    else if x.index.val = 461 then 21
    else if x.index.val = 496 then 22
    else if x.index.val = 534 then 23
    else if x.index.val = 605 then 24
    else if x.index.val = 607 then 25
    else if x.index.val = 628 then 26
    else if x.index.val = 742 then 27
    else if x.index.val = 814 then 28
    else if x.index.val = 885 then 29
    else if x.index.val = 894 then 30
    else if x.index.val = 931 then 31
    else if x.index.val = 1152 then 32
    else if x.index.val = 1159 then 33
    else if x.index.val = 1169 then 34
    else if x.index.val = 1208 then 35
    else if x.index.val = 1221 then 36
    else if x.index.val = 1264 then 37
    else if x.index.val = 1288 then 38
    else if x.index.val = 1381 then 39
    else if x.index.val = 1410 then 40
    else if x.index.val = 1450 then 41
    else if x.index.val = 1527 then 42
    else if x.index.val = 1532 then 43
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 44,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 44) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 9 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state0Used : Fin 9 → Fin 44 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state1Generators : Fin 9 → Source :=
  (Fin.cases ((⟨1527⟩ : Source)) (Fin.cases ((⟨1381⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state1Used : Fin 9 → Fin 44 :=
  (Fin.cases (42) (Fin.cases (39) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state2Generators : Fin 9 → Source :=
  (Fin.cases ((⟨1527⟩ : Source)) (Fin.cases ((⟨1381⟩ : Source)) (Fin.cases ((⟨1288⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state2Used : Fin 9 → Fin 44 :=
  (Fin.cases (42) (Fin.cases (39) (Fin.cases (38) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state3Generators : Fin 9 → Source :=
  (Fin.cases ((⟨1527⟩ : Source)) (Fin.cases ((⟨1381⟩ : Source)) (Fin.cases ((⟨35⟩ : Source)) (Fin.cases ((⟨1288⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state3Used : Fin 9 → Fin 44 :=
  (Fin.cases (42) (Fin.cases (39) (Fin.cases (9) (Fin.cases (38) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state4Generators : Fin 9 → Source :=
  (Fin.cases ((⟨179⟩ : Source)) (Fin.cases ((⟨534⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨607⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state4Used : Fin 9 → Fin 44 :=
  (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state5Generators : Fin 9 → Source :=
  (Fin.cases ((⟨19⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨1221⟩ : Source)) (Fin.cases ((⟨1208⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state5Used : Fin 9 → Fin 44 :=
  (Fin.cases (8) (Fin.cases (7) (Fin.cases (22) (Fin.cases (36) (Fin.cases (35) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state6Generators : Fin 9 → Source :=
  (Fin.cases ((⟨19⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨1221⟩ : Source)) (Fin.cases ((⟨1208⟩ : Source)) (Fin.cases ((⟨1169⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state6Used : Fin 9 → Fin 44 :=
  (Fin.cases (8) (Fin.cases (7) (Fin.cases (22) (Fin.cases (36) (Fin.cases (35) (Fin.cases (34) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state7Generators : Fin 9 → Source :=
  (Fin.cases ((⟨313⟩ : Source)) (Fin.cases ((⟨216⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨179⟩ : Source)) (Fin.cases ((⟨534⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨607⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state7Used : Fin 9 → Fin 44 :=
  (Fin.cases (18) (Fin.cases (16) (Fin.cases (7) (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (25) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state8Generators : Fin 9 → Source :=
  (Fin.cases ((⟨313⟩ : Source)) (Fin.cases ((⟨216⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨179⟩ : Source)) (Fin.cases ((⟨534⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨607⟩ : Source)) (Fin.cases ((⟨1169⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state8Used : Fin 9 → Fin 44 :=
  (Fin.cases (18) (Fin.cases (16) (Fin.cases (7) (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (25) (Fin.cases (34) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state9Generators : Fin 9 → Source :=
  (Fin.cases ((⟨162⟩ : Source)) (Fin.cases ((⟨313⟩ : Source)) (Fin.cases ((⟨216⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨179⟩ : Source)) (Fin.cases ((⟨534⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨607⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state9Used : Fin 9 → Fin 44 :=
  (Fin.cases (12) (Fin.cases (18) (Fin.cases (16) (Fin.cases (7) (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (25) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

private def state10Generators : Fin 9 → Source :=
  (Fin.cases ((⟨162⟩ : Source)) (Fin.cases ((⟨313⟩ : Source)) (Fin.cases ((⟨216⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨179⟩ : Source)) (Fin.cases ((⟨534⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨607⟩ : Source)) (Fin.cases ((⟨885⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state10Used : Fin 9 → Fin 44 :=
  (Fin.cases (12) (Fin.cases (18) (Fin.cases (16) (Fin.cases (7) (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (25) (Fin.cases (29) (fun i => Fin.elim0 i))))))))))

private def state11Generators : Fin 9 → Source :=
  (Fin.cases ((⟨162⟩ : Source)) (Fin.cases ((⟨313⟩ : Source)) (Fin.cases ((⟨216⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨179⟩ : Source)) (Fin.cases ((⟨534⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨607⟩ : Source)) (Fin.cases ((⟨1169⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state11Used : Fin 9 → Fin 44 :=
  (Fin.cases (12) (Fin.cases (18) (Fin.cases (16) (Fin.cases (7) (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (25) (Fin.cases (34) (fun i => Fin.elim0 i))))))))))

private def state12Generators : Fin 9 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨162⟩ : Source)) (Fin.cases ((⟨313⟩ : Source)) (Fin.cases ((⟨216⟩ : Source)) (Fin.cases ((⟨14⟩ : Source)) (Fin.cases ((⟨179⟩ : Source)) (Fin.cases ((⟨534⟩ : Source)) (Fin.cases ((⟨496⟩ : Source)) (Fin.cases ((⟨607⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state12Used : Fin 9 → Fin 44 :=
  (Fin.cases (1) (Fin.cases (12) (Fin.cases (18) (Fin.cases (16) (Fin.cases (7) (Fin.cases (14) (Fin.cases (23) (Fin.cases (22) (Fin.cases (25) (fun i => Fin.elim0 i))))))))))

private def state13Generators : Fin 9 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i))))))))))

private def state13Used : Fin 9 → Fin 44 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i))))))))))

def stateGenerators : Fin 14 → Fin 9 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (fun i => Fin.elim0 i)))))))))))))))

def stateUsed : Fin 14 → Fin 9 → Fin 44 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (fun i => Fin.elim0 i)))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 14) (k : Fin 9),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 29 → Fin 44 :=
  (Fin.cases (0) (Fin.cases (25) (Fin.cases (40) (Fin.cases (7) (Fin.cases (38) (Fin.cases (28) (Fin.cases (16) (Fin.cases (15) (Fin.cases (31) (Fin.cases (12) (Fin.cases (20) (Fin.cases (1) (Fin.cases (13) (Fin.cases (32) (Fin.cases (24) (Fin.cases (21) (Fin.cases (34) (Fin.cases (9) (Fin.cases (41) (Fin.cases (19) (Fin.cases (26) (Fin.cases (30) (Fin.cases (27) (Fin.cases (11) (Fin.cases (29) (Fin.cases (10) (Fin.cases (33) (Fin.cases (37) (Fin.cases (43) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 29,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 4 → Fin 44 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (fun i => Fin.elim0 i)))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 4,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 14 → Fin 29 → Fin 14 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (4) (Fin.cases (1) (Fin.cases (5) (Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (6) (Fin.cases (3) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (4) (Fin.cases (1) (Fin.cases (5) (Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (6) (Fin.cases (3) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (5) (Fin.cases (2) (Fin.cases (5) (Fin.cases (2) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (6) (Fin.cases (3) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (6) (Fin.cases (3) (Fin.cases (6) (Fin.cases (3) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (6) (Fin.cases (3) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (4) (Fin.cases (4) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (5) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (6) (Fin.cases (6) (Fin.cases (6) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))) (fun i => Fin.elim0 i)))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow28NormalCore

end
