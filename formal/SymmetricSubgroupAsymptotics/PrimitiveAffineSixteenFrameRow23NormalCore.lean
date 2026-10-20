import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow23TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow23TopCertificate.group

def topAmbient : Fin 5 → Source := PrimitiveAffineSixteenFrameRow23TopCertificate.ambient
def topRepresentative : Fin 24 → Source := PrimitiveAffineSixteenFrameRow23TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow23TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow23TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow23TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 39 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow23TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 39 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow23TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 39,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow23TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow23TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 39 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 39 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378221885127668000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12360506614714471200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13306445636072142180 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8522270792435480970 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758543672213795 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086237463236055600 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8459149666686673200 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (221467886037076890 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531512973625064685 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531512973372415695 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353939312751120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701378097680 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12157994746889122080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1162851566971959450 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12157976127921795360 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (10059598923214903110 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12149325449388162510 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311269535231638765 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1162851567477238155 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9987837171680482050 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158018819894927055 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279618714555453490 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136222090165835590 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223257441025 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364704749206840065 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13369519473428848620 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11207998081523323650 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655952174555905 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271086191120 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333259045212210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924333258224378625 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229803849648592710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839230665905877520 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378196545036090605 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13378203266160341280 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2526630943583615130 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2526630944088893835 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378196545288724175 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 39) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 39) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 39) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 39) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow23TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow23TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow23TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow23TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow23TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 39) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 39) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 39 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 4 then 4
    else if x.index.val = 5 then 5
    else if x.index.val = 6 then 6
    else if x.index.val = 11 then 7
    else if x.index.val = 13 then 8
    else if x.index.val = 16 then 9
    else if x.index.val = 58 then 10
    else if x.index.val = 67 then 11
    else if x.index.val = 76 then 12
    else if x.index.val = 104 then 13
    else if x.index.val = 115 then 14
    else if x.index.val = 228 then 15
    else if x.index.val = 265 then 16
    else if x.index.val = 266 then 17
    else if x.index.val = 314 then 18
    else if x.index.val = 318 then 19
    else if x.index.val = 332 then 20
    else if x.index.val = 346 then 21
    else if x.index.val = 359 then 22
    else if x.index.val = 364 then 23
    else if x.index.val = 379 then 24
    else if x.index.val = 391 then 25
    else if x.index.val = 431 then 26
    else if x.index.val = 487 then 27
    else if x.index.val = 506 then 28
    else if x.index.val = 552 then 29
    else if x.index.val = 625 then 30
    else if x.index.val = 630 then 31
    else if x.index.val = 637 then 32
    else if x.index.val = 641 then 33
    else if x.index.val = 645 then 34
    else if x.index.val = 705 then 35
    else if x.index.val = 706 then 36
    else if x.index.val = 749 then 37
    else if x.index.val = 763 then 38
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 39,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 39) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 8 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state0Used : Fin 8 → Fin 39 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state1Generators : Fin 8 → Source :=
  (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state1Used : Fin 8 → Fin 39 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state2Generators : Fin 8 → Source :=
  (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨641⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state2Used : Fin 8 → Fin 39 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (33) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state3Generators : Fin 8 → Source :=
  (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨16⟩ : Source)) (Fin.cases ((⟨364⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state3Used : Fin 8 → Fin 39 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (9) (Fin.cases (23) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state4Generators : Fin 8 → Source :=
  (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨314⟩ : Source)) (Fin.cases ((⟨637⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state4Used : Fin 8 → Fin 39 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (18) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state5Generators : Fin 8 → Source :=
  (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨641⟩ : Source)) (Fin.cases ((⟨16⟩ : Source)) (Fin.cases ((⟨364⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state5Used : Fin 8 → Fin 39 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (33) (Fin.cases (9) (Fin.cases (23) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state6Generators : Fin 8 → Source :=
  (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨641⟩ : Source)) (Fin.cases ((⟨314⟩ : Source)) (Fin.cases ((⟨637⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state6Used : Fin 8 → Fin 39 :=
  (Fin.cases (22) (Fin.cases (24) (Fin.cases (33) (Fin.cases (18) (Fin.cases (32) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state7Generators : Fin 8 → Source :=
  (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (Fin.cases ((⟨391⟩ : Source)) (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state7Used : Fin 8 → Fin 39 :=
  (Fin.cases (12) (Fin.cases (29) (Fin.cases (25) (Fin.cases (22) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state8Generators : Fin 8 → Source :=
  (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (Fin.cases ((⟨391⟩ : Source)) (Fin.cases ((⟨359⟩ : Source)) (Fin.cases ((⟨67⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state8Used : Fin 8 → Fin 39 :=
  (Fin.cases (12) (Fin.cases (29) (Fin.cases (25) (Fin.cases (22) (Fin.cases (11) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state9Generators : Fin 8 → Source :=
  (Fin.cases ((⟨265⟩ : Source)) (Fin.cases ((⟨645⟩ : Source)) (Fin.cases ((⟨625⟩ : Source)) (Fin.cases ((⟨506⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state9Used : Fin 8 → Fin 39 :=
  (Fin.cases (16) (Fin.cases (34) (Fin.cases (30) (Fin.cases (28) (Fin.cases (12) (Fin.cases (29) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state10Generators : Fin 8 → Source :=
  (Fin.cases ((⟨265⟩ : Source)) (Fin.cases ((⟨645⟩ : Source)) (Fin.cases ((⟨625⟩ : Source)) (Fin.cases ((⟨506⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (Fin.cases ((⟨67⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state10Used : Fin 8 → Fin 39 :=
  (Fin.cases (16) (Fin.cases (34) (Fin.cases (30) (Fin.cases (28) (Fin.cases (12) (Fin.cases (29) (Fin.cases (11) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state11Generators : Fin 8 → Source :=
  (Fin.cases ((⟨266⟩ : Source)) (Fin.cases ((⟨265⟩ : Source)) (Fin.cases ((⟨645⟩ : Source)) (Fin.cases ((⟨625⟩ : Source)) (Fin.cases ((⟨506⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state11Used : Fin 8 → Fin 39 :=
  (Fin.cases (17) (Fin.cases (16) (Fin.cases (34) (Fin.cases (30) (Fin.cases (28) (Fin.cases (12) (Fin.cases (29) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state12Generators : Fin 8 → Source :=
  (Fin.cases ((⟨266⟩ : Source)) (Fin.cases ((⟨265⟩ : Source)) (Fin.cases ((⟨645⟩ : Source)) (Fin.cases ((⟨625⟩ : Source)) (Fin.cases ((⟨506⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (Fin.cases ((⟨104⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state12Used : Fin 8 → Fin 39 :=
  (Fin.cases (17) (Fin.cases (16) (Fin.cases (34) (Fin.cases (30) (Fin.cases (28) (Fin.cases (12) (Fin.cases (29) (Fin.cases (13) (fun i => Fin.elim0 i)))))))))

private def state13Generators : Fin 8 → Source :=
  (Fin.cases ((⟨266⟩ : Source)) (Fin.cases ((⟨265⟩ : Source)) (Fin.cases ((⟨645⟩ : Source)) (Fin.cases ((⟨625⟩ : Source)) (Fin.cases ((⟨506⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (Fin.cases ((⟨67⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state13Used : Fin 8 → Fin 39 :=
  (Fin.cases (17) (Fin.cases (16) (Fin.cases (34) (Fin.cases (30) (Fin.cases (28) (Fin.cases (12) (Fin.cases (29) (Fin.cases (11) (fun i => Fin.elim0 i)))))))))

private def state14Generators : Fin 8 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨266⟩ : Source)) (Fin.cases ((⟨265⟩ : Source)) (Fin.cases ((⟨645⟩ : Source)) (Fin.cases ((⟨625⟩ : Source)) (Fin.cases ((⟨506⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨552⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state14Used : Fin 8 → Fin 39 :=
  (Fin.cases (1) (Fin.cases (17) (Fin.cases (16) (Fin.cases (34) (Fin.cases (30) (Fin.cases (28) (Fin.cases (12) (Fin.cases (29) (fun i => Fin.elim0 i)))))))))

private def state15Generators : Fin 8 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨4⟩ : Source)) (Fin.cases ((⟨5⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state15Used : Fin 8 → Fin 39 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

def stateGenerators : Fin 16 → Fin 8 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (Fin.cases (state14Generators) (Fin.cases (state15Generators) (fun i => Fin.elim0 i)))))))))))))))))

def stateUsed : Fin 16 → Fin 8 → Fin 39 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (Fin.cases (state14Used) (Fin.cases (state15Used) (fun i => Fin.elim0 i)))))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 16) (k : Fin 8),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 24 → Fin 39 :=
  (Fin.cases (0) (Fin.cases (29) (Fin.cases (24) (Fin.cases (34) (Fin.cases (9) (Fin.cases (18) (Fin.cases (17) (Fin.cases (1) (Fin.cases (15) (Fin.cases (20) (Fin.cases (36) (Fin.cases (14) (Fin.cases (11) (Fin.cases (33) (Fin.cases (31) (Fin.cases (38) (Fin.cases (10) (Fin.cases (21) (Fin.cases (26) (Fin.cases (13) (Fin.cases (35) (Fin.cases (27) (Fin.cases (37) (Fin.cases (19) (fun i => Fin.elim0 i)))))))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 24,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 5 → Fin 39 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (4) (Fin.cases (5) (fun i => Fin.elim0 i))))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 5,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 16 → Fin 24 → Fin 16 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (7) (Fin.cases (1) (Fin.cases (9) (Fin.cases (3) (Fin.cases (4) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (8) (Fin.cases (2) (Fin.cases (8) (Fin.cases (5) (Fin.cases (10) (Fin.cases (6) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (7) (Fin.cases (1) (Fin.cases (9) (Fin.cases (3) (Fin.cases (4) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (8) (Fin.cases (2) (Fin.cases (8) (Fin.cases (5) (Fin.cases (10) (Fin.cases (6) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (8) (Fin.cases (2) (Fin.cases (10) (Fin.cases (5) (Fin.cases (6) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (8) (Fin.cases (2) (Fin.cases (8) (Fin.cases (5) (Fin.cases (10) (Fin.cases (6) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (9) (Fin.cases (3) (Fin.cases (9) (Fin.cases (3) (Fin.cases (9) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (9) (Fin.cases (4) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (6) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (6) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (10) (Fin.cases (6) (Fin.cases (10) (Fin.cases (10) (Fin.cases (6) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (10) (Fin.cases (6) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (6) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (7) (Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (8) (Fin.cases (8) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (Fin.cases ((Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))))))))))))))))))) (fun i => Fin.elim0 i)))))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow23NormalCore

end
