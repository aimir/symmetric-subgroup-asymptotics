import SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12TopCertificate
import SymmetricSubgroupAsymptotics.FiniteNormalJoinWordRegistry
import SymmetricSubgroupAsymptotics.FinitePermutationCodeGroup


/-! Executable normal-state core.  Generated from a selected certificate; Lean rechecks all words. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalCore

abbrev Source := PrimitiveAffineSixteenFrameRow12TopCertificate.Source
local instance sourceGroup : Group Source := PrimitiveAffineSixteenFrameRow12TopCertificate.group

def topAmbient : Fin 3 → Source := PrimitiveAffineSixteenFrameRow12TopCertificate.ambient
def topRepresentative : Fin 28 → Source := PrimitiveAffineSixteenFrameRow12TopCertificate.representative
theorem topAmbient_full : Subgroup.closure (Set.range topAmbient) = ⊤ :=
  PrimitiveAffineSixteenFrameRow12TopCertificate.ambient_full
noncomputable def topConjugacy :
    FiniteConjugacyCentralizerCardinalCover topRepresentative :=
  PrimitiveAffineSixteenFrameRow12TopCertificate.conjugacy

def originalPermutationHom : Source →* Equiv.Perm (Fin 16) :=
  (Subgroup.subtype (Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow12TopCertificate.generators))).comp
    PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv.toMonoidHom

theorem originalPermutationHom_injective :
    Function.Injective originalPermutationHom := by
  intro x y h
  apply PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv.injective
  apply Subtype.ext
  exact h

def usedSource : Fin 49 → Source :=
  fun k ↦ ⟨PrimitiveAffineSixteenFrameRow12TopCertificate.normalUsedIndex k⟩

private def usedForwardCode : Fin 49 → Fin (16 ^ 16) :=
  PrimitiveAffineSixteenFrameRow12TopCertificate.normalUsedCode

private theorem usedForwardCode_matches : ∀ k : Fin 49,
    usedForwardCode k = PrimitiveAffineSixteenFrameRow12TopCertificate.certificate.rows (usedSource k).index := by
  intro k
  exact PrimitiveAffineSixteenFrameRow12TopCertificate.normalUsedCode_matches k

private def usedForwardFunction : Fin 49 → Fin 16 → Fin 16 :=
  fun k ↦ finFunctionFinEquiv.symm (usedForwardCode k)

private def usedInverseFunction : Fin 49 → Fin 16 → Fin 16 :=
  (Fin.cases (finFunctionFinEquiv.symm (18364758544493064720 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (13445608240663368480 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (6086104869005736330 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (11136273565631018085 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468314856105741210 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18288572946294925125 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370495843480080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223825642000 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996056115604152300 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (221517428499593385 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271338832400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (158003551535881935 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (8387390104505164080 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531462528984481005 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672508705284865 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284461192094465 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311319980126829805 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (221484313800390825 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (2311301361188994285 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364758543924855075 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364741987141493505 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951921905955 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701693640995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468331284355659945 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938491908865 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364704749206831395 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378230432330997455 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701125456400 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (1378211813393161935 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271654384385 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3468298170659158185 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364704749459481345 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839267903840530960 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (3531481147413101805 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996074734032773100 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924370496411664675 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279635271907016995 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (12229785230683231815 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364704749775041040 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839247223004799745 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996041877787573710 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (157984933107261135 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (9996023258849738190 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924353938744541475 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (14839284460939444515 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (18364721306558402610 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279672509273477170 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (15924316701946290945 : Fin (16 ^ 16))) (Fin.cases (finFunctionFinEquiv.symm (17279655951353721360 : Fin (16 ^ 16))) (fun i => Fin.elim0 i))))))))))))))))))))))))))))))))))))))))))))))))))

private theorem usedPermutation_left : ∀ (k : Fin 49) (i : Fin 16),
    usedInverseFunction k (usedForwardFunction k i) = i := by
  decide +kernel

private theorem usedPermutation_right : ∀ (k : Fin 49) (i : Fin 16),
    usedForwardFunction k (usedInverseFunction k i) = i := by
  decide +kernel

def usedPermutation (k : Fin 49) : Equiv.Perm (Fin 16) where
  toFun := usedForwardFunction k
  invFun := usedInverseFunction k
  left_inv := usedPermutation_left k
  right_inv := usedPermutation_right k

theorem usedPermutation_eq_original (k : Fin 49) :
    usedPermutation k = originalPermutationHom (usedSource k) := by
  apply permutationCode_injective 16
  change permutationCode (usedPermutation k) =
    permutationCode
      (((PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv (usedSource k) :
        Subgroup.closure (Set.range PrimitiveAffineSixteenFrameRow12TopCertificate.generators))) : Equiv.Perm (Fin 16))
  rw [PrimitiveAffineSixteenFrameRow12TopCertificate.originalEquiv_apply]
  have hcode :
      permutationCode (PrimitiveAffineSixteenFrameRow12TopCertificate.certificate.toCayley.elements (usedSource k).index) =
        PrimitiveAffineSixteenFrameRow12TopCertificate.certificate.rows (usedSource k).index := by
    simpa only [permutationGeneratorEncoding] using
      PrimitiveAffineSixteenFrameRow12TopCertificate.certificate.encode_elements (usedSource k).index
  rw [hcode]
  change finFunctionFinEquiv (finFunctionFinEquiv.symm (usedForwardCode k)) = _
  rw [Equiv.apply_symm_apply]
  exact usedForwardCode_matches k

def sourceCode : FiniteGroupCode Source (PermutationFunctionPair 16) :=
  (permutationFunctionPairCode 16).pullback originalPermutationHom
    originalPermutationHom_injective

def usedCode (k : Fin 49) : PermutationFunctionPair 16 :=
  permutationFunctionPair (usedPermutation k)

@[simp] theorem sourceCode_encode_used (k : Fin 49) :
    sourceCode.encode (usedSource k) = usedCode k := by
  change permutationFunctionPair (originalPermutationHom (usedSource k)) =
    permutationFunctionPair (usedPermutation k)
  rw [usedPermutation_eq_original]

def usedIndexOfSource (x : Source) : Fin 49 :=
  if x.index.val = 0 then 0
    else if x.index.val = 1 then 1
    else if x.index.val = 2 then 2
    else if x.index.val = 3 then 3
    else if x.index.val = 5 then 4
    else if x.index.val = 6 then 5
    else if x.index.val = 8 then 6
    else if x.index.val = 12 then 7
    else if x.index.val = 22 then 8
    else if x.index.val = 26 then 9
    else if x.index.val = 71 then 10
    else if x.index.val = 76 then 11
    else if x.index.val = 103 then 12
    else if x.index.val = 108 then 13
    else if x.index.val = 145 then 14
    else if x.index.val = 165 then 15
    else if x.index.val = 167 then 16
    else if x.index.val = 194 then 17
    else if x.index.val = 221 then 18
    else if x.index.val = 328 then 19
    else if x.index.val = 352 then 20
    else if x.index.val = 357 then 21
    else if x.index.val = 358 then 22
    else if x.index.val = 375 then 23
    else if x.index.val = 379 then 24
    else if x.index.val = 385 then 25
    else if x.index.val = 404 then 26
    else if x.index.val = 424 then 27
    else if x.index.val = 428 then 28
    else if x.index.val = 431 then 29
    else if x.index.val = 448 then 30
    else if x.index.val = 464 then 31
    else if x.index.val = 467 then 32
    else if x.index.val = 566 then 33
    else if x.index.val = 586 then 34
    else if x.index.val = 593 then 35
    else if x.index.val = 603 then 36
    else if x.index.val = 640 then 37
    else if x.index.val = 677 then 38
    else if x.index.val = 685 then 39
    else if x.index.val = 686 then 40
    else if x.index.val = 716 then 41
    else if x.index.val = 717 then 42
    else if x.index.val = 720 then 43
    else if x.index.val = 754 then 44
    else if x.index.val = 755 then 45
    else if x.index.val = 756 then 46
    else if x.index.val = 757 then 47
    else if x.index.val = 758 then 48
    else 0

@[simp] theorem usedIndexOfSource_used : ∀ k : Fin 49,
    usedIndexOfSource (usedSource k) = k := by
  decide +kernel

def usedEncode (x : Source) : PermutationFunctionPair 16 :=
  usedCode (usedIndexOfSource x)

@[simp] theorem usedEncode_used (k : Fin 49) :
    usedEncode (usedSource k) = sourceCode.encode (usedSource k) := by
  rw [usedEncode, usedIndexOfSource_used, sourceCode_encode_used]

private def state0Generators : Fin 8 → Source :=
  (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state0Used : Fin 8 → Fin 49 :=
  (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state1Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state1Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (43) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state2Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨352⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state2Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (43) (Fin.cases (20) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state3Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨145⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state3Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (43) (Fin.cases (14) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state4Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨424⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state4Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (43) (Fin.cases (10) (Fin.cases (27) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state5Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨379⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨424⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state5Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (43) (Fin.cases (24) (Fin.cases (10) (Fin.cases (27) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state6Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨165⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨424⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state6Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (43) (Fin.cases (15) (Fin.cases (10) (Fin.cases (27) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state7Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨754⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state7Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (44) (Fin.cases (43) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state8Generators : Fin 8 → Source :=
  (Fin.cases ((⟨685⟩ : Source)) (Fin.cases ((⟨754⟩ : Source)) (Fin.cases ((⟨720⟩ : Source)) (Fin.cases ((⟨145⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state8Used : Fin 8 → Fin 49 :=
  (Fin.cases (39) (Fin.cases (44) (Fin.cases (43) (Fin.cases (14) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state9Generators : Fin 8 → Source :=
  (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨464⟩ : Source)) (Fin.cases ((⟨755⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state9Used : Fin 8 → Fin 49 :=
  (Fin.cases (7) (Fin.cases (10) (Fin.cases (48) (Fin.cases (31) (Fin.cases (45) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state10Generators : Fin 8 → Source :=
  (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨71⟩ : Source)) (Fin.cases ((⟨758⟩ : Source)) (Fin.cases ((⟨464⟩ : Source)) (Fin.cases ((⟨755⟩ : Source)) (Fin.cases ((⟨165⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state10Used : Fin 8 → Fin 49 :=
  (Fin.cases (7) (Fin.cases (10) (Fin.cases (48) (Fin.cases (31) (Fin.cases (45) (Fin.cases (15) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state11Generators : Fin 8 → Source :=
  (Fin.cases ((⟨640⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨756⟩ : Source)) (Fin.cases ((⟨757⟩ : Source)) (Fin.cases ((⟨8⟩ : Source)) (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨677⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state11Used : Fin 8 → Fin 49 :=
  (Fin.cases (37) (Fin.cases (11) (Fin.cases (46) (Fin.cases (47) (Fin.cases (6) (Fin.cases (7) (Fin.cases (38) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

private def state12Generators : Fin 8 → Source :=
  (Fin.cases ((⟨640⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨756⟩ : Source)) (Fin.cases ((⟨757⟩ : Source)) (Fin.cases ((⟨8⟩ : Source)) (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨677⟩ : Source)) (Fin.cases ((⟨165⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state12Used : Fin 8 → Fin 49 :=
  (Fin.cases (37) (Fin.cases (11) (Fin.cases (46) (Fin.cases (47) (Fin.cases (6) (Fin.cases (7) (Fin.cases (38) (Fin.cases (15) (fun i => Fin.elim0 i)))))))))

private def state13Generators : Fin 8 → Source :=
  (Fin.cases ((⟨22⟩ : Source)) (Fin.cases ((⟨640⟩ : Source)) (Fin.cases ((⟨76⟩ : Source)) (Fin.cases ((⟨756⟩ : Source)) (Fin.cases ((⟨757⟩ : Source)) (Fin.cases ((⟨8⟩ : Source)) (Fin.cases ((⟨12⟩ : Source)) (Fin.cases ((⟨677⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state13Used : Fin 8 → Fin 49 :=
  (Fin.cases (8) (Fin.cases (37) (Fin.cases (11) (Fin.cases (46) (Fin.cases (47) (Fin.cases (6) (Fin.cases (7) (Fin.cases (38) (fun i => Fin.elim0 i)))))))))

private def state14Generators : Fin 8 → Source :=
  (Fin.cases ((⟨1⟩ : Source)) (Fin.cases ((⟨2⟩ : Source)) (Fin.cases ((⟨3⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (Fin.cases ((⟨0⟩ : Source)) (fun i => Fin.elim0 i)))))))))

private def state14Used : Fin 8 → Fin 49 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (Fin.cases (0) (fun i => Fin.elim0 i)))))))))

def stateGenerators : Fin 15 → Fin 8 → Source :=
  (Fin.cases (state0Generators) (Fin.cases (state1Generators) (Fin.cases (state2Generators) (Fin.cases (state3Generators) (Fin.cases (state4Generators) (Fin.cases (state5Generators) (Fin.cases (state6Generators) (Fin.cases (state7Generators) (Fin.cases (state8Generators) (Fin.cases (state9Generators) (Fin.cases (state10Generators) (Fin.cases (state11Generators) (Fin.cases (state12Generators) (Fin.cases (state13Generators) (Fin.cases (state14Generators) (fun i => Fin.elim0 i))))))))))))))))

def stateUsed : Fin 15 → Fin 8 → Fin 49 :=
  (Fin.cases (state0Used) (Fin.cases (state1Used) (Fin.cases (state2Used) (Fin.cases (state3Used) (Fin.cases (state4Used) (Fin.cases (state5Used) (Fin.cases (state6Used) (Fin.cases (state7Used) (Fin.cases (state8Used) (Fin.cases (state9Used) (Fin.cases (state10Used) (Fin.cases (state11Used) (Fin.cases (state12Used) (Fin.cases (state13Used) (Fin.cases (state14Used) (fun i => Fin.elim0 i))))))))))))))))

@[simp] theorem stateGenerators_eq_used : ∀ (s : Fin 15) (k : Fin 8),
    stateGenerators s k = usedSource (stateUsed s k) := by
  decide +kernel

def representativeUsed : Fin 28 → Fin 49 :=
  (Fin.cases (0) (Fin.cases (38) (Fin.cases (32) (Fin.cases (48) (Fin.cases (29) (Fin.cases (39) (Fin.cases (11) (Fin.cases (41) (Fin.cases (28) (Fin.cases (26) (Fin.cases (8) (Fin.cases (34) (Fin.cases (23) (Fin.cases (30) (Fin.cases (35) (Fin.cases (22) (Fin.cases (36) (Fin.cases (21) (Fin.cases (19) (Fin.cases (25) (Fin.cases (33) (Fin.cases (13) (Fin.cases (18) (Fin.cases (16) (Fin.cases (40) (Fin.cases (42) (Fin.cases (17) (Fin.cases (9) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))

@[simp] theorem topRepresentative_eq_used : ∀ j : Fin 28,
    topRepresentative j = usedSource (representativeUsed j) := by
  decide +kernel

def ambientUsed : Fin 3 → Fin 49 :=
  (Fin.cases (1) (Fin.cases (2) (Fin.cases (3) (fun i => Fin.elim0 i))))

@[simp] theorem topAmbient_eq_used : ∀ j : Fin 3,
    topAmbient j = usedSource (ambientUsed j) := by
  decide +kernel

def child : Fin 15 → Fin 28 → Fin 15 :=
  (Fin.cases ((Fin.cases (0) (Fin.cases (9) (Fin.cases (4) (Fin.cases (7) (Fin.cases (9) (Fin.cases (1) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (5) (Fin.cases (6) (Fin.cases (2) (Fin.cases (5) (Fin.cases (6) (Fin.cases (3) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (1) (Fin.cases (9) (Fin.cases (4) (Fin.cases (7) (Fin.cases (9) (Fin.cases (1) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (5) (Fin.cases (6) (Fin.cases (2) (Fin.cases (5) (Fin.cases (6) (Fin.cases (3) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (2) (Fin.cases (10) (Fin.cases (6) (Fin.cases (8) (Fin.cases (10) (Fin.cases (2) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (6) (Fin.cases (2) (Fin.cases (10) (Fin.cases (6) (Fin.cases (8) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (3) (Fin.cases (10) (Fin.cases (5) (Fin.cases (8) (Fin.cases (10) (Fin.cases (3) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (5) (Fin.cases (10) (Fin.cases (8) (Fin.cases (5) (Fin.cases (10) (Fin.cases (3) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (4) (Fin.cases (9) (Fin.cases (4) (Fin.cases (9) (Fin.cases (9) (Fin.cases (4) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (5) (Fin.cases (6) (Fin.cases (6) (Fin.cases (5) (Fin.cases (6) (Fin.cases (5) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (5) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (10) (Fin.cases (5) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (5) (Fin.cases (10) (Fin.cases (10) (Fin.cases (5) (Fin.cases (10) (Fin.cases (5) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (6) (Fin.cases (10) (Fin.cases (6) (Fin.cases (10) (Fin.cases (10) (Fin.cases (6) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (6) (Fin.cases (6) (Fin.cases (10) (Fin.cases (6) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (7) (Fin.cases (9) (Fin.cases (9) (Fin.cases (7) (Fin.cases (9) (Fin.cases (7) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (8) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (10) (Fin.cases (10) (Fin.cases (8) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (9) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (10) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (11) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (12) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (13) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (Fin.cases ((Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (Fin.cases (14) (fun i => Fin.elim0 i)))))))))))))))))))))))))))))) (fun i => Fin.elim0 i))))))))))))))))

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenFrameRow12NormalCore

end
