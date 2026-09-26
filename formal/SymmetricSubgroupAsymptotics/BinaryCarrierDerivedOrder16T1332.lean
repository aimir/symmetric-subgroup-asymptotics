import SymmetricSubgroupAsymptotics.DerivedWordFiniteCertificate
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk034

/-! Selected 64-row certificate for the derived subgroup of the literal
16T1332 action. Displayed original derived words generate the candidate;
all transitions, conjugates and original commutators are checked on the
sixteen original points. No ambient-group enumeration is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1332

abbrev Original :=
  Subgroup.closure (Set.range BinaryActionData16.node1332Generators)

def basisWords : Fin 6 → DerivedGeneratorWord (Fin 5) :=
  ![.comm 0 2, .comm 0 4, .comm 1 2, .comm 1 4,
    .comm 2 4, .comm 3 4]

private def ambientBasis (j : Fin 6) : Equiv.Perm (Fin 16) :=
  (basisWords j).eval BinaryActionData16.node1332Generators

private def rowWords (i : Fin 64) : List (Fin 6) :=
  ![[], [0], [1], [2], [3], [4], [5], [0,1],
    [0,2], [0,3], [0,4], [0,5], [1,2], [1,3], [1,4], [1,5],
    [2,3], [2,4], [2,5], [3,4], [3,5], [4,3], [4,5], [5,1],
    [5,3], [5,4], [0,1,2], [0,1,3], [0,1,4], [0,1,5], [0,2,3], [0,2,4],
    [0,2,5], [0,3,4], [0,3,5], [0,4,3], [0,4,5], [0,5,1], [0,5,3], [0,5,4],
    [1,2,3], [1,2,4], [1,3,4], [1,3,5], [1,4,3], [1,4,5], [1,5,3], [1,5,4],
    [3,4,5], [3,5,4], [0,1,2,3], [0,1,2,4], [0,1,3,4], [0,1,3,5], [0,1,4,3], [0,1,4,5],
    [0,1,5,3], [0,1,5,4], [0,3,4,5], [0,3,5,4], [1,3,4,5], [1,3,5,4], [0,1,3,4,5], [0,1,3,5,4]] i

def ambientRows (i : Fin 64) : Equiv.Perm (Fin 16) :=
  ((rowWords i).map ambientBasis).prod

private def elements (i : Fin 64) : Original :=
  ((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node1332Generators basisWords)).prod

private theorem basis_coe (j : Fin 6) :
    (derivedWordGenerators BinaryActionData16.node1332Generators basisWords j :
      Equiv.Perm (Fin 16)) = ambientBasis j :=
  closureGenerators_eval_coe BinaryActionData16.node1332Generators (basisWords j)

private theorem elements_coe (i : Fin 64) :
    (elements i : Equiv.Perm (Fin 16)) = ambientRows i := by
  change Original.subtype (((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node1332Generators basisWords)).prod) = _
  have hf : Original.subtype ∘
      derivedWordGenerators BinaryActionData16.node1332Generators basisWords = ambientBasis := by
    funext j
    exact basis_coe j
  rw [map_list_prod, List.map_map, hf]
  rfl

private def next (i : Fin 64) (j : Fin 6) : Fin 64 :=
  ![![1,2,3,4,5,6], ![0,7,8,9,10,11], ![7,0,12,13,14,15], ![8,12,0,16,17,18],
    ![9,13,16,0,19,20], ![10,14,17,21,8,22], ![11,23,18,24,25,8], ![2,1,26,27,28,29],
    ![3,26,1,30,31,32], ![4,27,30,1,33,34], ![5,28,31,35,3,36], ![6,37,32,38,39,3],
    ![26,3,2,40,41,37], ![27,4,40,2,42,43], ![28,5,41,44,26,45], ![29,32,37,46,47,26],
    ![30,40,4,3,35,38], ![31,41,5,33,1,39], ![32,29,6,34,36,1], ![33,42,35,31,30,48],
    ![34,46,38,32,49,30], ![35,44,33,5,4,49], ![36,47,39,48,6,31], ![37,6,29,43,45,2],
    ![38,43,34,6,48,4], ![39,45,36,49,32,5], ![12,8,7,50,51,23], ![13,9,50,7,52,53],
    ![14,10,51,54,12,55], ![15,18,23,56,57,12], ![16,50,9,8,21,24], ![17,51,10,19,0,25],
    ![18,15,11,20,22,0], ![19,52,21,17,16,58], ![20,56,24,18,59,16], ![21,54,19,10,9,59],
    ![22,57,25,58,11,17], ![23,11,15,53,55,7], ![24,53,20,11,58,9], ![25,55,22,59,18,10],
    ![50,16,13,12,54,56], ![51,17,14,52,7,57], ![52,19,54,51,50,60], ![53,24,56,23,61,50],
    ![54,21,52,14,13,61], ![55,25,57,60,15,51], ![56,20,53,15,60,13], ![57,22,55,61,23,14],
    ![58,61,59,22,20,21], ![59,60,58,25,24,19], ![40,30,27,26,44,46], ![41,31,28,42,2,47],
    ![42,33,44,41,40,62], ![43,38,46,37,63,40], ![44,35,42,28,27,63], ![45,39,47,62,29,41],
    ![46,34,43,29,62,27], ![47,36,45,63,37,28], ![48,63,49,36,34,35], ![49,62,48,39,38,33],
    ![62,49,63,45,43,44], ![63,48,62,47,46,42], ![60,59,61,55,53,54], ![61,58,60,57,56,52]] i j

private def conjugateRow (i : Fin 5) (j : Fin 6) : Fin 64 :=
  ![![1,2,3,4,5,11], ![1,2,3,4,17,18], ![1,26,3,16,31,11],
    ![1,12,3,16,10,6], ![3,7,1,16,31,32]] i j

private def commutatorRow (i j : Fin 5) : Fin 64 :=
  ![![0,0,1,0,2], ![0,0,3,3,4], ![1,3,0,1,5],
    ![0,3,1,0,6], ![2,4,31,32,0]] i j

private theorem identity_pointwise : ∀ x : Fin 16, ambientRows 0 x = x := by
  decide +kernel

private theorem next_pointwise_row000 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (0 : Fin 64) j) x =
      (ambientRows (0 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row001 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (1 : Fin 64) j) x =
      (ambientRows (1 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row002 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (2 : Fin 64) j) x =
      (ambientRows (2 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row003 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (3 : Fin 64) j) x =
      (ambientRows (3 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row004 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (4 : Fin 64) j) x =
      (ambientRows (4 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row005 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (5 : Fin 64) j) x =
      (ambientRows (5 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row006 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (6 : Fin 64) j) x =
      (ambientRows (6 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row007 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (7 : Fin 64) j) x =
      (ambientRows (7 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row008 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (8 : Fin 64) j) x =
      (ambientRows (8 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row009 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (9 : Fin 64) j) x =
      (ambientRows (9 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row010 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (10 : Fin 64) j) x =
      (ambientRows (10 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row011 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (11 : Fin 64) j) x =
      (ambientRows (11 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row012 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (12 : Fin 64) j) x =
      (ambientRows (12 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row013 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (13 : Fin 64) j) x =
      (ambientRows (13 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row014 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (14 : Fin 64) j) x =
      (ambientRows (14 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row015 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (15 : Fin 64) j) x =
      (ambientRows (15 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row016 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (16 : Fin 64) j) x =
      (ambientRows (16 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row017 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (17 : Fin 64) j) x =
      (ambientRows (17 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row018 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (18 : Fin 64) j) x =
      (ambientRows (18 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row019 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (19 : Fin 64) j) x =
      (ambientRows (19 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row020 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (20 : Fin 64) j) x =
      (ambientRows (20 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row021 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (21 : Fin 64) j) x =
      (ambientRows (21 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row022 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (22 : Fin 64) j) x =
      (ambientRows (22 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row023 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (23 : Fin 64) j) x =
      (ambientRows (23 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row024 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (24 : Fin 64) j) x =
      (ambientRows (24 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row025 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (25 : Fin 64) j) x =
      (ambientRows (25 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row026 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (26 : Fin 64) j) x =
      (ambientRows (26 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row027 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (27 : Fin 64) j) x =
      (ambientRows (27 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row028 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (28 : Fin 64) j) x =
      (ambientRows (28 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row029 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (29 : Fin 64) j) x =
      (ambientRows (29 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row030 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (30 : Fin 64) j) x =
      (ambientRows (30 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row031 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (31 : Fin 64) j) x =
      (ambientRows (31 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row032 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (32 : Fin 64) j) x =
      (ambientRows (32 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row033 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (33 : Fin 64) j) x =
      (ambientRows (33 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row034 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (34 : Fin 64) j) x =
      (ambientRows (34 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row035 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (35 : Fin 64) j) x =
      (ambientRows (35 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row036 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (36 : Fin 64) j) x =
      (ambientRows (36 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row037 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (37 : Fin 64) j) x =
      (ambientRows (37 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row038 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (38 : Fin 64) j) x =
      (ambientRows (38 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row039 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (39 : Fin 64) j) x =
      (ambientRows (39 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row040 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (40 : Fin 64) j) x =
      (ambientRows (40 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row041 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (41 : Fin 64) j) x =
      (ambientRows (41 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row042 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (42 : Fin 64) j) x =
      (ambientRows (42 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row043 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (43 : Fin 64) j) x =
      (ambientRows (43 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row044 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (44 : Fin 64) j) x =
      (ambientRows (44 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row045 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (45 : Fin 64) j) x =
      (ambientRows (45 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row046 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (46 : Fin 64) j) x =
      (ambientRows (46 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row047 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (47 : Fin 64) j) x =
      (ambientRows (47 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row048 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (48 : Fin 64) j) x =
      (ambientRows (48 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row049 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (49 : Fin 64) j) x =
      (ambientRows (49 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row050 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (50 : Fin 64) j) x =
      (ambientRows (50 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row051 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (51 : Fin 64) j) x =
      (ambientRows (51 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row052 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (52 : Fin 64) j) x =
      (ambientRows (52 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row053 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (53 : Fin 64) j) x =
      (ambientRows (53 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row054 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (54 : Fin 64) j) x =
      (ambientRows (54 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row055 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (55 : Fin 64) j) x =
      (ambientRows (55 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row056 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (56 : Fin 64) j) x =
      (ambientRows (56 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row057 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (57 : Fin 64) j) x =
      (ambientRows (57 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row058 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (58 : Fin 64) j) x =
      (ambientRows (58 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row059 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (59 : Fin 64) j) x =
      (ambientRows (59 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row060 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (60 : Fin 64) j) x =
      (ambientRows (60 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row061 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (61 : Fin 64) j) x =
      (ambientRows (61 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row062 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (62 : Fin 64) j) x =
      (ambientRows (62 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row063 : ∀ (j : Fin 6) (x : Fin 16),
    ambientRows (next (63 : Fin 64) j) x =
      (ambientRows (63 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise : ∀ (i : Fin 64) (j : Fin 6) (x : Fin 16),
    ambientRows (next i j) x = (ambientRows i * ambientBasis j) x := by
  intro i
  fin_cases i
  · exact next_pointwise_row000
  · exact next_pointwise_row001
  · exact next_pointwise_row002
  · exact next_pointwise_row003
  · exact next_pointwise_row004
  · exact next_pointwise_row005
  · exact next_pointwise_row006
  · exact next_pointwise_row007
  · exact next_pointwise_row008
  · exact next_pointwise_row009
  · exact next_pointwise_row010
  · exact next_pointwise_row011
  · exact next_pointwise_row012
  · exact next_pointwise_row013
  · exact next_pointwise_row014
  · exact next_pointwise_row015
  · exact next_pointwise_row016
  · exact next_pointwise_row017
  · exact next_pointwise_row018
  · exact next_pointwise_row019
  · exact next_pointwise_row020
  · exact next_pointwise_row021
  · exact next_pointwise_row022
  · exact next_pointwise_row023
  · exact next_pointwise_row024
  · exact next_pointwise_row025
  · exact next_pointwise_row026
  · exact next_pointwise_row027
  · exact next_pointwise_row028
  · exact next_pointwise_row029
  · exact next_pointwise_row030
  · exact next_pointwise_row031
  · exact next_pointwise_row032
  · exact next_pointwise_row033
  · exact next_pointwise_row034
  · exact next_pointwise_row035
  · exact next_pointwise_row036
  · exact next_pointwise_row037
  · exact next_pointwise_row038
  · exact next_pointwise_row039
  · exact next_pointwise_row040
  · exact next_pointwise_row041
  · exact next_pointwise_row042
  · exact next_pointwise_row043
  · exact next_pointwise_row044
  · exact next_pointwise_row045
  · exact next_pointwise_row046
  · exact next_pointwise_row047
  · exact next_pointwise_row048
  · exact next_pointwise_row049
  · exact next_pointwise_row050
  · exact next_pointwise_row051
  · exact next_pointwise_row052
  · exact next_pointwise_row053
  · exact next_pointwise_row054
  · exact next_pointwise_row055
  · exact next_pointwise_row056
  · exact next_pointwise_row057
  · exact next_pointwise_row058
  · exact next_pointwise_row059
  · exact next_pointwise_row060
  · exact next_pointwise_row061
  · exact next_pointwise_row062
  · exact next_pointwise_row063

private theorem conjugate_pointwise : ∀ (i : Fin 5) (j : Fin 6) (x : Fin 16),
    ambientRows (conjugateRow i j) x =
      (BinaryActionData16.node1332Generators i * ambientBasis j *
        (BinaryActionData16.node1332Generators i)⁻¹) x := by
  intro i
  fin_cases i <;> decide +kernel

private theorem commutator_pointwise : ∀ (i j : Fin 5) (x : Fin 16),
    ambientRows (commutatorRow i j) x =
      ⁅BinaryActionData16.node1332Generators i,
        BinaryActionData16.node1332Generators j⁆ x := by
  intro i
  fin_cases i <;> decide +kernel

private theorem pointwise_rows_injective_row000 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (0 : Fin 64) x = ambientRows j x) →
      (0 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row001 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (1 : Fin 64) x = ambientRows j x) →
      (1 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row002 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (2 : Fin 64) x = ambientRows j x) →
      (2 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row003 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (3 : Fin 64) x = ambientRows j x) →
      (3 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row004 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (4 : Fin 64) x = ambientRows j x) →
      (4 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row005 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (5 : Fin 64) x = ambientRows j x) →
      (5 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row006 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (6 : Fin 64) x = ambientRows j x) →
      (6 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row007 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (7 : Fin 64) x = ambientRows j x) →
      (7 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row008 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (8 : Fin 64) x = ambientRows j x) →
      (8 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row009 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (9 : Fin 64) x = ambientRows j x) →
      (9 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row010 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (10 : Fin 64) x = ambientRows j x) →
      (10 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row011 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (11 : Fin 64) x = ambientRows j x) →
      (11 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row012 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (12 : Fin 64) x = ambientRows j x) →
      (12 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row013 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (13 : Fin 64) x = ambientRows j x) →
      (13 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row014 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (14 : Fin 64) x = ambientRows j x) →
      (14 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row015 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (15 : Fin 64) x = ambientRows j x) →
      (15 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row016 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (16 : Fin 64) x = ambientRows j x) →
      (16 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row017 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (17 : Fin 64) x = ambientRows j x) →
      (17 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row018 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (18 : Fin 64) x = ambientRows j x) →
      (18 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row019 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (19 : Fin 64) x = ambientRows j x) →
      (19 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row020 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (20 : Fin 64) x = ambientRows j x) →
      (20 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row021 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (21 : Fin 64) x = ambientRows j x) →
      (21 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row022 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (22 : Fin 64) x = ambientRows j x) →
      (22 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row023 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (23 : Fin 64) x = ambientRows j x) →
      (23 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row024 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (24 : Fin 64) x = ambientRows j x) →
      (24 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row025 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (25 : Fin 64) x = ambientRows j x) →
      (25 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row026 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (26 : Fin 64) x = ambientRows j x) →
      (26 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row027 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (27 : Fin 64) x = ambientRows j x) →
      (27 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row028 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (28 : Fin 64) x = ambientRows j x) →
      (28 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row029 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (29 : Fin 64) x = ambientRows j x) →
      (29 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row030 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (30 : Fin 64) x = ambientRows j x) →
      (30 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row031 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (31 : Fin 64) x = ambientRows j x) →
      (31 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row032 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (32 : Fin 64) x = ambientRows j x) →
      (32 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row033 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (33 : Fin 64) x = ambientRows j x) →
      (33 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row034 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (34 : Fin 64) x = ambientRows j x) →
      (34 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row035 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (35 : Fin 64) x = ambientRows j x) →
      (35 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row036 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (36 : Fin 64) x = ambientRows j x) →
      (36 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row037 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (37 : Fin 64) x = ambientRows j x) →
      (37 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row038 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (38 : Fin 64) x = ambientRows j x) →
      (38 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row039 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (39 : Fin 64) x = ambientRows j x) →
      (39 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row040 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (40 : Fin 64) x = ambientRows j x) →
      (40 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row041 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (41 : Fin 64) x = ambientRows j x) →
      (41 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row042 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (42 : Fin 64) x = ambientRows j x) →
      (42 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row043 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (43 : Fin 64) x = ambientRows j x) →
      (43 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row044 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (44 : Fin 64) x = ambientRows j x) →
      (44 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row045 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (45 : Fin 64) x = ambientRows j x) →
      (45 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row046 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (46 : Fin 64) x = ambientRows j x) →
      (46 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row047 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (47 : Fin 64) x = ambientRows j x) →
      (47 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row048 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (48 : Fin 64) x = ambientRows j x) →
      (48 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row049 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (49 : Fin 64) x = ambientRows j x) →
      (49 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row050 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (50 : Fin 64) x = ambientRows j x) →
      (50 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row051 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (51 : Fin 64) x = ambientRows j x) →
      (51 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row052 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (52 : Fin 64) x = ambientRows j x) →
      (52 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row053 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (53 : Fin 64) x = ambientRows j x) →
      (53 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row054 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (54 : Fin 64) x = ambientRows j x) →
      (54 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row055 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (55 : Fin 64) x = ambientRows j x) →
      (55 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row056 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (56 : Fin 64) x = ambientRows j x) →
      (56 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row057 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (57 : Fin 64) x = ambientRows j x) →
      (57 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row058 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (58 : Fin 64) x = ambientRows j x) →
      (58 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row059 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (59 : Fin 64) x = ambientRows j x) →
      (59 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row060 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (60 : Fin 64) x = ambientRows j x) →
      (60 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row061 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (61 : Fin 64) x = ambientRows j x) →
      (61 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row062 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (62 : Fin 64) x = ambientRows j x) →
      (62 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective_row063 : ∀ j : Fin 64,
    (∀ x : Fin 16, ambientRows (63 : Fin 64) x = ambientRows j x) →
      (63 : Fin 64) = j := by
  decide +kernel

private theorem pointwise_rows_injective : ∀ i j : Fin 64,
    (∀ x : Fin 16, ambientRows i x = ambientRows j x) → i = j := by
  intro i
  fin_cases i
  · exact pointwise_rows_injective_row000
  · exact pointwise_rows_injective_row001
  · exact pointwise_rows_injective_row002
  · exact pointwise_rows_injective_row003
  · exact pointwise_rows_injective_row004
  · exact pointwise_rows_injective_row005
  · exact pointwise_rows_injective_row006
  · exact pointwise_rows_injective_row007
  · exact pointwise_rows_injective_row008
  · exact pointwise_rows_injective_row009
  · exact pointwise_rows_injective_row010
  · exact pointwise_rows_injective_row011
  · exact pointwise_rows_injective_row012
  · exact pointwise_rows_injective_row013
  · exact pointwise_rows_injective_row014
  · exact pointwise_rows_injective_row015
  · exact pointwise_rows_injective_row016
  · exact pointwise_rows_injective_row017
  · exact pointwise_rows_injective_row018
  · exact pointwise_rows_injective_row019
  · exact pointwise_rows_injective_row020
  · exact pointwise_rows_injective_row021
  · exact pointwise_rows_injective_row022
  · exact pointwise_rows_injective_row023
  · exact pointwise_rows_injective_row024
  · exact pointwise_rows_injective_row025
  · exact pointwise_rows_injective_row026
  · exact pointwise_rows_injective_row027
  · exact pointwise_rows_injective_row028
  · exact pointwise_rows_injective_row029
  · exact pointwise_rows_injective_row030
  · exact pointwise_rows_injective_row031
  · exact pointwise_rows_injective_row032
  · exact pointwise_rows_injective_row033
  · exact pointwise_rows_injective_row034
  · exact pointwise_rows_injective_row035
  · exact pointwise_rows_injective_row036
  · exact pointwise_rows_injective_row037
  · exact pointwise_rows_injective_row038
  · exact pointwise_rows_injective_row039
  · exact pointwise_rows_injective_row040
  · exact pointwise_rows_injective_row041
  · exact pointwise_rows_injective_row042
  · exact pointwise_rows_injective_row043
  · exact pointwise_rows_injective_row044
  · exact pointwise_rows_injective_row045
  · exact pointwise_rows_injective_row046
  · exact pointwise_rows_injective_row047
  · exact pointwise_rows_injective_row048
  · exact pointwise_rows_injective_row049
  · exact pointwise_rows_injective_row050
  · exact pointwise_rows_injective_row051
  · exact pointwise_rows_injective_row052
  · exact pointwise_rows_injective_row053
  · exact pointwise_rows_injective_row054
  · exact pointwise_rows_injective_row055
  · exact pointwise_rows_injective_row056
  · exact pointwise_rows_injective_row057
  · exact pointwise_rows_injective_row058
  · exact pointwise_rows_injective_row059
  · exact pointwise_rows_injective_row060
  · exact pointwise_rows_injective_row061
  · exact pointwise_rows_injective_row062
  · exact pointwise_rows_injective_row063

private def cayley : FiniteCayleyCertificate
    (derivedWordGenerators BinaryActionData16.node1332Generators basisWords) 64 where
  elements := elements
  identity := 0
  identity_eq := by
    apply Subtype.ext
    change (elements 0 : Equiv.Perm (Fin 16)) = 1
    rw [elements_coe]
    exact Equiv.ext identity_pointwise
  next := next
  next_eq := by
    intro i j
    apply Subtype.ext
    change (elements (next i j) : Equiv.Perm (Fin 16)) =
      (elements i : Equiv.Perm (Fin 16)) *
        (derivedWordGenerators BinaryActionData16.node1332Generators basisWords j :
          Equiv.Perm (Fin 16))
    rw [elements_coe, elements_coe, basis_coe]
    exact Equiv.ext (next_pointwise i j)
  words := rowWords
  words_eq _ := rfl

/-- Every row equation is on the same original action and the same displayed
derived words. The generic consumer supplies all derived-group reasoning. -/
def certificate : DerivedWordFiniteCertificate
    BinaryActionData16.node1332Generators basisWords 64 where
  cayley := cayley
  rows_injective := by
    intro i j h
    have he : (elements i : Equiv.Perm (Fin 16)) =
        (elements j : Equiv.Perm (Fin 16)) := congrArg Subtype.val h
    rw [elements_coe, elements_coe] at he
    exact pointwise_rows_injective i j (fun x => congrArg (fun f => f x) he)
  conjugateRow := conjugateRow
  conjugate_eq := by
    intro i j
    apply Subtype.ext
    change (elements (conjugateRow i j) : Equiv.Perm (Fin 16)) =
      BinaryActionData16.node1332Generators i *
        (derivedWordGenerators BinaryActionData16.node1332Generators basisWords j :
          Equiv.Perm (Fin 16)) * (BinaryActionData16.node1332Generators i)⁻¹
    rw [elements_coe, basis_coe]
    exact Equiv.ext (conjugate_pointwise i j)
  commutatorRow := commutatorRow
  commutator_eq := by
    intro i j
    apply Subtype.ext
    change (elements (commutatorRow i j) : Equiv.Perm (Fin 16)) =
      ⁅BinaryActionData16.node1332Generators i, BinaryActionData16.node1332Generators j⁆
    rw [elements_coe]
    exact Equiv.ext (commutator_pointwise i j)

/-- Public literal row binding for subsequent original-point centralizer checks. -/
theorem certificate_elements_coe (i : Fin 64) :
    (certificate.cayley.elements i : Equiv.Perm (Fin 16)) = ambientRows i :=
  elements_coe i

theorem card_commutator : Nat.card (commutator Original) = 64 :=
  certificate.card_commutator

private theorem noncentral_point :
    (BinaryActionData16.node1332Generators 4 * ambientBasis 0 *
      (BinaryActionData16.node1332Generators 4)⁻¹) (0 : Fin 16) ≠
        ambientBasis 0 (0 : Fin 16) := by
  decide +kernel

/-- A displayed original conjugation moves a displayed derived element.
This is whole-original-group noncentrality, not internal noncommutativity. -/
theorem commutator_not_le_center : ¬ commutator Original ≤ Subgroup.center Original := by
  intro h
  let d : Original := derivedWordGenerators BinaryActionData16.node1332Generators basisWords 0
  let u : Original := closureGenerators BinaryActionData16.node1332Generators 4
  have hd : d ∈ commutator Original :=
    (basisWords 0).eval_mem_commutator (closureGenerators BinaryActionData16.node1332Generators)
  have he : u * d = d * u := Subgroup.mem_center_iff.mp (h hd) u
  have hc : u * d * u⁻¹ = d := by
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  have hp := congrArg Subtype.val hc
  change BinaryActionData16.node1332Generators 4 *
    (derivedWordGenerators BinaryActionData16.node1332Generators basisWords 0 :
      Equiv.Perm (Fin 16)) * (BinaryActionData16.node1332Generators 4)⁻¹ =
    (derivedWordGenerators BinaryActionData16.node1332Generators basisWords 0 :
      Equiv.Perm (Fin 16)) at hp
  rw [basis_coe] at hp
  exact noncentral_point (congrArg (fun f : Equiv.Perm (Fin 16) => f 0) hp)

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1332
