import SymmetricSubgroupAsymptotics.DerivedWordFiniteCertificate
import Mathlib.Tactic.FinCases
import SymmetricSubgroupAsymptotics.GeneratedAction16.DataChunk039

/-! Selected 64-row certificate for the derived subgroup of the literal
16T1547 action. Displayed original derived words generate the candidate;
all transitions, conjugates and original commutators are checked on the
sixteen original points. No ambient-group enumeration is imported. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped commutatorElement

namespace SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1547

abbrev Original :=
  Subgroup.closure (Set.range BinaryActionData16.node1547Generators)

def basisWords : Fin 5 → DerivedGeneratorWord (Fin 6) :=
  ![.comm 0 3, .comm 0 4, .comm 0 5, .comm 1 3,
    .comm 1 4]

private def ambientBasis (j : Fin 5) : Equiv.Perm (Fin 16) :=
  (basisWords j).eval BinaryActionData16.node1547Generators

private def rowWords (i : Fin 64) : List (Fin 5) :=
  ![[], [0], [1], [2], [3], [4], [0,1], [0,2],
    [0,3], [0,4], [1,0], [1,1], [1,2], [1,3], [1,4], [2,3],
    [2,4], [3,0], [3,4], [4,1], [4,3], [0,1,0], [0,1,1], [0,1,2],
    [0,1,3], [0,1,4], [0,2,3], [0,2,4], [0,3,0], [0,3,4], [0,4,1], [0,4,3],
    [1,0,2], [1,0,3], [1,1,2], [1,1,4], [1,2,3], [1,2,4], [1,3,4], [1,4,3],
    [2,3,0], [2,3,4], [2,4,1], [2,4,3], [0,1,0,2], [0,1,0,3], [0,1,1,2], [0,1,1,4],
    [0,1,2,3], [0,1,2,4], [0,1,3,4], [0,1,4,3], [0,2,3,0], [0,2,3,4], [0,2,4,1], [0,2,4,3],
    [1,0,2,3], [1,1,2,4], [1,2,3,4], [1,2,4,3], [0,1,0,2,3], [0,1,1,2,4], [0,1,2,3,4], [0,1,2,4,3]] i

def ambientRows (i : Fin 64) : Equiv.Perm (Fin 16) :=
  ((rowWords i).map ambientBasis).prod

private def elements (i : Fin 64) : Original :=
  ((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node1547Generators basisWords)).prod

private theorem basis_coe (j : Fin 5) :
    (derivedWordGenerators BinaryActionData16.node1547Generators basisWords j :
      Equiv.Perm (Fin 16)) = ambientBasis j :=
  closureGenerators_eval_coe BinaryActionData16.node1547Generators (basisWords j)

private theorem elements_coe (i : Fin 64) :
    (elements i : Equiv.Perm (Fin 16)) = ambientRows i := by
  change Original.subtype (((rowWords i).map
    (derivedWordGenerators BinaryActionData16.node1547Generators basisWords)).prod) = _
  have hf : Original.subtype ∘
      derivedWordGenerators BinaryActionData16.node1547Generators basisWords = ambientBasis := by
    funext j
    exact basis_coe j
  rw [map_list_prod, List.map_map, hf]
  rfl

private def next (i : Fin 64) (j : Fin 5) : Fin 64 :=
  ![![1,2,3,4,5], ![0,6,7,8,9], ![10,11,12,13,14], ![7,12,0,15,16],
    ![17,13,15,11,18], ![9,19,16,20,0], ![21,22,23,24,25], ![3,23,1,26,27],
    ![28,24,26,22,29], ![5,30,27,31,1], ![2,1,32,33,30], ![22,21,34,28,35],
    ![32,34,2,36,37], ![24,28,36,21,38], ![30,5,37,39,2], ![40,36,4,34,41],
    ![27,42,5,43,3], ![4,33,40,1,31], ![31,39,41,5,4], ![25,35,42,38,21],
    ![29,38,43,35,28], ![6,0,44,45,19], ![11,10,46,17,47], ![44,46,6,48,49],
    ![13,17,48,10,50], ![19,9,49,51,6], ![52,48,8,46,53], ![16,54,9,55,7],
    ![8,45,52,0,20], ![20,51,53,9,8], ![14,47,54,50,10], ![18,50,55,47,17],
    ![12,7,10,56,54], ![45,8,56,6,51], ![46,44,11,52,57], ![47,14,57,18,11],
    ![48,52,13,44,58], ![54,16,14,59,12], ![50,18,58,14,13], ![51,20,59,19,45],
    ![15,56,17,7,55], ![55,59,18,16,15], ![49,57,19,58,44], ![53,58,20,57,52],
    ![23,3,21,60,42], ![33,4,60,2,39], ![34,32,22,40,61], ![35,25,61,29,22],
    ![36,40,24,32,62], ![42,27,25,63,23], ![38,29,62,25,24], ![39,31,63,30,33],
    ![26,60,28,3,43], ![43,63,29,27,26], ![37,61,30,62,32], ![41,62,31,61,40],
    ![60,26,33,23,63], ![61,37,35,41,34], ![62,41,38,37,36], ![63,43,39,42,60],
    ![56,15,45,12,59], ![57,49,47,53,46], ![58,53,50,49,48], ![59,55,51,54,56]] i j

private def conjugateRow (i : Fin 6) (j : Fin 5) : Fin 64 :=
  ![![5,28,3,21,1], ![33,25,3,29,39], ![1,25,3,29,5],
    ![1,2,61,28,5], ![22,21,60,28,5], ![35,30,3,31,22]] i j

private def commutatorRow (i j : Fin 6) : Fin 64 :=
  ![![0,0,0,1,2,3], ![0,0,34,4,5,63], ![0,34,0,47,39,47],
    ![1,28,47,0,9,0], ![21,5,39,9,0,10], ![3,63,47,0,10,0]] i j

private theorem identity_pointwise : ∀ x : Fin 16, ambientRows 0 x = x := by
  decide +kernel

private theorem next_pointwise_row000 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (0 : Fin 64) j) x =
      (ambientRows (0 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row001 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (1 : Fin 64) j) x =
      (ambientRows (1 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row002 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (2 : Fin 64) j) x =
      (ambientRows (2 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row003 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (3 : Fin 64) j) x =
      (ambientRows (3 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row004 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (4 : Fin 64) j) x =
      (ambientRows (4 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row005 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (5 : Fin 64) j) x =
      (ambientRows (5 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row006 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (6 : Fin 64) j) x =
      (ambientRows (6 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row007 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (7 : Fin 64) j) x =
      (ambientRows (7 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row008 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (8 : Fin 64) j) x =
      (ambientRows (8 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row009 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (9 : Fin 64) j) x =
      (ambientRows (9 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row010 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (10 : Fin 64) j) x =
      (ambientRows (10 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row011 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (11 : Fin 64) j) x =
      (ambientRows (11 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row012 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (12 : Fin 64) j) x =
      (ambientRows (12 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row013 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (13 : Fin 64) j) x =
      (ambientRows (13 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row014 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (14 : Fin 64) j) x =
      (ambientRows (14 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row015 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (15 : Fin 64) j) x =
      (ambientRows (15 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row016 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (16 : Fin 64) j) x =
      (ambientRows (16 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row017 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (17 : Fin 64) j) x =
      (ambientRows (17 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row018 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (18 : Fin 64) j) x =
      (ambientRows (18 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row019 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (19 : Fin 64) j) x =
      (ambientRows (19 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row020 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (20 : Fin 64) j) x =
      (ambientRows (20 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row021 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (21 : Fin 64) j) x =
      (ambientRows (21 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row022 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (22 : Fin 64) j) x =
      (ambientRows (22 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row023 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (23 : Fin 64) j) x =
      (ambientRows (23 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row024 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (24 : Fin 64) j) x =
      (ambientRows (24 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row025 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (25 : Fin 64) j) x =
      (ambientRows (25 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row026 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (26 : Fin 64) j) x =
      (ambientRows (26 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row027 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (27 : Fin 64) j) x =
      (ambientRows (27 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row028 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (28 : Fin 64) j) x =
      (ambientRows (28 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row029 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (29 : Fin 64) j) x =
      (ambientRows (29 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row030 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (30 : Fin 64) j) x =
      (ambientRows (30 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row031 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (31 : Fin 64) j) x =
      (ambientRows (31 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row032 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (32 : Fin 64) j) x =
      (ambientRows (32 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row033 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (33 : Fin 64) j) x =
      (ambientRows (33 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row034 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (34 : Fin 64) j) x =
      (ambientRows (34 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row035 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (35 : Fin 64) j) x =
      (ambientRows (35 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row036 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (36 : Fin 64) j) x =
      (ambientRows (36 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row037 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (37 : Fin 64) j) x =
      (ambientRows (37 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row038 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (38 : Fin 64) j) x =
      (ambientRows (38 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row039 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (39 : Fin 64) j) x =
      (ambientRows (39 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row040 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (40 : Fin 64) j) x =
      (ambientRows (40 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row041 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (41 : Fin 64) j) x =
      (ambientRows (41 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row042 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (42 : Fin 64) j) x =
      (ambientRows (42 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row043 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (43 : Fin 64) j) x =
      (ambientRows (43 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row044 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (44 : Fin 64) j) x =
      (ambientRows (44 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row045 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (45 : Fin 64) j) x =
      (ambientRows (45 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row046 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (46 : Fin 64) j) x =
      (ambientRows (46 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row047 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (47 : Fin 64) j) x =
      (ambientRows (47 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row048 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (48 : Fin 64) j) x =
      (ambientRows (48 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row049 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (49 : Fin 64) j) x =
      (ambientRows (49 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row050 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (50 : Fin 64) j) x =
      (ambientRows (50 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row051 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (51 : Fin 64) j) x =
      (ambientRows (51 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row052 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (52 : Fin 64) j) x =
      (ambientRows (52 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row053 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (53 : Fin 64) j) x =
      (ambientRows (53 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row054 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (54 : Fin 64) j) x =
      (ambientRows (54 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row055 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (55 : Fin 64) j) x =
      (ambientRows (55 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row056 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (56 : Fin 64) j) x =
      (ambientRows (56 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row057 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (57 : Fin 64) j) x =
      (ambientRows (57 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row058 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (58 : Fin 64) j) x =
      (ambientRows (58 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row059 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (59 : Fin 64) j) x =
      (ambientRows (59 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row060 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (60 : Fin 64) j) x =
      (ambientRows (60 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row061 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (61 : Fin 64) j) x =
      (ambientRows (61 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row062 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (62 : Fin 64) j) x =
      (ambientRows (62 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise_row063 : ∀ (j : Fin 5) (x : Fin 16),
    ambientRows (next (63 : Fin 64) j) x =
      (ambientRows (63 : Fin 64) * ambientBasis j) x := by
  decide +kernel

private theorem next_pointwise : ∀ (i : Fin 64) (j : Fin 5) (x : Fin 16),
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

private theorem conjugate_pointwise : ∀ (i : Fin 6) (j : Fin 5) (x : Fin 16),
    ambientRows (conjugateRow i j) x =
      (BinaryActionData16.node1547Generators i * ambientBasis j *
        (BinaryActionData16.node1547Generators i)⁻¹) x := by
  intro i
  fin_cases i <;> decide +kernel

private theorem commutator_pointwise : ∀ (i j : Fin 6) (x : Fin 16),
    ambientRows (commutatorRow i j) x =
      ⁅BinaryActionData16.node1547Generators i,
        BinaryActionData16.node1547Generators j⁆ x := by
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
    (derivedWordGenerators BinaryActionData16.node1547Generators basisWords) 64 where
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
        (derivedWordGenerators BinaryActionData16.node1547Generators basisWords j :
          Equiv.Perm (Fin 16))
    rw [elements_coe, elements_coe, basis_coe]
    exact Equiv.ext (next_pointwise i j)
  words := rowWords
  words_eq _ := rfl

/-- Every row equation is on the same original action and the same displayed
derived words. The generic consumer supplies all derived-group reasoning. -/
def certificate : DerivedWordFiniteCertificate
    BinaryActionData16.node1547Generators basisWords 64 where
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
      BinaryActionData16.node1547Generators i *
        (derivedWordGenerators BinaryActionData16.node1547Generators basisWords j :
          Equiv.Perm (Fin 16)) * (BinaryActionData16.node1547Generators i)⁻¹
    rw [elements_coe, basis_coe]
    exact Equiv.ext (conjugate_pointwise i j)
  commutatorRow := commutatorRow
  commutator_eq := by
    intro i j
    apply Subtype.ext
    change (elements (commutatorRow i j) : Equiv.Perm (Fin 16)) =
      ⁅BinaryActionData16.node1547Generators i, BinaryActionData16.node1547Generators j⁆
    rw [elements_coe]
    exact Equiv.ext (commutator_pointwise i j)

/-- Public literal row binding for subsequent original-point centralizer checks. -/
theorem certificate_elements_coe (i : Fin 64) :
    (certificate.cayley.elements i : Equiv.Perm (Fin 16)) = ambientRows i :=
  elements_coe i

theorem card_commutator : Nat.card (commutator Original) = 64 :=
  certificate.card_commutator

private theorem noncentral_point :
    (BinaryActionData16.node1547Generators 0 * ambientBasis 0 *
      (BinaryActionData16.node1547Generators 0)⁻¹) (6 : Fin 16) ≠
        ambientBasis 0 (6 : Fin 16) := by
  decide +kernel

/-- A displayed original conjugation moves a displayed derived element.
This is whole-original-group noncentrality, not internal noncommutativity. -/
theorem commutator_not_le_center : ¬ commutator Original ≤ Subgroup.center Original := by
  intro h
  let d : Original := derivedWordGenerators BinaryActionData16.node1547Generators basisWords 0
  let u : Original := closureGenerators BinaryActionData16.node1547Generators 0
  have hd : d ∈ commutator Original :=
    (basisWords 0).eval_mem_commutator (closureGenerators BinaryActionData16.node1547Generators)
  have he : u * d = d * u := Subgroup.mem_center_iff.mp (h hd) u
  have hc : u * d * u⁻¹ = d := by
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  have hp := congrArg Subtype.val hc
  change BinaryActionData16.node1547Generators 0 *
    (derivedWordGenerators BinaryActionData16.node1547Generators basisWords 0 :
      Equiv.Perm (Fin 16)) * (BinaryActionData16.node1547Generators 0)⁻¹ =
    (derivedWordGenerators BinaryActionData16.node1547Generators basisWords 0 :
      Equiv.Perm (Fin 16)) at hp
  rw [basis_coe] at hp
  exact noncentral_point (congrArg (fun f : Equiv.Perm (Fin 16) => f 6) hp)

end SymmetricSubgroupAsymptotics.BinaryCarrierDerivedOrder16T1547
