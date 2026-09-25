import SymmetricSubgroupAsymptotics.BinaryGeneratorMenu16T1086

/-! All actual index-two transitive children of b16_1086, using generator-sized edges. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryGeneratorChildren16T1086
open BinaryGeneratorMenu16T1086
private def C := BinaryMenuCayley16T1086.certificate
private def parity (i : Fin 1024) : Fin 16 :=
  Fin.ofNat 16 (((if (i.val) / 32 < 16 then (if (i.val) / 32 < 8 then (if (i.val) / 32 < 4 then (if (i.val) / 32 < 2 then (if (i.val) / 32 < 1 then 224274032986935117802236755640584101838 else 246782296409358482773398955868210122463) else (if (i.val) / 32 < 3 then 184242035066085257611311596758231940588 else 206750298488508622582473796985857961213)) else (if (i.val) / 32 < 6 then (if (i.val) / 32 < 5 then 297492262958503859508270975754793822393 else 274983999536080494537108775527167801768) else (if (i.val) / 32 < 7 then 337524260879353719699196134637145983643 else 315015997456930354728033934409519963018))) else (if (i.val) / 32 < 12 then (if (i.val) / 32 < 10 then (if (i.val) / 32 < 9 then 297492262958503859508270975754793822393 else 274983999536080494537108775527167801768) else (if (i.val) / 32 < 11 then 337524260879353719699196134637145983643 else 315015997456930354728033934409519963018)) else (if (i.val) / 32 < 14 then (if (i.val) / 32 < 13 then 224274032986935117802236755640584101838 else 246782296409358482773398955868210122463) else (if (i.val) / 32 < 15 then 184242035066085257611311596758231940588 else 206750298488508622582473796985857961213)))) else (if (i.val) / 32 < 24 then (if (i.val) / 32 < 20 then (if (i.val) / 32 < 18 then (if (i.val) / 32 < 17 then 65298367384857968926265831904600409687 else 42790103962434603955103631676974389062) else (if (i.val) / 32 < 19 then 25266369464008108735340673022248248437 else 2758106041584743764178472794622227812)) else (if (i.val) / 32 < 22 then (if (i.val) / 32 < 21 then 93500070511579980689975651563558088992 else 116008333934003345661137851791184109617) else (if (i.val) / 32 < 23 then 133532068432429840880900810445910250242 else 156040331854853205852063010673536270867))) else (if (i.val) / 32 < 28 then (if (i.val) / 32 < 26 then (if (i.val) / 32 < 25 then 93500070511579980689975651563558088992 else 116008333934003345661137851791184109617) else (if (i.val) / 32 < 27 then 133532068432429840880900810445910250242 else 156040331854853205852063010673536270867)) else (if (i.val) / 32 < 30 then (if (i.val) / 32 < 29 then 65298367384857968926265831904600409687 else 42790103962434603955103631676974389062) else (if (i.val) / 32 < 31 then 25266369464008108735340673022248248437 else 2758106041584743764178472794622227812))))) : ℕ) / 2 ^ (4 * ((i.val) % 32)) % 2 ^ 4)
private def values (bits : Fin 4 → Bool) (i : Fin 1024) : Bool :=
  (if (parity i).val < 8 then (if (parity i).val < 4 then (if (parity i).val < 2 then (if (parity i).val < 1 then true else (true == bits 0)) else (if (parity i).val < 3 then (true == bits 1) else ((true == bits 0) == bits 1))) else (if (parity i).val < 6 then (if (parity i).val < 5 then (true == bits 2) else ((true == bits 0) == bits 2)) else (if (parity i).val < 7 then ((true == bits 1) == bits 2) else (((true == bits 0) == bits 1) == bits 2)))) else (if (parity i).val < 12 then (if (parity i).val < 10 then (if (parity i).val < 9 then (true == bits 3) else ((true == bits 0) == bits 3)) else (if (parity i).val < 11 then ((true == bits 1) == bits 3) else (((true == bits 0) == bits 1) == bits 3))) else (if (parity i).val < 14 then (if (parity i).val < 13 then ((true == bits 2) == bits 3) else (((true == bits 0) == bits 2) == bits 3)) else (if (parity i).val < 15 then (((true == bits 1) == bits 2) == bits 3) else ((((true == bits 0) == bits 1) == bits 2) == bits 3)))))
private def characters : BinaryRowCharacters C where
  values := values
  identity_eq := by decide +kernel
  parent_eq := by decide +kernel

private def conjugator0 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,14,15,13,12,3,2,6,7,5,4,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,11,10,8,9,12,13,15,14,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow0 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 924 else 687) else (if j.val < 3 then 1019 else (if j.val < 4 then 243 else 104)))
private theorem generator_checked0 : ∀ j,
    characters.values (binaryAssignment (0 : Fin 16)) (generatorRow0 j) = true ∧
    C.rows (generatorRow0 j) = permutationCode (MulAut.conj conjugator0⁻¹ (registry.generators 1 j)) :=
  by decide +kernel

private def conjugator1 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,8,9,2,3,10,11,12,13,4,5,14,15,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,4,5,10,11,14,15,2,3,6,7,8,9,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow1 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 986 else 1006) else (if j.val < 3 then 1021 else (if j.val < 4 then 512 else 377)))
private theorem generator_checked1 : ∀ j,
    characters.values (binaryAssignment (1 : Fin 16)) (generatorRow1 j) = true ∧
    C.rows (generatorRow1 j) = permutationCode (MulAut.conj conjugator1⁻¹ (registry.generators 3 j)) :=
  by decide +kernel

private def conjugator2 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,14,15,9,8,5,4,6,7,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,11,10,12,13,9,8,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow2 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 953 else 655) else (if j.val < 3 then 1022 else (if j.val < 4 then 483 else 65)))
private theorem generator_checked2 : ∀ j,
    characters.values (binaryAssignment (2 : Fin 16)) (generatorRow2 j) = true ∧
    C.rows (generatorRow2 j) = permutationCode (MulAut.conj conjugator2⁻¹ (registry.generators 1 j)) :=
  by decide +kernel

private def conjugator3 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,3,2,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,3,2,4,5,6,7,10,11,8,9,15,14,13,12] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow3 (j : Fin 4) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 943 else 752) else (if j.val < 3 then 837 else 383))
private theorem generator_checked3 : ∀ j,
    characters.values (binaryAssignment (3 : Fin 16)) (generatorRow3 j) = true ∧
    C.rows (generatorRow3 j) = permutationCode (MulAut.conj conjugator3⁻¹ (registry.generators 4 j)) :=
  by decide +kernel

private def conjugator4 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,14,15,13,12,2,3,7,6,5,4,8,9,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,11,10,9,8,12,13,15,14,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow4 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 924 else 655) else (if j.val < 3 then 1019 else (if j.val < 4 then 227 else 78)))
private theorem generator_checked4 : ∀ j,
    characters.values (binaryAssignment (4 : Fin 16)) (generatorRow4 j) = true ∧
    C.rows (generatorRow4 j) = permutationCode (MulAut.conj conjugator4⁻¹ (registry.generators 1 j)) :=
  by decide +kernel

private def conjugator5 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,10,11,3,2,9,8,14,15,4,5,13,12,7,6] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,5,4,10,11,15,14,7,6,2,3,13,12,8,9] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow5 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 986 else 763) else (if j.val < 3 then 1021 else (if j.val < 4 then 850 else 351)))
private theorem generator_checked5 : ∀ j,
    characters.values (binaryAssignment (5 : Fin 16)) (generatorRow5 j) = true ∧
    C.rows (generatorRow5 j) = permutationCode (MulAut.conj conjugator5⁻¹ (registry.generators 0 j)) :=
  by decide +kernel

private def conjugator6 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,13,12,14,15,9,8,5,4,6,7,11,10] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,11,10,12,13,9,8,15,14,5,4,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow6 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 953 else 751) else (if j.val < 3 then 632 else (if j.val < 4 then 267 else 253)))
private theorem generator_checked6 : ∀ j,
    characters.values (binaryAssignment (6 : Fin 16)) (generatorRow6 j) = true ∧
    C.rows (generatorRow6 j) = permutationCode (MulAut.conj conjugator6⁻¹ (registry.generators 2 j)) :=
  by decide +kernel

private def conjugator8 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,15,14,13,12,3,2,7,6,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,10,11,9,8,12,13,14,15,5,4,3,2] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow8 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 924 else 719) else (if j.val < 3 then 887 else (if j.val < 4 then 340 else 479)))
private theorem generator_checked8 : ∀ j,
    characters.values (binaryAssignment (8 : Fin 16)) (generatorRow8 j) = true ∧
    C.rows (generatorRow8 j) = permutationCode (MulAut.conj conjugator8⁻¹ (registry.generators 2 j)) :=
  by decide +kernel

private def conjugator9 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,11,10,3,2,9,8,15,14,4,5,12,13,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,5,4,10,11,14,15,7,6,3,2,12,13,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow9 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 986 else 971) else (if j.val < 3 then 1021 else (if j.val < 4 then 793 else 275)))
private theorem generator_checked9 : ∀ j,
    characters.values (binaryAssignment (9 : Fin 16)) (generatorRow9 j) = true ∧
    C.rows (generatorRow9 j) = permutationCode (MulAut.conj conjugator9⁻¹ (registry.generators 3 j)) :=
  by decide +kernel

private def conjugator10 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,12,13,14,15,8,9,4,5,6,7,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,10,11,12,13,8,9,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow10 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 953 else 719) else (if j.val < 3 then 590 else (if j.val < 4 then 286 else 140)))
private theorem generator_checked10 : ∀ j,
    characters.values (binaryAssignment (10 : Fin 16)) (generatorRow10 j) = true ∧
    C.rows (generatorRow10 j) = permutationCode (MulAut.conj conjugator10⁻¹ (registry.generators 2 j)) :=
  by decide +kernel

private def conjugator11 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,6,7,4,5,2,3,15,14,8,9,11,10,13,12] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,6,7,4,5,2,3,10,11,13,12,15,14,9,8] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow11 (j : Fin 4) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 943 else 725) else (if j.val < 3 then 603 else 337))
private theorem generator_checked11 : ∀ j,
    characters.values (binaryAssignment (11 : Fin 16)) (generatorRow11 j) = true ∧
    C.rows (generatorRow11 j) = permutationCode (MulAut.conj conjugator11⁻¹ (registry.generators 4 j)) :=
  by decide +kernel

private def conjugator12 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,14,15,13,12,3,2,6,7,4,5,8,9,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,7,6,10,11,8,9,12,13,14,15,5,4,2,3] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow12 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 924 else 751) else (if j.val < 3 then 868 else (if j.val < 4 then 373 else 463)))
private theorem generator_checked12 : ∀ j,
    characters.values (binaryAssignment (12 : Fin 16)) (generatorRow12 j) = true ∧
    C.rows (generatorRow12 j) = permutationCode (MulAut.conj conjugator12⁻¹ (registry.generators 2 j)) :=
  by decide +kernel

private def conjugator13 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,8,9,2,3,10,11,12,13,4,5,14,15,6,7] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,4,5,10,11,14,15,2,3,6,7,8,9,12,13] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow13 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 986 else 654) else (if j.val < 3 then 1021 else (if j.val < 4 then 605 else 373)))
private theorem generator_checked13 : ∀ j,
    characters.values (binaryAssignment (13 : Fin 16)) (generatorRow13 j) = true ∧
    C.rows (generatorRow13 j) = permutationCode (MulAut.conj conjugator13⁻¹ (registry.generators 0 j)) :=
  by decide +kernel

private def conjugator14 : Equiv.Perm (Fin 16) where
  toFun x := (#[0,1,2,3,12,13,14,15,8,9,4,5,6,7,10,11] : Array (Fin 16))[x.val]!
  invFun x := (#[0,1,2,3,10,11,12,13,8,9,14,15,4,5,6,7] : Array (Fin 16))[x.val]!
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def generatorRow14 (j : Fin 5) : Fin 1024 :=
  (if j.val < 2 then (if j.val < 1 then 953 else 687) else (if j.val < 3 then 1022 else (if j.val < 4 then 439 else 6)))
private theorem generator_checked14 : ∀ j,
    characters.values (binaryAssignment (14 : Fin 16)) (generatorRow14 j) = true ∧
    C.rows (generatorRow14 j) = permutationCode (MulAut.conj conjugator14⁻¹ (registry.generators 1 j)) :=
  by decide +kernel

private theorem checked : ∀ bits : Fin 4 → Bool,
    (∃ j, bits j = false) →
    (∀ i j, characters.values bits (C.next i j) = (characters.values bits i == bits j)) →
    (∀ y : Fin 16, ∃ i, characters.values bits i = true ∧ encodedRowAction C i 0 = y) →
    ∃ k, ∃ g : Equiv.Perm (Fin 16), registry.order k * 2 = 1024 ∧
      ∀ j, ∃ i, characters.values bits i = true ∧
        C.rows i = permutationCode (MulAut.conj g⁻¹ (registry.generators k j)) := by
  intro bits
  obtain ⟨b,rfl⟩ := binaryAssignment_surjective 4 bits
  fin_cases b
  · intro _ _ _
    exact ⟨1,conjugator0,by decide +kernel,
      fun j => ⟨generatorRow0 j,generator_checked0 j⟩⟩
  · intro _ _ _
    exact ⟨3,conjugator1,by decide +kernel,
      fun j => ⟨generatorRow1 j,generator_checked1 j⟩⟩
  · intro _ _ _
    exact ⟨1,conjugator2,by decide +kernel,
      fun j => ⟨generatorRow2 j,generator_checked2 j⟩⟩
  · intro _ _ _
    exact ⟨4,conjugator3,by decide +kernel,
      fun j => ⟨generatorRow3 j,generator_checked3 j⟩⟩
  · intro _ _ _
    exact ⟨1,conjugator4,by decide +kernel,
      fun j => ⟨generatorRow4 j,generator_checked4 j⟩⟩
  · intro _ _ _
    exact ⟨0,conjugator5,by decide +kernel,
      fun j => ⟨generatorRow5 j,generator_checked5 j⟩⟩
  · intro _ _ _
    exact ⟨2,conjugator6,by decide +kernel,
      fun j => ⟨generatorRow6 j,generator_checked6 j⟩⟩
  · intro _ _ ht
    obtain ⟨i,hi,he⟩ := ht 8
    exact False.elim ((show ∀ i : Fin 1024, characters.values (binaryAssignment (7 : Fin 16)) i = true →
      encodedRowAction C i 0 ≠ 8 from (Fin.addCases (m := 512) (n := 512) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))))) (Fin.addCases (m := 256) (n := 256) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))))) (Fin.addCases (m := 128) (n := 128) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))) (Fin.addCases (m := 64) (n := 64) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))) (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))))))) i hi he)
  · intro _ _ _
    exact ⟨2,conjugator8,by decide +kernel,
      fun j => ⟨generatorRow8 j,generator_checked8 j⟩⟩
  · intro _ _ _
    exact ⟨3,conjugator9,by decide +kernel,
      fun j => ⟨generatorRow9 j,generator_checked9 j⟩⟩
  · intro _ _ _
    exact ⟨2,conjugator10,by decide +kernel,
      fun j => ⟨generatorRow10 j,generator_checked10 j⟩⟩
  · intro _ _ _
    exact ⟨4,conjugator11,by decide +kernel,
      fun j => ⟨generatorRow11 j,generator_checked11 j⟩⟩
  · intro _ _ _
    exact ⟨2,conjugator12,by decide +kernel,
      fun j => ⟨generatorRow12 j,generator_checked12 j⟩⟩
  · intro _ _ _
    exact ⟨0,conjugator13,by decide +kernel,
      fun j => ⟨generatorRow13 j,generator_checked13 j⟩⟩
  · intro _ _ _
    exact ⟨1,conjugator14,by decide +kernel,
      fun j => ⟨generatorRow14 j,generator_checked14 j⟩⟩
  · intro hn _ _
    exact False.elim ((show ¬(∃ j : Fin 4, binaryAssignment (15 : Fin 16) j = false)
      from by decide +kernel) hn)

/-- Every actual transitive index-two child is covered in its original permutation action. -/
theorem children (K : Subgroup (Equiv.Perm (Fin 16)))
    (hle : K ≤ Subgroup.closure (Set.range BinaryMenuCayley16T1086.generators))
    (hindex : K.relIndex (Subgroup.closure (Set.range BinaryMenuCayley16T1086.generators)) = 2)
    (ht : PermutationSubgroupTransitive K) : ActionRegistryCovered actions K :=
  binary_generator_registry_children C characters actions registry
    BinaryMenuCayley16T1086.rows_injective 0 checked K hle hindex ht

end SymmetricSubgroupAsymptotics.BinaryGeneratorChildren16T1086
