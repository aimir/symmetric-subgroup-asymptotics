import SymmetricSubgroupAsymptotics.BinaryNormalSparseRegistry
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T27.States

/-! Selected original J=8T27 normal-registry pilot. Finite source data
are untrusted until these kernel proofs pass. No six-field profile or
energy/counting assertion is made by this registry stage. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
local instance : Group Source := BinaryMenuCayley8T27.group

private def childRows0 (j : Fin 1) : N0.state.Row := ⟨(51 : Fin 64)⟩
private def childIndex0 (j : Fin 1) : Fin 13 := (1 : Fin 13)

private theorem covers0 : ∀ z : Fin 64,
    N0.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows0 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (Fin.addCases (m := 32) (n := 32) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)) (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel)))

private theorem child0_generators : ∀ j : Fin 1, ∀ k,
    N0.normalGenerators k ∈ (states (childIndex0 j)).kernel := by
  intro j
  fin_cases j
  · intro k
    exact Fin.elim0 k

private theorem child0_lift : ∀ j : Fin 1,
    N0.cosets.representatives (childRows0 j).index ∈
      (states (childIndex0 j)).kernel := by
  intro j
  fin_cases j
  · change N0.cosets.representatives 51 ∈ N1.kernel
    have he : N0.cosets.representatives 51 =
        (⟨N1.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N1.normalCertificate _

private theorem child0_card : ∀ j : Fin 1,
    Nat.card (states (childIndex0 j)).kernel = Nat.card N0.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N1.kernel = Nat.card N0.kernel * 2
    norm_num [N1.kernel_card, N0.kernel_card]

private def children0 : BinaryNormalChildren generators_full (states 0) states where
  count := 1
  rows := childRows0
  covers := by
    rintro ⟨z⟩ hz
    exact covers0 z hz
  child := childIndex0
  generator_mem := child0_generators
  lift_mem := child0_lift
  child_card := child0_card

private def childRows1 (j : Fin 1) : N1.state.Row := ⟨(26 : Fin 32)⟩
private def childIndex1 (j : Fin 1) : Fin 13 := (2 : Fin 13)

private theorem covers1 : ∀ z : Fin 32,
    N1.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows1 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private theorem child1_generators : ∀ j : Fin 1, ∀ k,
    N1.normalGenerators k ∈ (states (childIndex1 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N1.normalGenerators k ∈ N2.kernel
    intro k
    have he : ∀ k : Fin 1, N1.normalGenerators k =
        (⟨N2.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _

private theorem child1_lift : ∀ j : Fin 1,
    N1.cosets.representatives (childRows1 j).index ∈
      (states (childIndex1 j)).kernel := by
  intro j
  fin_cases j
  · change N1.cosets.representatives 26 ∈ N2.kernel
    have he : N1.cosets.representatives 26 =
        (⟨N2.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _

private theorem child1_card : ∀ j : Fin 1,
    Nat.card (states (childIndex1 j)).kernel = Nat.card N1.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N2.kernel = Nat.card N1.kernel * 2
    norm_num [N2.kernel_card, N1.kernel_card]

private def children1 : BinaryNormalChildren generators_full (states 1) states where
  count := 1
  rows := childRows1
  covers := by
    rintro ⟨z⟩ hz
    exact covers1 z hz
  child := childIndex1
  generator_mem := child1_generators
  lift_mem := child1_lift
  child_card := child1_card

private def childRows2 (j : Fin 3) : N2.state.Row := ⟨((if j.val < 1 then 5 else (if j.val < 2 then 10 else 15)) : Fin 16)⟩
private def childIndex2 (j : Fin 3) : Fin 13 := ((if j.val < 1 then 7 else (if j.val < 2 then 3 else 4)) : Fin 13)

private theorem covers2 : ∀ z : Fin 16,
    N2.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows2 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child2_generators : ∀ j : Fin 3, ∀ k,
    N2.normalGenerators k ∈ (states (childIndex2 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N2.normalGenerators k ∈ N7.kernel
    intro k
    have he : ∀ k : Fin 2, N2.normalGenerators k =
        (⟨N7.normalCertificate.rows (((if k.val < 1 then 3 else 6) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change ∀ k, N2.normalGenerators k ∈ N3.kernel
    intro k
    have he : ∀ k : Fin 2, N2.normalGenerators k =
        (⟨N3.normalCertificate.rows (((if k.val < 1 then 3 else 6) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _
  · change ∀ k, N2.normalGenerators k ∈ N4.kernel
    intro k
    have he : ∀ k : Fin 2, N2.normalGenerators k =
        (⟨N4.normalCertificate.rows (((if k.val < 1 then 2 else 5) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _

private theorem child2_lift : ∀ j : Fin 3,
    N2.cosets.representatives (childRows2 j).index ∈
      (states (childIndex2 j)).kernel := by
  intro j
  fin_cases j
  · change N2.cosets.representatives 5 ∈ N7.kernel
    have he : N2.cosets.representatives 5 =
        (⟨N7.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change N2.cosets.representatives 10 ∈ N3.kernel
    have he : N2.cosets.representatives 10 =
        (⟨N3.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _
  · change N2.cosets.representatives 15 ∈ N4.kernel
    have he : N2.cosets.representatives 15 =
        (⟨N4.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _

private theorem child2_card : ∀ j : Fin 3,
    Nat.card (states (childIndex2 j)).kernel = Nat.card N2.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N7.kernel = Nat.card N2.kernel * 2
    norm_num [N7.kernel_card, N2.kernel_card]
  · change Nat.card N3.kernel = Nat.card N2.kernel * 2
    norm_num [N3.kernel_card, N2.kernel_card]
  · change Nat.card N4.kernel = Nat.card N2.kernel * 2
    norm_num [N4.kernel_card, N2.kernel_card]

private def children2 : BinaryNormalChildren generators_full (states 2) states where
  count := 3
  rows := childRows2
  covers := by
    rintro ⟨z⟩ hz
    exact covers2 z hz
  child := childIndex2
  generator_mem := child2_generators
  lift_mem := child2_lift
  child_card := child2_card

private def childRows3 (j : Fin 1) : N3.state.Row := ⟨(5 : Fin 8)⟩
private def childIndex3 (j : Fin 1) : Fin 13 := (8 : Fin 13)

private theorem covers3 : ∀ z : Fin 8,
    N3.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows3 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child3_generators : ∀ j : Fin 1, ∀ k,
    N3.normalGenerators k ∈ (states (childIndex3 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N3.normalGenerators k ∈ N8.kernel
    intro k
    have he : ∀ k : Fin 3, N3.normalGenerators k =
        (⟨N8.normalCertificate.rows (((if k.val < 1 then 8 else (if k.val < 2 then 6 else 13)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _

private theorem child3_lift : ∀ j : Fin 1,
    N3.cosets.representatives (childRows3 j).index ∈
      (states (childIndex3 j)).kernel := by
  intro j
  fin_cases j
  · change N3.cosets.representatives 5 ∈ N8.kernel
    have he : N3.cosets.representatives 5 =
        (⟨N8.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _

private theorem child3_card : ∀ j : Fin 1,
    Nat.card (states (childIndex3 j)).kernel = Nat.card N3.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N8.kernel = Nat.card N3.kernel * 2
    norm_num [N8.kernel_card, N3.kernel_card]

private def children3 : BinaryNormalChildren generators_full (states 3) states where
  count := 1
  rows := childRows3
  covers := by
    rintro ⟨z⟩ hz
    exact covers3 z hz
  child := childIndex3
  generator_mem := child3_generators
  lift_mem := child3_lift
  child_card := child3_card

private def childRows4 (j : Fin 3) : N4.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 4 else 5)) : Fin 8)⟩
private def childIndex4 (j : Fin 3) : Fin 13 := ((if j.val < 1 then 6 else (if j.val < 2 then 8 else 5)) : Fin 13)

private theorem covers4 : ∀ z : Fin 8,
    N4.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows4 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child4_generators : ∀ j : Fin 3, ∀ k,
    N4.normalGenerators k ∈ (states (childIndex4 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N4.normalGenerators k ∈ N6.kernel
    intro k
    have he : ∀ k : Fin 3, N4.normalGenerators k =
        (⟨N6.normalCertificate.rows (((if k.val < 1 then 3 else (if k.val < 2 then 5 else 10)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _
  · change ∀ k, N4.normalGenerators k ∈ N8.kernel
    intro k
    have he : ∀ k : Fin 3, N4.normalGenerators k =
        (⟨N8.normalCertificate.rows (((if k.val < 1 then 5 else (if k.val < 2 then 6 else 13)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change ∀ k, N4.normalGenerators k ∈ N5.kernel
    intro k
    have he : ∀ k : Fin 3, N4.normalGenerators k =
        (⟨N5.normalCertificate.rows (((if k.val < 1 then 5 else (if k.val < 2 then 6 else 13)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _

private theorem child4_lift : ∀ j : Fin 3,
    N4.cosets.representatives (childRows4 j).index ∈
      (states (childIndex4 j)).kernel := by
  intro j
  fin_cases j
  · change N4.cosets.representatives 1 ∈ N6.kernel
    have he : N4.cosets.representatives 1 =
        (⟨N6.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _
  · change N4.cosets.representatives 4 ∈ N8.kernel
    have he : N4.cosets.representatives 4 =
        (⟨N8.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change N4.cosets.representatives 5 ∈ N5.kernel
    have he : N4.cosets.representatives 5 =
        (⟨N5.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _

private theorem child4_card : ∀ j : Fin 3,
    Nat.card (states (childIndex4 j)).kernel = Nat.card N4.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N6.kernel = Nat.card N4.kernel * 2
    norm_num [N6.kernel_card, N4.kernel_card]
  · change Nat.card N8.kernel = Nat.card N4.kernel * 2
    norm_num [N8.kernel_card, N4.kernel_card]
  · change Nat.card N5.kernel = Nat.card N4.kernel * 2
    norm_num [N5.kernel_card, N4.kernel_card]

private def children4 : BinaryNormalChildren generators_full (states 4) states where
  count := 3
  rows := childRows4
  covers := by
    rintro ⟨z⟩ hz
    exact covers4 z hz
  child := childIndex4
  generator_mem := child4_generators
  lift_mem := child4_lift
  child_card := child4_card

private def childRows5 (j : Fin 1) : N5.state.Row := ⟨(1 : Fin 4)⟩
private def childIndex5 (j : Fin 1) : Fin 13 := (10 : Fin 13)

private theorem covers5 : ∀ z : Fin 4,
    N5.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows5 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child5_generators : ∀ j : Fin 1, ∀ k,
    N5.normalGenerators k ∈ (states (childIndex5 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N5.normalGenerators k ∈ N10.kernel
    intro k
    have he : ∀ k : Fin 3, N5.normalGenerators k =
        (⟨N10.normalCertificate.rows (((if k.val < 1 then 21 else (if k.val < 2 then 11 else 26)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _

private theorem child5_lift : ∀ j : Fin 1,
    N5.cosets.representatives (childRows5 j).index ∈
      (states (childIndex5 j)).kernel := by
  intro j
  fin_cases j
  · change N5.cosets.representatives 1 ∈ N10.kernel
    have he : N5.cosets.representatives 1 =
        (⟨N10.normalCertificate.rows 15⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _

private theorem child5_card : ∀ j : Fin 1,
    Nat.card (states (childIndex5 j)).kernel = Nat.card N5.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N10.kernel = Nat.card N5.kernel * 2
    norm_num [N10.kernel_card, N5.kernel_card]

private def children5 : BinaryNormalChildren generators_full (states 5) states where
  count := 1
  rows := childRows5
  covers := by
    rintro ⟨z⟩ hz
    exact covers5 z hz
  child := childIndex5
  generator_mem := child5_generators
  lift_mem := child5_lift
  child_card := child5_card

private def childRows6 (j : Fin 1) : N6.state.Row := ⟨(2 : Fin 4)⟩
private def childIndex6 (j : Fin 1) : Fin 13 := (10 : Fin 13)

private theorem covers6 : ∀ z : Fin 4,
    N6.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows6 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child6_generators : ∀ j : Fin 1, ∀ k,
    N6.normalGenerators k ∈ (states (childIndex6 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N6.normalGenerators k ∈ N10.kernel
    intro k
    have he : ∀ k : Fin 4, N6.normalGenerators k =
        (⟨N10.normalCertificate.rows (((if k.val < 2 then (if k.val < 1 then 15 else 11) else (if k.val < 3 then 13 else 26)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _

private theorem child6_lift : ∀ j : Fin 1,
    N6.cosets.representatives (childRows6 j).index ∈
      (states (childIndex6 j)).kernel := by
  intro j
  fin_cases j
  · change N6.cosets.representatives 2 ∈ N10.kernel
    have he : N6.cosets.representatives 2 =
        (⟨N10.normalCertificate.rows 5⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _

private theorem child6_card : ∀ j : Fin 1,
    Nat.card (states (childIndex6 j)).kernel = Nat.card N6.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N10.kernel = Nat.card N6.kernel * 2
    norm_num [N10.kernel_card, N6.kernel_card]

private def children6 : BinaryNormalChildren generators_full (states 6) states where
  count := 1
  rows := childRows6
  covers := by
    rintro ⟨z⟩ hz
    exact covers6 z hz
  child := childIndex6
  generator_mem := child6_generators
  lift_mem := child6_lift
  child_card := child6_card

private def childRows7 (j : Fin 1) : N7.state.Row := ⟨(7 : Fin 8)⟩
private def childIndex7 (j : Fin 1) : Fin 13 := (8 : Fin 13)

private theorem covers7 : ∀ z : Fin 8,
    N7.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows7 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child7_generators : ∀ j : Fin 1, ∀ k,
    N7.normalGenerators k ∈ (states (childIndex7 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N7.normalGenerators k ∈ N8.kernel
    intro k
    have he : ∀ k : Fin 3, N7.normalGenerators k =
        (⟨N8.normalCertificate.rows (((if k.val < 1 then 6 else (if k.val < 2 then 2 else 4)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _

private theorem child7_lift : ∀ j : Fin 1,
    N7.cosets.representatives (childRows7 j).index ∈
      (states (childIndex7 j)).kernel := by
  intro j
  fin_cases j
  · change N7.cosets.representatives 7 ∈ N8.kernel
    have he : N7.cosets.representatives 7 =
        (⟨N8.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _

private theorem child7_card : ∀ j : Fin 1,
    Nat.card (states (childIndex7 j)).kernel = Nat.card N7.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N8.kernel = Nat.card N7.kernel * 2
    norm_num [N8.kernel_card, N7.kernel_card]

private def children7 : BinaryNormalChildren generators_full (states 7) states where
  count := 1
  rows := childRows7
  covers := by
    rintro ⟨z⟩ hz
    exact covers7 z hz
  child := childIndex7
  generator_mem := child7_generators
  lift_mem := child7_lift
  child_card := child7_card

private def childRows8 (j : Fin 3) : N8.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex8 (j : Fin 3) : Fin 13 := ((if j.val < 1 then 10 else (if j.val < 2 then 11 else 9)) : Fin 13)

private theorem covers8 : ∀ z : Fin 4,
    N8.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows8 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child8_generators : ∀ j : Fin 3, ∀ k,
    N8.normalGenerators k ∈ (states (childIndex8 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N8.normalGenerators k ∈ N10.kernel
    intro k
    have he : ∀ k : Fin 3, N8.normalGenerators k =
        (⟨N10.normalCertificate.rows (((if k.val < 1 then 17 else (if k.val < 2 then 13 else 5)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change ∀ k, N8.normalGenerators k ∈ N11.kernel
    intro k
    have he : ∀ k : Fin 3, N8.normalGenerators k =
        (⟨N11.normalCertificate.rows (((if k.val < 1 then 20 else (if k.val < 2 then 14 else 6)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change ∀ k, N8.normalGenerators k ∈ N9.kernel
    intro k
    have he : ∀ k : Fin 3, N8.normalGenerators k =
        (⟨N9.normalCertificate.rows (((if k.val < 1 then 20 else (if k.val < 2 then 14 else 6)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N9.normalCertificate _

private theorem child8_lift : ∀ j : Fin 3,
    N8.cosets.representatives (childRows8 j).index ∈
      (states (childIndex8 j)).kernel := by
  intro j
  fin_cases j
  · change N8.cosets.representatives 1 ∈ N10.kernel
    have he : N8.cosets.representatives 1 =
        (⟨N10.normalCertificate.rows 15⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change N8.cosets.representatives 2 ∈ N11.kernel
    have he : N8.cosets.representatives 2 =
        (⟨N11.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change N8.cosets.representatives 3 ∈ N9.kernel
    have he : N8.cosets.representatives 3 =
        (⟨N9.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N9.normalCertificate _

private theorem child8_card : ∀ j : Fin 3,
    Nat.card (states (childIndex8 j)).kernel = Nat.card N8.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N10.kernel = Nat.card N8.kernel * 2
    norm_num [N10.kernel_card, N8.kernel_card]
  · change Nat.card N11.kernel = Nat.card N8.kernel * 2
    norm_num [N11.kernel_card, N8.kernel_card]
  · change Nat.card N9.kernel = Nat.card N8.kernel * 2
    norm_num [N9.kernel_card, N8.kernel_card]

private def children8 : BinaryNormalChildren generators_full (states 8) states where
  count := 3
  rows := childRows8
  covers := by
    rintro ⟨z⟩ hz
    exact covers8 z hz
  child := childIndex8
  generator_mem := child8_generators
  lift_mem := child8_lift
  child_card := child8_card

private def childRows9 (j : Fin 1) : N9.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex9 (j : Fin 1) : Fin 13 := (12 : Fin 13)

private theorem covers9 : ∀ z : Fin 2,
    N9.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows9 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child9_generators : ∀ j : Fin 1, ∀ k,
    N9.normalGenerators k ∈ (states (childIndex9 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N9.normalGenerators k ∈ N12.kernel
    intro k
    have he : ∀ k : Fin 3, N9.normalGenerators k =
        (⟨N12.normalCertificate.rows (((if k.val < 1 then 35 else (if k.val < 2 then 29 else 13)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child9_lift : ∀ j : Fin 1,
    N9.cosets.representatives (childRows9 j).index ∈
      (states (childIndex9 j)).kernel := by
  intro j
  fin_cases j
  · change N9.cosets.representatives 1 ∈ N12.kernel
    have he : N9.cosets.representatives 1 =
        (⟨N12.normalCertificate.rows 31⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child9_card : ∀ j : Fin 1,
    Nat.card (states (childIndex9 j)).kernel = Nat.card N9.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N12.kernel = Nat.card N9.kernel * 2
    norm_num [N12.kernel_card, N9.kernel_card]

private def children9 : BinaryNormalChildren generators_full (states 9) states where
  count := 1
  rows := childRows9
  covers := by
    rintro ⟨z⟩ hz
    exact covers9 z hz
  child := childIndex9
  generator_mem := child9_generators
  lift_mem := child9_lift
  child_card := child9_card

private def childRows10 (j : Fin 1) : N10.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex10 (j : Fin 1) : Fin 13 := (12 : Fin 13)

private theorem covers10 : ∀ z : Fin 2,
    N10.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows10 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child10_generators : ∀ j : Fin 1, ∀ k,
    N10.normalGenerators k ∈ (states (childIndex10 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N10.normalGenerators k ∈ N12.kernel
    intro k
    have he : ∀ k : Fin 4, N10.normalGenerators k =
        (⟨N12.normalCertificate.rows (((if k.val < 2 then (if k.val < 1 then 41 else 31) else (if k.val < 3 then 29 else 13)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child10_lift : ∀ j : Fin 1,
    N10.cosets.representatives (childRows10 j).index ∈
      (states (childIndex10 j)).kernel := by
  intro j
  fin_cases j
  · change N10.cosets.representatives 1 ∈ N12.kernel
    have he : N10.cosets.representatives 1 =
        (⟨N12.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child10_card : ∀ j : Fin 1,
    Nat.card (states (childIndex10 j)).kernel = Nat.card N10.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N12.kernel = Nat.card N10.kernel * 2
    norm_num [N12.kernel_card, N10.kernel_card]

private def children10 : BinaryNormalChildren generators_full (states 10) states where
  count := 1
  rows := childRows10
  covers := by
    rintro ⟨z⟩ hz
    exact covers10 z hz
  child := childIndex10
  generator_mem := child10_generators
  lift_mem := child10_lift
  child_card := child10_card

private def childRows11 (j : Fin 1) : N11.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex11 (j : Fin 1) : Fin 13 := (12 : Fin 13)

private theorem covers11 : ∀ z : Fin 2,
    N11.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows11 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child11_generators : ∀ j : Fin 1, ∀ k,
    N11.normalGenerators k ∈ (states (childIndex11 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N11.normalGenerators k ∈ N12.kernel
    intro k
    have he : ∀ k : Fin 4, N11.normalGenerators k =
        (⟨N12.normalCertificate.rows (((if k.val < 2 then (if k.val < 1 then 3 else 27) else (if k.val < 3 then 29 else 8)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child11_lift : ∀ j : Fin 1,
    N11.cosets.representatives (childRows11 j).index ∈
      (states (childIndex11 j)).kernel := by
  intro j
  fin_cases j
  · change N11.cosets.representatives 1 ∈ N12.kernel
    have he : N11.cosets.representatives 1 =
        (⟨N12.normalCertificate.rows 31⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child11_card : ∀ j : Fin 1,
    Nat.card (states (childIndex11 j)).kernel = Nat.card N11.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N12.kernel = Nat.card N11.kernel * 2
    norm_num [N12.kernel_card, N11.kernel_card]

private def children11 : BinaryNormalChildren generators_full (states 11) states where
  count := 1
  rows := childRows11
  covers := by
    rintro ⟨z⟩ hz
    exact covers11 z hz
  child := childIndex11
  generator_mem := child11_generators
  lift_mem := child11_lift
  child_card := child11_card

private def childRows12 (j : Fin 0) : N12.state.Row := Fin.elim0 j
private def childIndex12 (j : Fin 0) : Fin 13 := Fin.elim0 j

private theorem covers12 : ∀ z : Fin 1,
    N12.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 0, childRows12 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child12_generators : ∀ j : Fin 0, ∀ k,
    N12.normalGenerators k ∈ (states (childIndex12 j)).kernel := by
  intro j
  exact Fin.elim0 j

private theorem child12_lift : ∀ j : Fin 0,
    N12.cosets.representatives (childRows12 j).index ∈
      (states (childIndex12 j)).kernel := by
  intro j
  exact Fin.elim0 j

private theorem child12_card : ∀ j : Fin 0,
    Nat.card (states (childIndex12 j)).kernel = Nat.card N12.kernel * 2 := by
  intro j
  exact Fin.elim0 j

private def children12 : BinaryNormalChildren generators_full (states 12) states where
  count := 0
  rows := childRows12
  covers := by
    rintro ⟨z⟩ hz
    exact covers12 z hz
  child := childIndex12
  generator_mem := child12_generators
  lift_mem := child12_lift
  child_card := child12_card

private def children : (i : Fin 13) →
    BinaryNormalChildren generators_full (states i) states :=
  (Fin.cases children0 (Fin.cases children1 (Fin.cases children2 (Fin.cases children3 (Fin.cases children4 (Fin.cases children5 (Fin.cases children6 (Fin.cases children7 (Fin.cases children8 (Fin.cases children9 (Fin.cases children10 (Fin.cases children11 (Fin.cases children12 (fun i => Fin.elim0 i))))))))))))))

def registry : BinaryNormalSparseRegistry generators_full states where
  bottom := 0
  bottom_kernel := by
    change Subgroup.closure (Set.range N0.normalGenerators) = ⊥
    rw [show Set.range N0.normalGenerators = ∅ by ext x; simp]
    exact Subgroup.closure_empty
  children := children

theorem source_isPGroup : IsPGroup 2 Source :=
  IsPGroup.of_card (n := 6) (by rw [source_card]; rfl)

theorem complete (N : Subgroup Source) [N.Normal] :
    ∃ i, (states i).kernel = N := registry.complete source_isPGroup N

/-- Completeness concerns the same original literal Fin8 action. -/
theorem complete_original
    (N : Subgroup (Subgroup.closure (Set.range BinaryMenuCayley8T27.generators)))
    [N.Normal] :
    ∃ i, (states i).kernel.map BinaryMenuCayley8T27.originalEquiv.toMonoidHom = N :=
  registry.complete_map_of_equiv source_isPGroup BinaryMenuCayley8T27.originalEquiv N

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T27
