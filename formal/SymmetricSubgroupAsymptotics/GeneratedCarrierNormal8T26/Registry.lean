import SymmetricSubgroupAsymptotics.BinaryNormalSparseRegistry
import SymmetricSubgroupAsymptotics.GeneratedCarrierNormal8T26.States

/-! Complete original normal registry for the explicitly selected 8T26.
Every original central involution in every literal quotient is checked;
no completeness or numerical carrier-profile claim is trusted from input. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26
local instance selectedRegistrySourceGroup : Group Source := BinaryMenuCayley8T26.group

private def childRows0 (j : Fin 1) : N0.state.Row := ⟨(26 : Fin 64)⟩
private def childIndex0 (j : Fin 1) : Fin 27 := (1 : Fin 27)

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
  · change N0.cosets.representatives 26 ∈ N1.kernel
    have he : N0.cosets.representatives 26 =
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

private def childRows1 (j : Fin 3) : N1.state.Row := ⟨((if j.val < 1 then 4 else (if j.val < 2 then 26 else 29)) : Fin 32)⟩
private def childIndex1 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 8 else (if j.val < 2 then 2 else 3)) : Fin 27)

private theorem covers1 : ∀ z : Fin 32,
    N1.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows1 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (Fin.addCases (m := 16) (n := 16) (by decide +kernel) (by decide +kernel))

private theorem child1_generators : ∀ j : Fin 3, ∀ k,
    N1.normalGenerators k ∈ (states (childIndex1 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N1.normalGenerators k ∈ N8.kernel
    intro k
    have he : ∀ k : Fin 1, N1.normalGenerators k =
        (⟨N8.normalCertificate.rows ((1 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change ∀ k, N1.normalGenerators k ∈ N2.kernel
    intro k
    have he : ∀ k : Fin 1, N1.normalGenerators k =
        (⟨N2.normalCertificate.rows ((1 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _
  · change ∀ k, N1.normalGenerators k ∈ N3.kernel
    intro k
    have he : ∀ k : Fin 1, N1.normalGenerators k =
        (⟨N3.normalCertificate.rows ((0 : Fin 4))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _

private theorem child1_lift : ∀ j : Fin 3,
    N1.cosets.representatives (childRows1 j).index ∈
      (states (childIndex1 j)).kernel := by
  intro j
  fin_cases j
  · change N1.cosets.representatives 4 ∈ N8.kernel
    have he : N1.cosets.representatives 4 =
        (⟨N8.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N8.normalCertificate _
  · change N1.cosets.representatives 26 ∈ N2.kernel
    have he : N1.cosets.representatives 26 =
        (⟨N2.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N2.normalCertificate _
  · change N1.cosets.representatives 29 ∈ N3.kernel
    have he : N1.cosets.representatives 29 =
        (⟨N3.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N3.normalCertificate _

private theorem child1_card : ∀ j : Fin 3,
    Nat.card (states (childIndex1 j)).kernel = Nat.card N1.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N8.kernel = Nat.card N1.kernel * 2
    norm_num [N8.kernel_card, N1.kernel_card]
  · change Nat.card N2.kernel = Nat.card N1.kernel * 2
    norm_num [N2.kernel_card, N1.kernel_card]
  · change Nat.card N3.kernel = Nat.card N1.kernel * 2
    norm_num [N3.kernel_card, N1.kernel_card]

private def children1 : BinaryNormalChildren generators_full (states 1) states where
  count := 3
  rows := childRows1
  covers := by
    rintro ⟨z⟩ hz
    exact covers1 z hz
  child := childIndex1
  generator_mem := child1_generators
  lift_mem := child1_lift
  child_card := child1_card

private def childRows2 (j : Fin 3) : N2.state.Row := ⟨((if j.val < 1 then 4 else (if j.val < 2 then 14 else 15)) : Fin 16)⟩
private def childIndex2 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 11 else (if j.val < 2 then 5 else 4)) : Fin 27)

private theorem covers2 : ∀ z : Fin 16,
    N2.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows2 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child2_generators : ∀ j : Fin 3, ∀ k,
    N2.normalGenerators k ∈ (states (childIndex2 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N2.normalGenerators k ∈ N11.kernel
    intro k
    have he : ∀ k : Fin 1, N2.normalGenerators k =
        (⟨N11.normalCertificate.rows ((4 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change ∀ k, N2.normalGenerators k ∈ N5.kernel
    intro k
    have he : ∀ k : Fin 1, N2.normalGenerators k =
        (⟨N5.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _
  · change ∀ k, N2.normalGenerators k ∈ N4.kernel
    intro k
    have he : ∀ k : Fin 1, N2.normalGenerators k =
        (⟨N4.normalCertificate.rows ((5 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _

private theorem child2_lift : ∀ j : Fin 3,
    N2.cosets.representatives (childRows2 j).index ∈
      (states (childIndex2 j)).kernel := by
  intro j
  fin_cases j
  · change N2.cosets.representatives 4 ∈ N11.kernel
    have he : N2.cosets.representatives 4 =
        (⟨N11.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change N2.cosets.representatives 14 ∈ N5.kernel
    have he : N2.cosets.representatives 14 =
        (⟨N5.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N5.normalCertificate _
  · change N2.cosets.representatives 15 ∈ N4.kernel
    have he : N2.cosets.representatives 15 =
        (⟨N4.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N4.normalCertificate _

private theorem child2_card : ∀ j : Fin 3,
    Nat.card (states (childIndex2 j)).kernel = Nat.card N2.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N11.kernel = Nat.card N2.kernel * 2
    norm_num [N11.kernel_card, N2.kernel_card]
  · change Nat.card N5.kernel = Nat.card N2.kernel * 2
    norm_num [N5.kernel_card, N2.kernel_card]
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

private def childRows3 (j : Fin 3) : N3.state.Row := ⟨((if j.val < 1 then 2 else (if j.val < 2 then 4 else 10)) : Fin 16)⟩
private def childIndex3 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 7 else (if j.val < 2 then 11 else 6)) : Fin 27)

private theorem covers3 : ∀ z : Fin 16,
    N3.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows3 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child3_generators : ∀ j : Fin 3, ∀ k,
    N3.normalGenerators k ∈ (states (childIndex3 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N3.normalGenerators k ∈ N7.kernel
    intro k
    have he : ∀ k : Fin 2, N3.normalGenerators k =
        (⟨N7.normalCertificate.rows (((if k.val < 1 then 2 else 0) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change ∀ k, N3.normalGenerators k ∈ N11.kernel
    intro k
    have he : ∀ k : Fin 2, N3.normalGenerators k =
        (⟨N11.normalCertificate.rows (((if k.val < 1 then 3 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change ∀ k, N3.normalGenerators k ∈ N6.kernel
    intro k
    have he : ∀ k : Fin 2, N3.normalGenerators k =
        (⟨N6.normalCertificate.rows (((if k.val < 1 then 3 else 2) : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _

private theorem child3_lift : ∀ j : Fin 3,
    N3.cosets.representatives (childRows3 j).index ∈
      (states (childIndex3 j)).kernel := by
  intro j
  fin_cases j
  · change N3.cosets.representatives 2 ∈ N7.kernel
    have he : N3.cosets.representatives 2 =
        (⟨N7.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N7.normalCertificate _
  · change N3.cosets.representatives 4 ∈ N11.kernel
    have he : N3.cosets.representatives 4 =
        (⟨N11.normalCertificate.rows 0⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change N3.cosets.representatives 10 ∈ N6.kernel
    have he : N3.cosets.representatives 10 =
        (⟨N6.normalCertificate.rows 4⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N6.normalCertificate _

private theorem child3_card : ∀ j : Fin 3,
    Nat.card (states (childIndex3 j)).kernel = Nat.card N3.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N7.kernel = Nat.card N3.kernel * 2
    norm_num [N7.kernel_card, N3.kernel_card]
  · change Nat.card N11.kernel = Nat.card N3.kernel * 2
    norm_num [N11.kernel_card, N3.kernel_card]
  · change Nat.card N6.kernel = Nat.card N3.kernel * 2
    norm_num [N6.kernel_card, N3.kernel_card]

private def children3 : BinaryNormalChildren generators_full (states 3) states where
  count := 3
  rows := childRows3
  covers := by
    rintro ⟨z⟩ hz
    exact covers3 z hz
  child := childIndex3
  generator_mem := child3_generators
  lift_mem := child3_lift
  child_card := child3_card

private def childRows4 (j : Fin 1) : N4.state.Row := ⟨(4 : Fin 8)⟩
private def childIndex4 (j : Fin 1) : Fin 27 := (12 : Fin 27)

private theorem covers4 : ∀ z : Fin 8,
    N4.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows4 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child4_generators : ∀ j : Fin 1, ∀ k,
    N4.normalGenerators k ∈ (states (childIndex4 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N4.normalGenerators k ∈ N12.kernel
    intro k
    have he : ∀ k : Fin 2, N4.normalGenerators k =
        (⟨N12.normalCertificate.rows (((if k.val < 1 then 10 else 0) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child4_lift : ∀ j : Fin 1,
    N4.cosets.representatives (childRows4 j).index ∈
      (states (childIndex4 j)).kernel := by
  intro j
  fin_cases j
  · change N4.cosets.representatives 4 ∈ N12.kernel
    have he : N4.cosets.representatives 4 =
        (⟨N12.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child4_card : ∀ j : Fin 1,
    Nat.card (states (childIndex4 j)).kernel = Nat.card N4.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N12.kernel = Nat.card N4.kernel * 2
    norm_num [N12.kernel_card, N4.kernel_card]

private def children4 : BinaryNormalChildren generators_full (states 4) states where
  count := 1
  rows := childRows4
  covers := by
    rintro ⟨z⟩ hz
    exact covers4 z hz
  child := childIndex4
  generator_mem := child4_generators
  lift_mem := child4_lift
  child_card := child4_card

private def childRows5 (j : Fin 1) : N5.state.Row := ⟨(4 : Fin 8)⟩
private def childIndex5 (j : Fin 1) : Fin 27 := (12 : Fin 27)

private theorem covers5 : ∀ z : Fin 8,
    N5.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows5 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child5_generators : ∀ j : Fin 1, ∀ k,
    N5.normalGenerators k ∈ (states (childIndex5 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N5.normalGenerators k ∈ N12.kernel
    intro k
    have he : ∀ k : Fin 2, N5.normalGenerators k =
        (⟨N12.normalCertificate.rows (((if k.val < 1 then 10 else 13) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child5_lift : ∀ j : Fin 1,
    N5.cosets.representatives (childRows5 j).index ∈
      (states (childIndex5 j)).kernel := by
  intro j
  fin_cases j
  · change N5.cosets.representatives 4 ∈ N12.kernel
    have he : N5.cosets.representatives 4 =
        (⟨N12.normalCertificate.rows 2⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child5_card : ∀ j : Fin 1,
    Nat.card (states (childIndex5 j)).kernel = Nat.card N5.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N12.kernel = Nat.card N5.kernel * 2
    norm_num [N12.kernel_card, N5.kernel_card]

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

private def childRows6 (j : Fin 1) : N6.state.Row := ⟨(2 : Fin 8)⟩
private def childIndex6 (j : Fin 1) : Fin 27 := (17 : Fin 27)

private theorem covers6 : ∀ z : Fin 8,
    N6.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows6 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child6_generators : ∀ j : Fin 1, ∀ k,
    N6.normalGenerators k ∈ (states (childIndex6 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N6.normalGenerators k ∈ N17.kernel
    intro k
    have he : ∀ k : Fin 3, N6.normalGenerators k =
        (⟨N17.normalCertificate.rows (((if k.val < 1 then 6 else (if k.val < 2 then 11 else 4)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _

private theorem child6_lift : ∀ j : Fin 1,
    N6.cosets.representatives (childRows6 j).index ∈
      (states (childIndex6 j)).kernel := by
  intro j
  fin_cases j
  · change N6.cosets.representatives 2 ∈ N17.kernel
    have he : N6.cosets.representatives 2 =
        (⟨N17.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _

private theorem child6_card : ∀ j : Fin 1,
    Nat.card (states (childIndex6 j)).kernel = Nat.card N6.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N17.kernel = Nat.card N6.kernel * 2
    norm_num [N17.kernel_card, N6.kernel_card]

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

private def childRows7 (j : Fin 1) : N7.state.Row := ⟨(3 : Fin 8)⟩
private def childIndex7 (j : Fin 1) : Fin 27 := (17 : Fin 27)

private theorem covers7 : ∀ z : Fin 8,
    N7.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows7 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child7_generators : ∀ j : Fin 1, ∀ k,
    N7.normalGenerators k ∈ (states (childIndex7 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N7.normalGenerators k ∈ N17.kernel
    intro k
    have he : ∀ k : Fin 3, N7.normalGenerators k =
        (⟨N17.normalCertificate.rows (((if k.val < 1 then 5 else (if k.val < 2 then 6 else 4)) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _

private theorem child7_lift : ∀ j : Fin 1,
    N7.cosets.representatives (childRows7 j).index ∈
      (states (childIndex7 j)).kernel := by
  intro j
  fin_cases j
  · change N7.cosets.representatives 3 ∈ N17.kernel
    have he : N7.cosets.representatives 3 =
        (⟨N17.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _

private theorem child7_card : ∀ j : Fin 1,
    Nat.card (states (childIndex7 j)).kernel = Nat.card N7.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N17.kernel = Nat.card N7.kernel * 2
    norm_num [N17.kernel_card, N7.kernel_card]

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

private def childRows8 (j : Fin 3) : N8.state.Row := ⟨((if j.val < 1 then 5 else (if j.val < 2 then 14 else 15)) : Fin 16)⟩
private def childIndex8 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 10 else (if j.val < 2 then 11 else 9)) : Fin 27)

private theorem covers8 : ∀ z : Fin 16,
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
    have he : ∀ k : Fin 1, N8.normalGenerators k =
        (⟨N10.normalCertificate.rows ((1 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change ∀ k, N8.normalGenerators k ∈ N11.kernel
    intro k
    have he : ∀ k : Fin 1, N8.normalGenerators k =
        (⟨N11.normalCertificate.rows ((0 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change ∀ k, N8.normalGenerators k ∈ N9.kernel
    intro k
    have he : ∀ k : Fin 1, N8.normalGenerators k =
        (⟨N9.normalCertificate.rows ((1 : Fin 8))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N9.normalCertificate _

private theorem child8_lift : ∀ j : Fin 3,
    N8.cosets.representatives (childRows8 j).index ∈
      (states (childIndex8 j)).kernel := by
  intro j
  fin_cases j
  · change N8.cosets.representatives 5 ∈ N10.kernel
    have he : N8.cosets.representatives 5 =
        (⟨N10.normalCertificate.rows 4⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N10.normalCertificate _
  · change N8.cosets.representatives 14 ∈ N11.kernel
    have he : N8.cosets.representatives 14 =
        (⟨N11.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N11.normalCertificate _
  · change N8.cosets.representatives 15 ∈ N9.kernel
    have he : N8.cosets.representatives 15 =
        (⟨N9.normalCertificate.rows 4⟩ : Source) := by decide +kernel
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

private def childRows9 (j : Fin 1) : N9.state.Row := ⟨(5 : Fin 8)⟩
private def childIndex9 (j : Fin 1) : Fin 27 := (14 : Fin 27)

private theorem covers9 : ∀ z : Fin 8,
    N9.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows9 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child9_generators : ∀ j : Fin 1, ∀ k,
    N9.normalGenerators k ∈ (states (childIndex9 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N9.normalGenerators k ∈ N14.kernel
    intro k
    have he : ∀ k : Fin 2, N9.normalGenerators k =
        (⟨N14.normalCertificate.rows (((if k.val < 1 then 2 else 13) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _

private theorem child9_lift : ∀ j : Fin 1,
    N9.cosets.representatives (childRows9 j).index ∈
      (states (childIndex9 j)).kernel := by
  intro j
  fin_cases j
  · change N9.cosets.representatives 5 ∈ N14.kernel
    have he : N9.cosets.representatives 5 =
        (⟨N14.normalCertificate.rows 8⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _

private theorem child9_card : ∀ j : Fin 1,
    Nat.card (states (childIndex9 j)).kernel = Nat.card N9.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N14.kernel = Nat.card N9.kernel * 2
    norm_num [N14.kernel_card, N9.kernel_card]

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

private def childRows10 (j : Fin 1) : N10.state.Row := ⟨(7 : Fin 8)⟩
private def childIndex10 (j : Fin 1) : Fin 27 := (14 : Fin 27)

private theorem covers10 : ∀ z : Fin 8,
    N10.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows10 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child10_generators : ∀ j : Fin 1, ∀ k,
    N10.normalGenerators k ∈ (states (childIndex10 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N10.normalGenerators k ∈ N14.kernel
    intro k
    have he : ∀ k : Fin 2, N10.normalGenerators k =
        (⟨N14.normalCertificate.rows (((if k.val < 1 then 12 else 2) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _

private theorem child10_lift : ∀ j : Fin 1,
    N10.cosets.representatives (childRows10 j).index ∈
      (states (childIndex10 j)).kernel := by
  intro j
  fin_cases j
  · change N10.cosets.representatives 7 ∈ N14.kernel
    have he : N10.cosets.representatives 7 =
        (⟨N14.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _

private theorem child10_card : ∀ j : Fin 1,
    Nat.card (states (childIndex10 j)).kernel = Nat.card N10.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N14.kernel = Nat.card N10.kernel * 2
    norm_num [N14.kernel_card, N10.kernel_card]

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

private def childRows11 (j : Fin 7) : N11.state.Row := ⟨((if j.val < 3 then (if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) else (if j.val < 5 then (if j.val < 4 then 4 else 5) else (if j.val < 6 then 6 else 7))) : Fin 8)⟩
private def childIndex11 (j : Fin 7) : Fin 27 := ((if j.val < 3 then (if j.val < 1 then 22 else (if j.val < 2 then 17 else 15)) else (if j.val < 5 then (if j.val < 4 then 16 else 14) else (if j.val < 6 then 13 else 12))) : Fin 27)

private theorem covers11 : ∀ z : Fin 8,
    N11.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 7, childRows11 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child11_generators : ∀ j : Fin 7, ∀ k,
    N11.normalGenerators k ∈ (states (childIndex11 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N11.normalGenerators k ∈ N22.kernel
    intro k
    have he : ∀ k : Fin 2, N11.normalGenerators k =
        (⟨N22.normalCertificate.rows (((if k.val < 1 then 2 else 3) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _
  · change ∀ k, N11.normalGenerators k ∈ N17.kernel
    intro k
    have he : ∀ k : Fin 2, N11.normalGenerators k =
        (⟨N17.normalCertificate.rows (((if k.val < 1 then 1 else 3) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change ∀ k, N11.normalGenerators k ∈ N15.kernel
    intro k
    have he : ∀ k : Fin 2, N11.normalGenerators k =
        (⟨N15.normalCertificate.rows (((if k.val < 1 then 0 else 2) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N15.normalCertificate _
  · change ∀ k, N11.normalGenerators k ∈ N16.kernel
    intro k
    have he : ∀ k : Fin 2, N11.normalGenerators k =
        (⟨N16.normalCertificate.rows (((if k.val < 1 then 2 else 3) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change ∀ k, N11.normalGenerators k ∈ N14.kernel
    intro k
    have he : ∀ k : Fin 2, N11.normalGenerators k =
        (⟨N14.normalCertificate.rows (((if k.val < 1 then 2 else 3) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change ∀ k, N11.normalGenerators k ∈ N13.kernel
    intro k
    have he : ∀ k : Fin 2, N11.normalGenerators k =
        (⟨N13.normalCertificate.rows (((if k.val < 1 then 0 else 2) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _
  · change ∀ k, N11.normalGenerators k ∈ N12.kernel
    intro k
    have he : ∀ k : Fin 2, N11.normalGenerators k =
        (⟨N12.normalCertificate.rows (((if k.val < 1 then 2 else 3) : Fin 16))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child11_lift : ∀ j : Fin 7,
    N11.cosets.representatives (childRows11 j).index ∈
      (states (childIndex11 j)).kernel := by
  intro j
  fin_cases j
  · change N11.cosets.representatives 1 ∈ N22.kernel
    have he : N11.cosets.representatives 1 =
        (⟨N22.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N22.normalCertificate _
  · change N11.cosets.representatives 2 ∈ N17.kernel
    have he : N11.cosets.representatives 2 =
        (⟨N17.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N17.normalCertificate _
  · change N11.cosets.representatives 3 ∈ N15.kernel
    have he : N11.cosets.representatives 3 =
        (⟨N15.normalCertificate.rows 4⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N15.normalCertificate _
  · change N11.cosets.representatives 4 ∈ N16.kernel
    have he : N11.cosets.representatives 4 =
        (⟨N16.normalCertificate.rows 9⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N16.normalCertificate _
  · change N11.cosets.representatives 5 ∈ N14.kernel
    have he : N11.cosets.representatives 5 =
        (⟨N14.normalCertificate.rows 8⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N14.normalCertificate _
  · change N11.cosets.representatives 6 ∈ N13.kernel
    have he : N11.cosets.representatives 6 =
        (⟨N13.normalCertificate.rows 14⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N13.normalCertificate _
  · change N11.cosets.representatives 7 ∈ N12.kernel
    have he : N11.cosets.representatives 7 =
        (⟨N12.normalCertificate.rows 1⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N12.normalCertificate _

private theorem child11_card : ∀ j : Fin 7,
    Nat.card (states (childIndex11 j)).kernel = Nat.card N11.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N22.kernel = Nat.card N11.kernel * 2
    norm_num [N22.kernel_card, N11.kernel_card]
  · change Nat.card N17.kernel = Nat.card N11.kernel * 2
    norm_num [N17.kernel_card, N11.kernel_card]
  · change Nat.card N15.kernel = Nat.card N11.kernel * 2
    norm_num [N15.kernel_card, N11.kernel_card]
  · change Nat.card N16.kernel = Nat.card N11.kernel * 2
    norm_num [N16.kernel_card, N11.kernel_card]
  · change Nat.card N14.kernel = Nat.card N11.kernel * 2
    norm_num [N14.kernel_card, N11.kernel_card]
  · change Nat.card N13.kernel = Nat.card N11.kernel * 2
    norm_num [N13.kernel_card, N11.kernel_card]
  · change Nat.card N12.kernel = Nat.card N11.kernel * 2
    norm_num [N12.kernel_card, N11.kernel_card]

private def children11 : BinaryNormalChildren generators_full (states 11) states where
  count := 7
  rows := childRows11
  covers := by
    rintro ⟨z⟩ hz
    exact covers11 z hz
  child := childIndex11
  generator_mem := child11_generators
  lift_mem := child11_lift
  child_card := child11_card

private def childRows12 (j : Fin 3) : N12.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex12 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 23 else (if j.val < 2 then 19 else 20)) : Fin 27)

private theorem covers12 : ∀ z : Fin 4,
    N12.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows12 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child12_generators : ∀ j : Fin 3, ∀ k,
    N12.normalGenerators k ∈ (states (childIndex12 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N12.normalGenerators k ∈ N23.kernel
    intro k
    have he : ∀ k : Fin 3, N12.normalGenerators k =
        (⟨N23.normalCertificate.rows (((if k.val < 1 then 4 else (if k.val < 2 then 6 else 27)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change ∀ k, N12.normalGenerators k ∈ N19.kernel
    intro k
    have he : ∀ k : Fin 3, N12.normalGenerators k =
        (⟨N19.normalCertificate.rows (((if k.val < 1 then 5 else (if k.val < 2 then 7 else 27)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change ∀ k, N12.normalGenerators k ∈ N20.kernel
    intro k
    have he : ∀ k : Fin 3, N12.normalGenerators k =
        (⟨N20.normalCertificate.rows (((if k.val < 1 then 4 else (if k.val < 2 then 6 else 27)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _

private theorem child12_lift : ∀ j : Fin 3,
    N12.cosets.representatives (childRows12 j).index ∈
      (states (childIndex12 j)).kernel := by
  intro j
  fin_cases j
  · change N12.cosets.representatives 1 ∈ N23.kernel
    have he : N12.cosets.representatives 1 =
        (⟨N23.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change N12.cosets.representatives 2 ∈ N19.kernel
    have he : N12.cosets.representatives 2 =
        (⟨N19.normalCertificate.rows 15⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change N12.cosets.representatives 3 ∈ N20.kernel
    have he : N12.cosets.representatives 3 =
        (⟨N20.normalCertificate.rows 12⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _

private theorem child12_card : ∀ j : Fin 3,
    Nat.card (states (childIndex12 j)).kernel = Nat.card N12.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N23.kernel = Nat.card N12.kernel * 2
    norm_num [N23.kernel_card, N12.kernel_card]
  · change Nat.card N19.kernel = Nat.card N12.kernel * 2
    norm_num [N19.kernel_card, N12.kernel_card]
  · change Nat.card N20.kernel = Nat.card N12.kernel * 2
    norm_num [N20.kernel_card, N12.kernel_card]

private def children12 : BinaryNormalChildren generators_full (states 12) states where
  count := 3
  rows := childRows12
  covers := by
    rintro ⟨z⟩ hz
    exact covers12 z hz
  child := childIndex12
  generator_mem := child12_generators
  lift_mem := child12_lift
  child_card := child12_card

private def childRows13 (j : Fin 3) : N13.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex13 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 23 else (if j.val < 2 then 21 else 18)) : Fin 27)

private theorem covers13 : ∀ z : Fin 4,
    N13.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows13 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child13_generators : ∀ j : Fin 3, ∀ k,
    N13.normalGenerators k ∈ (states (childIndex13 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N13.normalGenerators k ∈ N23.kernel
    intro k
    have he : ∀ k : Fin 3, N13.normalGenerators k =
        (⟨N23.normalCertificate.rows (((if k.val < 1 then 23 else (if k.val < 2 then 4 else 6)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change ∀ k, N13.normalGenerators k ∈ N21.kernel
    intro k
    have he : ∀ k : Fin 3, N13.normalGenerators k =
        (⟨N21.normalCertificate.rows (((if k.val < 1 then 22 else (if k.val < 2 then 1 else 5)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change ∀ k, N13.normalGenerators k ∈ N18.kernel
    intro k
    have he : ∀ k : Fin 3, N13.normalGenerators k =
        (⟨N18.normalCertificate.rows (((if k.val < 1 then 23 else (if k.val < 2 then 4 else 6)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _

private theorem child13_lift : ∀ j : Fin 3,
    N13.cosets.representatives (childRows13 j).index ∈
      (states (childIndex13 j)).kernel := by
  intro j
  fin_cases j
  · change N13.cosets.representatives 1 ∈ N23.kernel
    have he : N13.cosets.representatives 1 =
        (⟨N23.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _
  · change N13.cosets.representatives 2 ∈ N21.kernel
    have he : N13.cosets.representatives 2 =
        (⟨N21.normalCertificate.rows 15⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change N13.cosets.representatives 3 ∈ N18.kernel
    have he : N13.cosets.representatives 3 =
        (⟨N18.normalCertificate.rows 19⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _

private theorem child13_card : ∀ j : Fin 3,
    Nat.card (states (childIndex13 j)).kernel = Nat.card N13.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N23.kernel = Nat.card N13.kernel * 2
    norm_num [N23.kernel_card, N13.kernel_card]
  · change Nat.card N21.kernel = Nat.card N13.kernel * 2
    norm_num [N21.kernel_card, N13.kernel_card]
  · change Nat.card N18.kernel = Nat.card N13.kernel * 2
    norm_num [N18.kernel_card, N13.kernel_card]

private def children13 : BinaryNormalChildren generators_full (states 13) states where
  count := 3
  rows := childRows13
  covers := by
    rintro ⟨z⟩ hz
    exact covers13 z hz
  child := childIndex13
  generator_mem := child13_generators
  lift_mem := child13_lift
  child_card := child13_card

private def childRows14 (j : Fin 3) : N14.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex14 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 24 else (if j.val < 2 then 19 else 18)) : Fin 27)

private theorem covers14 : ∀ z : Fin 4,
    N14.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows14 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child14_generators : ∀ j : Fin 3, ∀ k,
    N14.normalGenerators k ∈ (states (childIndex14 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N14.normalGenerators k ∈ N24.kernel
    intro k
    have he : ∀ k : Fin 3, N14.normalGenerators k =
        (⟨N24.normalCertificate.rows (((if k.val < 1 then 25 else (if k.val < 2 then 4 else 6)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change ∀ k, N14.normalGenerators k ∈ N19.kernel
    intro k
    have he : ∀ k : Fin 3, N14.normalGenerators k =
        (⟨N19.normalCertificate.rows (((if k.val < 1 then 24 else (if k.val < 2 then 5 else 7)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change ∀ k, N14.normalGenerators k ∈ N18.kernel
    intro k
    have he : ∀ k : Fin 3, N14.normalGenerators k =
        (⟨N18.normalCertificate.rows (((if k.val < 1 then 25 else (if k.val < 2 then 4 else 6)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _

private theorem child14_lift : ∀ j : Fin 3,
    N14.cosets.representatives (childRows14 j).index ∈
      (states (childIndex14 j)).kernel := by
  intro j
  fin_cases j
  · change N14.cosets.representatives 1 ∈ N24.kernel
    have he : N14.cosets.representatives 1 =
        (⟨N24.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change N14.cosets.representatives 2 ∈ N19.kernel
    have he : N14.cosets.representatives 2 =
        (⟨N19.normalCertificate.rows 15⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _
  · change N14.cosets.representatives 3 ∈ N18.kernel
    have he : N14.cosets.representatives 3 =
        (⟨N18.normalCertificate.rows 19⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _

private theorem child14_card : ∀ j : Fin 3,
    Nat.card (states (childIndex14 j)).kernel = Nat.card N14.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N24.kernel = Nat.card N14.kernel * 2
    norm_num [N24.kernel_card, N14.kernel_card]
  · change Nat.card N19.kernel = Nat.card N14.kernel * 2
    norm_num [N19.kernel_card, N14.kernel_card]
  · change Nat.card N18.kernel = Nat.card N14.kernel * 2
    norm_num [N18.kernel_card, N14.kernel_card]

private def children14 : BinaryNormalChildren generators_full (states 14) states where
  count := 3
  rows := childRows14
  covers := by
    rintro ⟨z⟩ hz
    exact covers14 z hz
  child := childIndex14
  generator_mem := child14_generators
  lift_mem := child14_lift
  child_card := child14_card

private def childRows15 (j : Fin 3) : N15.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex15 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 24 else (if j.val < 2 then 21 else 20)) : Fin 27)

private theorem covers15 : ∀ z : Fin 4,
    N15.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows15 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child15_generators : ∀ j : Fin 3, ∀ k,
    N15.normalGenerators k ∈ (states (childIndex15 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N15.normalGenerators k ∈ N24.kernel
    intro k
    have he : ∀ k : Fin 3, N15.normalGenerators k =
        (⟨N24.normalCertificate.rows (((if k.val < 1 then 4 else (if k.val < 2 then 6 else 21)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change ∀ k, N15.normalGenerators k ∈ N21.kernel
    intro k
    have he : ∀ k : Fin 3, N15.normalGenerators k =
        (⟨N21.normalCertificate.rows (((if k.val < 1 then 1 else (if k.val < 2 then 5 else 19)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change ∀ k, N15.normalGenerators k ∈ N20.kernel
    intro k
    have he : ∀ k : Fin 3, N15.normalGenerators k =
        (⟨N20.normalCertificate.rows (((if k.val < 1 then 4 else (if k.val < 2 then 6 else 21)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _

private theorem child15_lift : ∀ j : Fin 3,
    N15.cosets.representatives (childRows15 j).index ∈
      (states (childIndex15 j)).kernel := by
  intro j
  fin_cases j
  · change N15.cosets.representatives 1 ∈ N24.kernel
    have he : N15.cosets.representatives 1 =
        (⟨N24.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change N15.cosets.representatives 2 ∈ N21.kernel
    have he : N15.cosets.representatives 2 =
        (⟨N21.normalCertificate.rows 15⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change N15.cosets.representatives 3 ∈ N20.kernel
    have he : N15.cosets.representatives 3 =
        (⟨N20.normalCertificate.rows 19⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _

private theorem child15_card : ∀ j : Fin 3,
    Nat.card (states (childIndex15 j)).kernel = Nat.card N15.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N24.kernel = Nat.card N15.kernel * 2
    norm_num [N24.kernel_card, N15.kernel_card]
  · change Nat.card N21.kernel = Nat.card N15.kernel * 2
    norm_num [N21.kernel_card, N15.kernel_card]
  · change Nat.card N20.kernel = Nat.card N15.kernel * 2
    norm_num [N20.kernel_card, N15.kernel_card]

private def children15 : BinaryNormalChildren generators_full (states 15) states where
  count := 3
  rows := childRows15
  covers := by
    rintro ⟨z⟩ hz
    exact covers15 z hz
  child := childIndex15
  generator_mem := child15_generators
  lift_mem := child15_lift
  child_card := child15_card

private def childRows16 (j : Fin 3) : N16.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex16 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 25 else (if j.val < 2 then 20 else 18)) : Fin 27)

private theorem covers16 : ∀ z : Fin 4,
    N16.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows16 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child16_generators : ∀ j : Fin 3, ∀ k,
    N16.normalGenerators k ∈ (states (childIndex16 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N16.normalGenerators k ∈ N25.kernel
    intro k
    have he : ∀ k : Fin 2, N16.normalGenerators k =
        (⟨N25.normalCertificate.rows (((if k.val < 1 then 17 else 5) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change ∀ k, N16.normalGenerators k ∈ N20.kernel
    intro k
    have he : ∀ k : Fin 2, N16.normalGenerators k =
        (⟨N20.normalCertificate.rows (((if k.val < 1 then 17 else 4) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change ∀ k, N16.normalGenerators k ∈ N18.kernel
    intro k
    have he : ∀ k : Fin 2, N16.normalGenerators k =
        (⟨N18.normalCertificate.rows (((if k.val < 1 then 17 else 4) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _

private theorem child16_lift : ∀ j : Fin 3,
    N16.cosets.representatives (childRows16 j).index ∈
      (states (childIndex16 j)).kernel := by
  intro j
  fin_cases j
  · change N16.cosets.representatives 1 ∈ N25.kernel
    have he : N16.cosets.representatives 1 =
        (⟨N25.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change N16.cosets.representatives 2 ∈ N20.kernel
    have he : N16.cosets.representatives 2 =
        (⟨N20.normalCertificate.rows 12⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N20.normalCertificate _
  · change N16.cosets.representatives 3 ∈ N18.kernel
    have he : N16.cosets.representatives 3 =
        (⟨N18.normalCertificate.rows 16⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N18.normalCertificate _

private theorem child16_card : ∀ j : Fin 3,
    Nat.card (states (childIndex16 j)).kernel = Nat.card N16.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N25.kernel = Nat.card N16.kernel * 2
    norm_num [N25.kernel_card, N16.kernel_card]
  · change Nat.card N20.kernel = Nat.card N16.kernel * 2
    norm_num [N20.kernel_card, N16.kernel_card]
  · change Nat.card N18.kernel = Nat.card N16.kernel * 2
    norm_num [N18.kernel_card, N16.kernel_card]

private def children16 : BinaryNormalChildren generators_full (states 16) states where
  count := 3
  rows := childRows16
  covers := by
    rintro ⟨z⟩ hz
    exact covers16 z hz
  child := childIndex16
  generator_mem := child16_generators
  lift_mem := child16_lift
  child_card := child16_card

private def childRows17 (j : Fin 3) : N17.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex17 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 25 else (if j.val < 2 then 21 else 19)) : Fin 27)

private theorem covers17 : ∀ z : Fin 4,
    N17.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows17 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child17_generators : ∀ j : Fin 3, ∀ k,
    N17.normalGenerators k ∈ (states (childIndex17 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N17.normalGenerators k ∈ N25.kernel
    intro k
    have he : ∀ k : Fin 3, N17.normalGenerators k =
        (⟨N25.normalCertificate.rows (((if k.val < 1 then 5 else (if k.val < 2 then 7 else 13)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change ∀ k, N17.normalGenerators k ∈ N21.kernel
    intro k
    have he : ∀ k : Fin 3, N17.normalGenerators k =
        (⟨N21.normalCertificate.rows (((if k.val < 1 then 1 else (if k.val < 2 then 5 else 11)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change ∀ k, N17.normalGenerators k ∈ N19.kernel
    intro k
    have he : ∀ k : Fin 3, N17.normalGenerators k =
        (⟨N19.normalCertificate.rows (((if k.val < 1 then 5 else (if k.val < 2 then 7 else 13)) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child17_lift : ∀ j : Fin 3,
    N17.cosets.representatives (childRows17 j).index ∈
      (states (childIndex17 j)).kernel := by
  intro j
  fin_cases j
  · change N17.cosets.representatives 1 ∈ N25.kernel
    have he : N17.cosets.representatives 1 =
        (⟨N25.normalCertificate.rows 3⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change N17.cosets.representatives 2 ∈ N21.kernel
    have he : N17.cosets.representatives 2 =
        (⟨N21.normalCertificate.rows 9⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N21.normalCertificate _
  · change N17.cosets.representatives 3 ∈ N19.kernel
    have he : N17.cosets.representatives 3 =
        (⟨N19.normalCertificate.rows 17⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N19.normalCertificate _

private theorem child17_card : ∀ j : Fin 3,
    Nat.card (states (childIndex17 j)).kernel = Nat.card N17.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N25.kernel = Nat.card N17.kernel * 2
    norm_num [N25.kernel_card, N17.kernel_card]
  · change Nat.card N21.kernel = Nat.card N17.kernel * 2
    norm_num [N21.kernel_card, N17.kernel_card]
  · change Nat.card N19.kernel = Nat.card N17.kernel * 2
    norm_num [N19.kernel_card, N17.kernel_card]

private def children17 : BinaryNormalChildren generators_full (states 17) states where
  count := 3
  rows := childRows17
  covers := by
    rintro ⟨z⟩ hz
    exact covers17 z hz
  child := childIndex17
  generator_mem := child17_generators
  lift_mem := child17_lift
  child_card := child17_card

private def childRows18 (j : Fin 1) : N18.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex18 (j : Fin 1) : Fin 27 := (26 : Fin 27)

private theorem covers18 : ∀ z : Fin 2,
    N18.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows18 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child18_generators : ∀ j : Fin 1, ∀ k,
    N18.normalGenerators k ∈ (states (childIndex18 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N18.normalGenerators k ∈ N26.kernel
    intro k
    have he : ∀ k : Fin 3, N18.normalGenerators k =
        (⟨N26.normalCertificate.rows (((if k.val < 1 then 35 else (if k.val < 2 then 50 else 9)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child18_lift : ∀ j : Fin 1,
    N18.cosets.representatives (childRows18 j).index ∈
      (states (childIndex18 j)).kernel := by
  intro j
  fin_cases j
  · change N18.cosets.representatives 1 ∈ N26.kernel
    have he : N18.cosets.representatives 1 =
        (⟨N26.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child18_card : ∀ j : Fin 1,
    Nat.card (states (childIndex18 j)).kernel = Nat.card N18.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N26.kernel = Nat.card N18.kernel * 2
    norm_num [N26.kernel_card, N18.kernel_card]

private def children18 : BinaryNormalChildren generators_full (states 18) states where
  count := 1
  rows := childRows18
  covers := by
    rintro ⟨z⟩ hz
    exact covers18 z hz
  child := childIndex18
  generator_mem := child18_generators
  lift_mem := child18_lift
  child_card := child18_card

private def childRows19 (j : Fin 1) : N19.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex19 (j : Fin 1) : Fin 27 := (26 : Fin 27)

private theorem covers19 : ∀ z : Fin 2,
    N19.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows19 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child19_generators : ∀ j : Fin 1, ∀ k,
    N19.normalGenerators k ∈ (states (childIndex19 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N19.normalGenerators k ∈ N26.kernel
    intro k
    have he : ∀ k : Fin 4, N19.normalGenerators k =
        (⟨N26.normalCertificate.rows (((if k.val < 2 then (if k.val < 1 then 50 else 9) else (if k.val < 3 then 13 else 27)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child19_lift : ∀ j : Fin 1,
    N19.cosets.representatives (childRows19 j).index ∈
      (states (childIndex19 j)).kernel := by
  intro j
  fin_cases j
  · change N19.cosets.representatives 1 ∈ N26.kernel
    have he : N19.cosets.representatives 1 =
        (⟨N26.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child19_card : ∀ j : Fin 1,
    Nat.card (states (childIndex19 j)).kernel = Nat.card N19.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N26.kernel = Nat.card N19.kernel * 2
    norm_num [N26.kernel_card, N19.kernel_card]

private def children19 : BinaryNormalChildren generators_full (states 19) states where
  count := 1
  rows := childRows19
  covers := by
    rintro ⟨z⟩ hz
    exact covers19 z hz
  child := childIndex19
  generator_mem := child19_generators
  lift_mem := child19_lift
  child_card := child19_card

private def childRows20 (j : Fin 1) : N20.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex20 (j : Fin 1) : Fin 27 := (26 : Fin 27)

private theorem covers20 : ∀ z : Fin 2,
    N20.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows20 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child20_generators : ∀ j : Fin 1, ∀ k,
    N20.normalGenerators k ∈ (states (childIndex20 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N20.normalGenerators k ∈ N26.kernel
    intro k
    have he : ∀ k : Fin 3, N20.normalGenerators k =
        (⟨N26.normalCertificate.rows (((if k.val < 1 then 35 else (if k.val < 2 then 9 else 43)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child20_lift : ∀ j : Fin 1,
    N20.cosets.representatives (childRows20 j).index ∈
      (states (childIndex20 j)).kernel := by
  intro j
  fin_cases j
  · change N20.cosets.representatives 1 ∈ N26.kernel
    have he : N20.cosets.representatives 1 =
        (⟨N26.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child20_card : ∀ j : Fin 1,
    Nat.card (states (childIndex20 j)).kernel = Nat.card N20.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N26.kernel = Nat.card N20.kernel * 2
    norm_num [N26.kernel_card, N20.kernel_card]

private def children20 : BinaryNormalChildren generators_full (states 20) states where
  count := 1
  rows := childRows20
  covers := by
    rintro ⟨z⟩ hz
    exact covers20 z hz
  child := childIndex20
  generator_mem := child20_generators
  lift_mem := child20_lift
  child_card := child20_card

private def childRows21 (j : Fin 1) : N21.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex21 (j : Fin 1) : Fin 27 := (26 : Fin 27)

private theorem covers21 : ∀ z : Fin 2,
    N21.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows21 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child21_generators : ∀ j : Fin 1, ∀ k,
    N21.normalGenerators k ∈ (states (childIndex21 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N21.normalGenerators k ∈ N26.kernel
    intro k
    have he : ∀ k : Fin 4, N21.normalGenerators k =
        (⟨N26.normalCertificate.rows (((if k.val < 2 then (if k.val < 1 then 9 else 13) else (if k.val < 3 then 27 else 43)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child21_lift : ∀ j : Fin 1,
    N21.cosets.representatives (childRows21 j).index ∈
      (states (childIndex21 j)).kernel := by
  intro j
  fin_cases j
  · change N21.cosets.representatives 1 ∈ N26.kernel
    have he : N21.cosets.representatives 1 =
        (⟨N26.normalCertificate.rows 7⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child21_card : ∀ j : Fin 1,
    Nat.card (states (childIndex21 j)).kernel = Nat.card N21.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N26.kernel = Nat.card N21.kernel * 2
    norm_num [N26.kernel_card, N21.kernel_card]

private def children21 : BinaryNormalChildren generators_full (states 21) states where
  count := 1
  rows := childRows21
  covers := by
    rintro ⟨z⟩ hz
    exact covers21 z hz
  child := childIndex21
  generator_mem := child21_generators
  lift_mem := child21_lift
  child_card := child21_card

private def childRows22 (j : Fin 3) : N22.state.Row := ⟨((if j.val < 1 then 1 else (if j.val < 2 then 2 else 3)) : Fin 4)⟩
private def childIndex22 (j : Fin 3) : Fin 27 := ((if j.val < 1 then 25 else (if j.val < 2 then 24 else 23)) : Fin 27)

private theorem covers22 : ∀ z : Fin 4,
    N22.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 3, childRows22 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child22_generators : ∀ j : Fin 3, ∀ k,
    N22.normalGenerators k ∈ (states (childIndex22 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N22.normalGenerators k ∈ N25.kernel
    intro k
    have he : ∀ k : Fin 2, N22.normalGenerators k =
        (⟨N25.normalCertificate.rows (((if k.val < 1 then 3 else 14) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change ∀ k, N22.normalGenerators k ∈ N24.kernel
    intro k
    have he : ∀ k : Fin 2, N22.normalGenerators k =
        (⟨N24.normalCertificate.rows (((if k.val < 1 then 3 else 15) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change ∀ k, N22.normalGenerators k ∈ N23.kernel
    intro k
    have he : ∀ k : Fin 2, N22.normalGenerators k =
        (⟨N23.normalCertificate.rows (((if k.val < 1 then 3 else 15) : Fin 32))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _

private theorem child22_lift : ∀ j : Fin 3,
    N22.cosets.representatives (childRows22 j).index ∈
      (states (childIndex22 j)).kernel := by
  intro j
  fin_cases j
  · change N22.cosets.representatives 1 ∈ N25.kernel
    have he : N22.cosets.representatives 1 =
        (⟨N25.normalCertificate.rows 15⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N25.normalCertificate _
  · change N22.cosets.representatives 2 ∈ N24.kernel
    have he : N22.cosets.representatives 2 =
        (⟨N24.normalCertificate.rows 12⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N24.normalCertificate _
  · change N22.cosets.representatives 3 ∈ N23.kernel
    have he : N22.cosets.representatives 3 =
        (⟨N23.normalCertificate.rows 30⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N23.normalCertificate _

private theorem child22_card : ∀ j : Fin 3,
    Nat.card (states (childIndex22 j)).kernel = Nat.card N22.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N25.kernel = Nat.card N22.kernel * 2
    norm_num [N25.kernel_card, N22.kernel_card]
  · change Nat.card N24.kernel = Nat.card N22.kernel * 2
    norm_num [N24.kernel_card, N22.kernel_card]
  · change Nat.card N23.kernel = Nat.card N22.kernel * 2
    norm_num [N23.kernel_card, N22.kernel_card]

private def children22 : BinaryNormalChildren generators_full (states 22) states where
  count := 3
  rows := childRows22
  covers := by
    rintro ⟨z⟩ hz
    exact covers22 z hz
  child := childIndex22
  generator_mem := child22_generators
  lift_mem := child22_lift
  child_card := child22_card

private def childRows23 (j : Fin 1) : N23.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex23 (j : Fin 1) : Fin 27 := (26 : Fin 27)

private theorem covers23 : ∀ z : Fin 2,
    N23.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows23 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child23_generators : ∀ j : Fin 1, ∀ k,
    N23.normalGenerators k ∈ (states (childIndex23 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N23.normalGenerators k ∈ N26.kernel
    intro k
    have he : ∀ k : Fin 2, N23.normalGenerators k =
        (⟨N26.normalCertificate.rows (((if k.val < 1 then 7 else 46) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child23_lift : ∀ j : Fin 1,
    N23.cosets.representatives (childRows23 j).index ∈
      (states (childIndex23 j)).kernel := by
  intro j
  fin_cases j
  · change N23.cosets.representatives 1 ∈ N26.kernel
    have he : N23.cosets.representatives 1 =
        (⟨N26.normalCertificate.rows 31⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child23_card : ∀ j : Fin 1,
    Nat.card (states (childIndex23 j)).kernel = Nat.card N23.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N26.kernel = Nat.card N23.kernel * 2
    norm_num [N26.kernel_card, N23.kernel_card]

private def children23 : BinaryNormalChildren generators_full (states 23) states where
  count := 1
  rows := childRows23
  covers := by
    rintro ⟨z⟩ hz
    exact covers23 z hz
  child := childIndex23
  generator_mem := child23_generators
  lift_mem := child23_lift
  child_card := child23_card

private def childRows24 (j : Fin 1) : N24.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex24 (j : Fin 1) : Fin 27 := (26 : Fin 27)

private theorem covers24 : ∀ z : Fin 2,
    N24.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows24 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child24_generators : ∀ j : Fin 1, ∀ k,
    N24.normalGenerators k ∈ (states (childIndex24 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N24.normalGenerators k ∈ N26.kernel
    intro k
    have he : ∀ k : Fin 3, N24.normalGenerators k =
        (⟨N26.normalCertificate.rows (((if k.val < 1 then 7 else (if k.val < 2 then 43 else 30)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child24_lift : ∀ j : Fin 1,
    N24.cosets.representatives (childRows24 j).index ∈
      (states (childIndex24 j)).kernel := by
  intro j
  fin_cases j
  · change N24.cosets.representatives 1 ∈ N26.kernel
    have he : N24.cosets.representatives 1 =
        (⟨N26.normalCertificate.rows 31⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child24_card : ∀ j : Fin 1,
    Nat.card (states (childIndex24 j)).kernel = Nat.card N24.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N26.kernel = Nat.card N24.kernel * 2
    norm_num [N26.kernel_card, N24.kernel_card]

private def children24 : BinaryNormalChildren generators_full (states 24) states where
  count := 1
  rows := childRows24
  covers := by
    rintro ⟨z⟩ hz
    exact covers24 z hz
  child := childIndex24
  generator_mem := child24_generators
  lift_mem := child24_lift
  child_card := child24_card

private def childRows25 (j : Fin 1) : N25.state.Row := ⟨(1 : Fin 2)⟩
private def childIndex25 (j : Fin 1) : Fin 27 := (26 : Fin 27)

private theorem covers25 : ∀ z : Fin 2,
    N25.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 1, childRows25 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child25_generators : ∀ j : Fin 1, ∀ k,
    N25.normalGenerators k ∈ (states (childIndex25 j)).kernel := by
  intro j
  fin_cases j
  · change ∀ k, N25.normalGenerators k ∈ N26.kernel
    intro k
    have he : ∀ k : Fin 3, N25.normalGenerators k =
        (⟨N26.normalCertificate.rows (((if k.val < 1 then 7 else (if k.val < 2 then 27 else 30)) : Fin 64))⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child25_lift : ∀ j : Fin 1,
    N25.cosets.representatives (childRows25 j).index ∈
      (states (childIndex25 j)).kernel := by
  intro j
  fin_cases j
  · change N25.cosets.representatives 1 ∈ N26.kernel
    have he : N25.cosets.representatives 1 =
        (⟨N26.normalCertificate.rows 25⟩ : Source) := by decide +kernel
    rw [he]
    exact binaryNormalRow_mem N26.normalCertificate _

private theorem child25_card : ∀ j : Fin 1,
    Nat.card (states (childIndex25 j)).kernel = Nat.card N25.kernel * 2 := by
  intro j
  fin_cases j
  · change Nat.card N26.kernel = Nat.card N25.kernel * 2
    norm_num [N26.kernel_card, N25.kernel_card]

private def children25 : BinaryNormalChildren generators_full (states 25) states where
  count := 1
  rows := childRows25
  covers := by
    rintro ⟨z⟩ hz
    exact covers25 z hz
  child := childIndex25
  generator_mem := child25_generators
  lift_mem := child25_lift
  child_card := child25_card

private def childRows26 (j : Fin 0) : N26.state.Row := Fin.elim0 j
private def childIndex26 (j : Fin 0) : Fin 27 := Fin.elim0 j

private theorem covers26 : ∀ z : Fin 1,
    N26.state.centralRowTests generators_full ⟨z⟩ →
      ∃ j : Fin 0, childRows26 j = ⟨z⟩ := by
  unfold BinaryNormalState.centralRowTests
  exact (by decide +kernel)

private theorem child26_generators : ∀ j : Fin 0, ∀ k,
    N26.normalGenerators k ∈ (states (childIndex26 j)).kernel := by
  intro j
  exact Fin.elim0 j

private theorem child26_lift : ∀ j : Fin 0,
    N26.cosets.representatives (childRows26 j).index ∈
      (states (childIndex26 j)).kernel := by
  intro j
  exact Fin.elim0 j

private theorem child26_card : ∀ j : Fin 0,
    Nat.card (states (childIndex26 j)).kernel = Nat.card N26.kernel * 2 := by
  intro j
  exact Fin.elim0 j

private def children26 : BinaryNormalChildren generators_full (states 26) states where
  count := 0
  rows := childRows26
  covers := by
    rintro ⟨z⟩ hz
    exact covers26 z hz
  child := childIndex26
  generator_mem := child26_generators
  lift_mem := child26_lift
  child_card := child26_card

private def children : (i : Fin 27) →
    BinaryNormalChildren generators_full (states i) states :=
  (Fin.cases children0 (Fin.cases children1 (Fin.cases children2 (Fin.cases children3 (Fin.cases children4 (Fin.cases children5 (Fin.cases children6 (Fin.cases children7 (Fin.cases children8 (Fin.cases children9 (Fin.cases children10 (Fin.cases children11 (Fin.cases children12 (Fin.cases children13 (Fin.cases children14 (Fin.cases children15 (Fin.cases children16 (Fin.cases children17 (Fin.cases children18 (Fin.cases children19 (Fin.cases children20 (Fin.cases children21 (Fin.cases children22 (Fin.cases children23 (Fin.cases children24 (Fin.cases children25 (Fin.cases children26 (fun i => Fin.elim0 i))))))))))))))))))))))))))))

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

/-- Completeness for the same literal original permutation action. -/
theorem complete_original
    (N : Subgroup (Subgroup.closure (Set.range BinaryMenuCayley8T26.generators))) [N.Normal] :
    ∃ i, (states i).kernel.map BinaryMenuCayley8T26.originalEquiv.toMonoidHom = N :=
  registry.complete_map_of_equiv source_isPGroup BinaryMenuCayley8T26.originalEquiv N

end SymmetricSubgroupAsymptotics.BinaryCarrierNormal8T26
