import SymmetricSubgroupAsymptotics.BinaryThreeQuartetPairedOrbitSocles

/-! Four further exact signed paired-Singer clients. Row253 retains its
actual cyclic block complement; the other three retain their symmetric
block complements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerSocles
open BinaryPlanePermutationAffineEquiv BinaryPlanePermutationWreathCoordinates
open BinaryPlaneWreathIrreducible
open PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateCore
open PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot
open Non2UnipotentPrefixFiniteMenu Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

def row252PointLifts : Fin 5 → PointWreath (R := SymmetricBlocks) :=
  ![⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 1 2)],1⟩,
  ⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 2 * Equiv.swap 1 3)],1⟩,
  ⟨![localPerm (Equiv.swap 1 2 * Equiv.swap 1 3),localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 0 1)],1⟩,
  ⟨![localPerm (Equiv.swap 0 2 * Equiv.swap 1 3),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1)],(Equiv.swap 0 2 * Equiv.swap 0 1)⟩,
  ⟨![localPerm (Equiv.swap 0 1 * Equiv.swap 0 2 * Equiv.swap 0 3),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1),localPerm 1],(Equiv.swap 0 1)⟩]
def row252Lifts : Fin 5 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (row252PointLifts i)

theorem row252_bindings (i : Fin 5) :
    BinaryThreeQuartetLiteralSocles.action (row252Lifts i) = row252Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row252Z : LinearWreath (R := SymmetricBlocks) := (row252Lifts 2).right
def row252G : LinearWreath (R := SymmetricBlocks) := (row252Lifts 3).right
def row252Word := BinaryThreeQuartetPairedOrbitSocles.words row252Z row252G

theorem row252_projection (i : Fin 3) (v : Fin 3 → V) :
    v * action (row252Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i)) v *
      action ((row252Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i))^2) v =
      Pi.mulSingle i (v i) := by
  funext j
  revert i v j
  decide +kernel

theorem row252_local_orbit (i : Fin 3) (u v : V) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ n : Fin 3, action ((row252Word i)^n.val) (Pi.mulSingle i u) = Pi.mulSingle i v := by
  have h : ∃ n : Fin 3, ∀ (j : Fin 3) (t : Fin 2),
      ((action ((row252Word i)^n.val) (Pi.mulSingle i u)) j).toAdd t =
        ((Pi.mulSingle i v : Fin 3 → V) j).toAdd t := by
    revert i u v hu hv
    decide +kernel
  obtain ⟨n,hn⟩ := h
  refine ⟨n,?_⟩
  funext j
  apply Multiplicative.toAdd.injective
  exact funext (hn j)

def row253PointLifts : Fin 5 → PointWreath (R := CyclicBlocks) :=
  ![⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 1 2)],1⟩,
  ⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 2 * Equiv.swap 1 3)],1⟩,
  ⟨![localPerm (Equiv.swap 0 2 * Equiv.swap 0 3),localPerm 1,localPerm (Equiv.swap 0 2 * Equiv.swap 0 1)],1⟩,
  ⟨![localPerm (Equiv.swap 2 3),localPerm (Equiv.swap 0 3),localPerm (Equiv.swap 0 1)],1⟩,
  ⟨![localPerm (Equiv.swap 0 2 * Equiv.swap 1 3),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1)],cyclicRotation⟩]
def row253Lifts : Fin 5 → BinaryThreeQuartetLiteralSocles.Model (R := CyclicBlocks) :=
  fun i => coordinates (row253PointLifts i)

theorem row253_bindings (i : Fin 5) :
    BinaryThreeQuartetLiteralSocles.action (row253Lifts i) = row253Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row253Z : LinearWreath (R := CyclicBlocks) := (row253Lifts 2).right
def row253G : LinearWreath (R := CyclicBlocks) := (row253Lifts 4).right
def row253Word := BinaryThreeQuartetPairedOrbitSocles.words row253Z row253G

theorem row253_projection (i : Fin 3) (v : Fin 3 → V) :
    v * action (row253Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i)) v *
      action ((row253Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i))^2) v =
      Pi.mulSingle i (v i) := by
  funext j
  revert i v j
  decide +kernel

theorem row253_local_orbit (i : Fin 3) (u v : V) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ n : Fin 3, action ((row253Word i)^n.val) (Pi.mulSingle i u) = Pi.mulSingle i v := by
  have h : ∃ n : Fin 3, ∀ (j : Fin 3) (t : Fin 2),
      ((action ((row253Word i)^n.val) (Pi.mulSingle i u)) j).toAdd t =
        ((Pi.mulSingle i v : Fin 3 → V) j).toAdd t := by
    revert i u v hu hv
    decide +kernel
  obtain ⟨n,hn⟩ := h
  refine ⟨n,?_⟩
  funext j
  apply Multiplicative.toAdd.injective
  exact funext (hn j)

def row254PointLifts : Fin 5 → PointWreath (R := SymmetricBlocks) :=
  ![⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 1 2)],1⟩,
  ⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 2 * Equiv.swap 1 3)],1⟩,
  ⟨![localPerm (Equiv.swap 1 2 * Equiv.swap 1 3),localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 0 1)],1⟩,
  ⟨![localPerm (Equiv.swap 0 1 * Equiv.swap 0 3 * Equiv.swap 0 2),localPerm (Equiv.swap 2 3),localPerm (Equiv.swap 0 2 * Equiv.swap 0 3 * Equiv.swap 0 1)],(Equiv.swap 0 2)⟩,
  ⟨![localPerm (Equiv.swap 0 1 * Equiv.swap 0 2),localPerm (Equiv.swap 0 2 * Equiv.swap 0 1),localPerm (Equiv.swap 1 2)],(Equiv.swap 0 1)⟩]
def row254Lifts : Fin 5 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (row254PointLifts i)

theorem row254_bindings (i : Fin 5) :
    BinaryThreeQuartetLiteralSocles.action (row254Lifts i) = row254Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row254Z : LinearWreath (R := SymmetricBlocks) := (row254Lifts 2).right
def row254G : LinearWreath (R := SymmetricBlocks) := (row254Lifts 3).right * (row254Lifts 4).right
def row254Word := BinaryThreeQuartetPairedOrbitSocles.words row254Z row254G

theorem row254_projection (i : Fin 3) (v : Fin 3 → V) :
    v * action (row254Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i)) v *
      action ((row254Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i))^2) v =
      Pi.mulSingle i (v i) := by
  funext j
  revert i v j
  decide +kernel

theorem row254_local_orbit (i : Fin 3) (u v : V) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ n : Fin 3, action ((row254Word i)^n.val) (Pi.mulSingle i u) = Pi.mulSingle i v := by
  have h : ∃ n : Fin 3, ∀ (j : Fin 3) (t : Fin 2),
      ((action ((row254Word i)^n.val) (Pi.mulSingle i u)) j).toAdd t =
        ((Pi.mulSingle i v : Fin 3 → V) j).toAdd t := by
    revert i u v hu hv
    decide +kernel
  obtain ⟨n,hn⟩ := h
  refine ⟨n,?_⟩
  funext j
  apply Multiplicative.toAdd.injective
  exact funext (hn j)

def row268PointLifts : Fin 6 → PointWreath (R := SymmetricBlocks) :=
  ![⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 3 * Equiv.swap 1 2)],1⟩,
  ⟨![localPerm 1,localPerm 1,localPerm (Equiv.swap 0 2 * Equiv.swap 1 3)],1⟩,
  ⟨![localPerm (Equiv.swap 0 2 * Equiv.swap 0 3),localPerm 1,localPerm (Equiv.swap 0 2 * Equiv.swap 0 1)],1⟩,
  ⟨![localPerm (Equiv.swap 2 3),localPerm (Equiv.swap 0 3),localPerm (Equiv.swap 0 1)],1⟩,
  ⟨![localPerm (Equiv.swap 0 2 * Equiv.swap 1 3),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1)],(Equiv.swap 0 2 * Equiv.swap 0 1)⟩,
  ⟨![localPerm (Equiv.swap 0 1 * Equiv.swap 0 2 * Equiv.swap 0 3),localPerm (Equiv.swap 0 3 * Equiv.swap 0 2 * Equiv.swap 0 1),localPerm 1],(Equiv.swap 0 1)⟩]
def row268Lifts : Fin 6 → BinaryThreeQuartetLiteralSocles.Model (R := SymmetricBlocks) :=
  fun i => coordinates (row268PointLifts i)

theorem row268_bindings (i : Fin 6) :
    BinaryThreeQuartetLiteralSocles.action (row268Lifts i) = row268Generators i := by
  apply Equiv.ext; intro x; revert i x; decide +kernel

def row268Z : LinearWreath (R := SymmetricBlocks) := (row268Lifts 2).right
def row268G : LinearWreath (R := SymmetricBlocks) := (row268Lifts 4).right
def row268Word := BinaryThreeQuartetPairedOrbitSocles.words row268Z row268G

theorem row268_projection (i : Fin 3) (v : Fin 3 → V) :
    v * action (row268Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i)) v *
      action ((row268Word (PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex i))^2) v =
      Pi.mulSingle i (v i) := by
  funext j
  revert i v j
  decide +kernel

theorem row268_local_orbit (i : Fin 3) (u v : V) (hu : u ≠ 1) (hv : v ≠ 1) :
    ∃ n : Fin 3, action ((row268Word i)^n.val) (Pi.mulSingle i u) = Pi.mulSingle i v := by
  have h : ∃ n : Fin 3, ∀ (j : Fin 3) (t : Fin 2),
      ((action ((row268Word i)^n.val) (Pi.mulSingle i u)) j).toAdd t =
        ((Pi.mulSingle i v : Fin 3 → V) j).toAdd t := by
    revert i u v hu hv
    decide +kernel
  obtain ⟨n,hn⟩ := h
  refine ⟨n,?_⟩
  funext j
  apply Multiplicative.toAdd.injective
  exact funext (hn j)

theorem row252_word_mem (i : Fin 3) : row252Word i ∈
    Subgroup.closure (Set.range (fun j => (row252Lifts j).right)) := by
  apply BinaryThreeQuartetPairedOrbitSocles.words_mem
  · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 5))
  · exact Subgroup.subset_closure (Set.mem_range_self (3 : Fin 5))

theorem row252_full :
    Subgroup.closure (Set.range (fun i => (row252Lifts i).right.right)) = ⊤ := by
  exact symmetric_full (fun i => (row252Lifts i).right.right) 3 4
    (by apply Equiv.ext; intro j; revert j; decide +kernel)
    (by apply Equiv.ext; intro j; revert j; decide +kernel)

theorem row252AtThree_quotientSocle (N : Subgroup Row252Top) [N.Normal] :
    SocleNormalGeneratorBound (Row252Top ⧸ N) 3 :=
  BinaryThreeQuartetPairedOrbitSocles.quotientSocle
    row252Lifts row252Generators row252_bindings row252_full
    row252Word row252_word_mem PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex
    row252_projection row252_local_orbit symmetric_transitive
    symmetricRotation 0 symmetric_cycle symmetric_normalGen N

def row252AtThree_family : row252Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row252Interface.normalRegistry (fun N => by letI := N.2; exact row252AtThree_quotientSocle N.1)

theorem row253_word_mem (i : Fin 3) : row253Word i ∈
    Subgroup.closure (Set.range (fun j => (row253Lifts j).right)) := by
  apply BinaryThreeQuartetPairedOrbitSocles.words_mem
  · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 5))
  · exact Subgroup.subset_closure (Set.mem_range_self (4 : Fin 5))

theorem row253_full :
    Subgroup.closure (Set.range (fun i => (row253Lifts i).right.right)) = ⊤ := by
  exact cyclic_full (fun i => (row253Lifts i).right.right) 4 rfl

theorem row253AtThree_quotientSocle (N : Subgroup Row253Top) [N.Normal] :
    SocleNormalGeneratorBound (Row253Top ⧸ N) 3 :=
  BinaryThreeQuartetPairedOrbitSocles.quotientSocle
    row253Lifts row253Generators row253_bindings row253_full
    row253Word row253_word_mem PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex
    row253_projection row253_local_orbit PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.blocks_transitive
    cyclicRotation 0 PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.blocks_cycle PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.blocks_normalGen N

def row253AtThree_family : row253Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row253Interface.normalRegistry (fun N => by letI := N.2; exact row253AtThree_quotientSocle N.1)

theorem row254_word_mem (i : Fin 3) : row254Word i ∈
    Subgroup.closure (Set.range (fun j => (row254Lifts j).right)) := by
  apply BinaryThreeQuartetPairedOrbitSocles.words_mem
  · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 5))
  · exact (Subgroup.closure (Set.range (fun j => (row254Lifts j).right))).mul_mem
      (Subgroup.subset_closure (Set.mem_range_self (3 : Fin 5)))
      (Subgroup.subset_closure (Set.mem_range_self (4 : Fin 5)))

theorem row254_full :
    Subgroup.closure (Set.range (fun i => (row254Lifts i).right.right)) = ⊤ := by
  let b := fun i => (row254Lifts i).right.right
  let B := Subgroup.closure (Set.range b)
  have hr : symmetricRotation ∈ B := by
    have he : b 3 * b 4 = symmetricRotation := by
      apply Equiv.ext; intro j; revert j; decide +kernel
    rw [← he]
    exact B.mul_mem (Subgroup.subset_closure (Set.mem_range_self (3 : Fin 5)))
      (Subgroup.subset_closure (Set.mem_range_self (4 : Fin 5)))
  have hs : symmetricReflection ∈ B := by
    have he : b 4 = symmetricReflection := by
      apply Equiv.ext; intro j; revert j; decide +kernel
    rw [← he]
    exact Subgroup.subset_closure (Set.mem_range_self (4 : Fin 5))
  have ht : Subgroup.closure (Set.range (![symmetricRotation,symmetricReflection] : Fin 2 → SymmetricBlocks)) = ⊤ :=
    symmetric_full _ 0 1 rfl rfl
  apply top_unique
  rw [← ht]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact hr
  · exact hs

theorem row254AtThree_quotientSocle (N : Subgroup Row254Top) [N.Normal] :
    SocleNormalGeneratorBound (Row254Top ⧸ N) 3 :=
  BinaryThreeQuartetPairedOrbitSocles.quotientSocle
    row254Lifts row254Generators row254_bindings row254_full
    row254Word row254_word_mem PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex
    row254_projection row254_local_orbit symmetric_transitive
    symmetricRotation 0 symmetric_cycle symmetric_normalGen N

def row254AtThree_family : row254Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row254Interface.normalRegistry (fun N => by letI := N.2; exact row254AtThree_quotientSocle N.1)

theorem row268_word_mem (i : Fin 3) : row268Word i ∈
    Subgroup.closure (Set.range (fun j => (row268Lifts j).right)) := by
  apply BinaryThreeQuartetPairedOrbitSocles.words_mem
  · exact Subgroup.subset_closure (Set.mem_range_self (2 : Fin 6))
  · exact Subgroup.subset_closure (Set.mem_range_self (4 : Fin 6))

theorem row268_full :
    Subgroup.closure (Set.range (fun i => (row268Lifts i).right.right)) = ⊤ := by
  exact symmetric_full (fun i => (row268Lifts i).right.right) 4 5
    (by apply Equiv.ext; intro j; revert j; decide +kernel)
    (by apply Equiv.ext; intro j; revert j; decide +kernel)

theorem row268AtThree_quotientSocle (N : Subgroup Row268Top) [N.Normal] :
    SocleNormalGeneratorBound (Row268Top ⧸ N) 3 :=
  BinaryThreeQuartetPairedOrbitSocles.quotientSocle
    row268Lifts row268Generators row268_bindings row268_full
    row268Word row268_word_mem PrimitiveAffineDegreeTwoTwelvePairedSingerPilot.projectionIndex
    row268_projection row268_local_orbit symmetric_transitive
    symmetricRotation 0 symmetric_cycle symmetric_normalGen N

def row268AtThree_family : row268Interface.normalRegistry.QuotientSocleGeneratorFamily 3 :=
  FiniteNormalStateRegistry.QuotientSocleGeneratorFamily.ofQuotientBounds
    row268Interface.normalRegistry (fun N => by letI := N.2; exact row268AtThree_quotientSocle N.1)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairedSingerSocles

end
