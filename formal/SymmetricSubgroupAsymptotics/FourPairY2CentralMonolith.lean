import SymmetricSubgroupAsymptotics.FourPairY2GraphPilot
import SymmetricSubgroupAsymptotics.BinaryPairFrameGenerators
import SymmetricSubgroupAsymptotics.BinaryPairFrameFourCentralQuotient
import SymmetricSubgroupAsymptotics.Non2PreE7NaturalS4Group

/-! Actual first-stage monolith of the selected Y2 source.
All selected facts are point equations on the original eight-point
permutations. The final catalogue recognition and lower Xc interval are
separate; this file does not assert the four-pair classification. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FourPairY2CentralMonolith
open FourPairY2GraphPilot

/-- Consecutive original points are the literal physical pairs. -/
def pointFrame : Fin 4 × ZMod 2 ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 4)) (ZMod.finEquiv 2).symm.toEquiv).trans
    finProdFinEquiv

def topCycle : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2

def generatorTops : Fin 6 → Equiv.Perm (Fin 4) :=
  ![1, 1, 1, 1, topCycle, NaturalS4.c1]

private theorem generator_frame_checked : ∀ (j : Fin 6) (i : Fin 4) (b : ZMod 2),
    (pointFrame.symm (sourceGenerators j (pointFrame (i,b)))).1 = generatorTops j i := by
  decide +kernel

def pairFrame : BinaryPairFrame Original (Fin 4) :=
  BinaryPairFrame.ofGenerators pointFrame sourceGenerators generatorTops
    (fun j x => generator_frame_checked j x.1 x.2)

def originalGenerator (j : Fin 6) : Original :=
  ⟨sourceGenerators j, Subgroup.subset_closure (Set.mem_range_self j)⟩

private theorem top_generator (j : Fin 6) :
    pairFrame.top (originalGenerator j) = generatorTops j :=
  BinaryPairFrame.ofGenerators_top_generator pointFrame sourceGenerators generatorTops
    (fun j x => generator_frame_checked j x.1 x.2) j

/-- P is normal in the actual pair-top range, not an assumed abstract A4. -/
def actualKlein : Subgroup pairFrame.top.range :=
  NaturalS4.klein.comap pairFrame.top.range.subtype

instance actualKlein_normal : actualKlein.Normal :=
  Subgroup.Normal.comap NaturalS4.klein_normal pairFrame.top.range.subtype

theorem actualKlein_binary : IsPGroup 2 actualKlein := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change ((g : pairFrame.top.range) : Equiv.Perm (Fin 4)) ^ 2 = 1
  exact NaturalS4.kleinSet_sq _ g.property

private theorem top_conjugate :
    pairFrame.top ((originalGenerator 4)⁻¹ * originalGenerator 5 * originalGenerator 4) =
      NaturalS4.c2 := by
  simp only [map_mul, map_inv, top_generator]
  apply Equiv.ext
  intro i
  revert i
  decide +kernel

def kleinU : actualKlein :=
  ⟨pairFrame.top.rangeRestrict (originalGenerator 5), by
    change pairFrame.top (originalGenerator 5) ∈ NaturalS4.klein
    rw [top_generator]
    decide +kernel⟩

def kleinV : actualKlein :=
  ⟨pairFrame.top.rangeRestrict
    ((originalGenerator 4)⁻¹ * originalGenerator 5 * originalGenerator 4), by
    change pairFrame.top ((originalGenerator 4)⁻¹ * originalGenerator 5 *
      originalGenerator 4) ∈ NaturalS4.klein
    rw [top_conjugate]
    decide +kernel⟩

private theorem kleinU_action : ∀ (x : Fin 4 → ZMod 2) (i : Fin 4),
    pairFrame.coordinateTopAction kleinU x i = x (![1, 0, 3, 2] i) := by
  intro x i
  change x ((pairFrame.top (originalGenerator 5))⁻¹ i) = _
  rw [top_generator]
  have h : ∀ i : Fin 4, (generatorTops 5)⁻¹ i = ![1, 0, 3, 2] i := by
    decide +kernel
  rw [h]

private theorem kleinV_action : ∀ (x : Fin 4 → ZMod 2) (i : Fin 4),
    pairFrame.coordinateTopAction kleinV x i = x (![2, 3, 0, 1] i) := by
  intro x i
  change x ((pairFrame.top ((originalGenerator 4)⁻¹ * originalGenerator 5 *
    originalGenerator 4))⁻¹ i) = _
  rw [top_conjugate]
  have h : ∀ i : Fin 4, NaturalS4.c2⁻¹ i = ![2, 3, 0, 1] i := by
    decide +kernel
  rw [h]

def flipKernel (j : Fin 4) : pairFrame.top.ker :=
  ⟨originalGenerator ⟨j.val, by omega⟩, by
    rw [MonoidHom.mem_ker, top_generator]
    fin_cases j <;> rfl⟩

private theorem flip_bits : ∀ (j i : Fin 4),
    pairFrame.bits (flipKernel j) i = if i = j then 1 else 0 := by
  intro j i
  change (pointFrame.symm (sourceGenerators ⟨j.val, by omega⟩
    (pointFrame (i,0)))).2 = _
  revert j i
  decide +kernel

theorem kernel_bits_separate : ∀ i j : Fin 4, i ≠ j →
    ∃ k : pairFrame.top.ker, pairFrame.bits k i ≠ pairFrame.bits k j := by
  intro i j hne
  refine ⟨flipKernel i, ?_⟩
  rw [flip_bits, if_pos rfl, flip_bits, if_neg hne.symm]
  exact one_ne_zero

/-- The constant flip is the explicit product of the four original flips. -/
def constantWord : Original :=
  originalGenerator 0 * originalGenerator 1 * originalGenerator 2 * originalGenerator 3

def constantKernel : pairFrame.top.ker :=
  ⟨constantWord, by
    change pairFrame.top (originalGenerator 0 * originalGenerator 1 *
      originalGenerator 2 * originalGenerator 3) = 1
    simp only [map_mul, top_generator]
    rfl⟩

private theorem constant_word_checked : ∀ x : Fin 8,
    (sourceGenerators 0 * sourceGenerators 1 * sourceGenerators 2 * sourceGenerators 3) x =
      centralFlip x := by
  decide +kernel

theorem constantWord_permutation : (constantWord : Equiv.Perm (Fin 8)) = centralFlip :=
  Equiv.ext constant_word_checked

private theorem constant_bits : ∀ i : Fin 4, pairFrame.bits constantKernel i = 1 := by
  intro i
  change (pointFrame.symm ((sourceGenerators 0 * sourceGenerators 1 *
    sourceGenerators 2 * sourceGenerators 3) (pointFrame (i,0)))).2 = 1
  revert i
  decide +kernel

/-- The graph kernel's exact literal test now has the original group value. -/
theorem projection_kernel_test (g : Original) :
    projection g = 1 ↔ g = 1 ∨ g = (constantKernel : Original) := by
  change g ∈ projection.ker ↔ _
  rw [kernel_mem_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · right
      apply Subtype.ext
      exact h.trans constantWord_permutation.symm
  · rintro (h | h)
    · exact Or.inl h
    · right
      exact (congrArg Subtype.val h).trans constantWord_permutation

/-- Both first-stage retained-chain obligations, with no project assumption
about the original normal subgroups. Lower Xc compression remains separate. -/
theorem firstStage : projection.ker ≠ ⊥ ∧
    ∀ N : Subgroup Original, N.Normal → N ≠ ⊥ → projection.ker ≤ N :=
  pairFrame.centralQuotient_normalCover actualKlein actualKlein_binary kleinU kleinV
    kleinU_action kleinV_action constantKernel constant_bits kernel_bits_separate
    projection projection_kernel_test

end SymmetricSubgroupAsymptotics.FourPairY2CentralMonolith

end
