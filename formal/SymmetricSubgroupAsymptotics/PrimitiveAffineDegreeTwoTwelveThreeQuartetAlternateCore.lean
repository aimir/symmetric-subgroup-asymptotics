import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.FiniteNormalChainGenerators

/-! Shared literal wreath elements and Singer words for the ten
three-quartet actions. The cyclic and symmetric block complements are
treated through their actual displayed generators. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateCore

open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlanePermutationWreathCoordinates
open PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot

def u : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 3
def v : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
def w : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

variable {R : Type} [Group R] [MulAction R (Fin 3)]

abbrev PointWreath := BinaryPlanePermutationWreathCoordinates.W (R := R) (I := Fin 3)
abbrev LinearWreath := BinaryPlaneWreathIrreducible.W (R := R) (I := Fin 3)

def localU : PointWreath (R := R) := ⟨Pi.mulSingle 2 (localPerm u),1⟩
def localV : PointWreath (R := R) := ⟨Pi.mulSingle 2 (localPerm v),1⟩
def localFour : PointWreath (R := R) := ⟨Pi.mulSingle 2 (localPerm (finRotate 4)),1⟩
def localSwap : PointWreath (R := R) := ⟨Pi.mulSingle 2 (localPerm (Equiv.swap 1 2)),1⟩
def rotateWreath (r : R) : PointWreath (R := R) :=
  ⟨![localPerm ((finRotate 4)^2),localPerm (finRotate 4),localPerm (finRotate 4)],r⟩
def twistFull : PointWreath (R := R) :=
  ⟨![localPerm (Equiv.swap 1 2),localPerm (Equiv.swap 2 3),localPerm (Equiv.swap 0 3)],1⟩
def twistPair : PointWreath (R := R) :=
  ⟨![localPerm (Equiv.swap 1 2),1,localPerm (Equiv.swap 0 3)],1⟩
def twistReverse : PointWreath (R := R) :=
  ⟨![localPerm (Equiv.swap 0 3),1,localPerm (Equiv.swap 1 2)],1⟩
def reflectA (s : R) : PointWreath (R := R) :=
  ⟨![localPerm ((finRotate 4)⁻¹),localPerm (finRotate 4),1],s⟩
def reflectB (s : R) : PointWreath (R := R) :=
  ⟨![localPerm (u⁻¹),localPerm u,localPerm (Equiv.swap 0 3)],s⟩
def reflectC (s : R) : PointWreath (R := R) :=
  ⟨![localPerm (w⁻¹),localPerm w,localPerm (Equiv.swap 1 2)],s⟩

def coreSinger : LinearWreath (R := R) := (coordinates (localU (R := R))).right
def coreRotation (r : R) : LinearWreath (R := R) := (coordinates (rotateWreath r)).right
def words (z g : LinearWreath (R := R)) : Fin 3 → LinearWreath (R := R) :=
  ![g*z*g⁻¹,g^2*z⁻¹*(g^2)⁻¹,z]

theorem local_of_words (C : Subgroup (LinearWreath (R := R)))
    (z g : LinearWreath (R := R)) (hz : z ∈ C) (hg : g ∈ C)
    (hw : ∀ i : Fin 3, words z g i = localEmbedding i singer) :
    ∀ i : Fin 3, localEmbedding i singer ∈ C := by
  intro i
  rw [← hw i]
  fin_cases i
  · exact C.mul_mem (C.mul_mem hg hz) (C.inv_mem hg)
  · exact C.mul_mem (C.mul_mem (C.pow_mem hg 2) (C.inv_mem hz))
      (C.inv_mem (C.pow_mem hg 2))
  · exact hz

abbrev CyclicBlocks := PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.Blocks
abbrev cyclicRotation := PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternatePilot.rotation
abbrev SymmetricBlocks := Equiv.Perm (Fin 3)
def symmetricRotation : SymmetricBlocks := finRotate 3
def symmetricReflection : SymmetricBlocks := Equiv.swap 0 1

theorem cyclic_words (i : Fin 3) :
    words (coreSinger (R := CyclicBlocks)) (coreRotation cyclicRotation) i =
      localEmbedding i singer := by
  apply PermutationalWreathProduct.ext
  · funext j
    apply LinearEquiv.ext
    intro t
    revert i j t
    decide +kernel
  · apply Subtype.ext
    apply Equiv.ext
    intro j
    revert i j
    decide +kernel

theorem symmetric_words (i : Fin 3) :
    words (coreSinger (R := SymmetricBlocks)) (coreRotation symmetricRotation) i =
      localEmbedding i singer := by
  apply PermutationalWreathProduct.ext
  · funext j
    apply LinearEquiv.ext
    intro t
    revert i j t
    decide +kernel
  · apply Equiv.ext
    intro j
    revert i j
    decide +kernel

theorem symmetric_four_swap :
    (coordinates (localFour (R := SymmetricBlocks))).right *
      (coordinates (localSwap (R := SymmetricBlocks))).right = coreSinger := by
  apply PermutationalWreathProduct.ext
  · funext j
    apply LinearEquiv.ext
    intro t
    revert j t
    decide +kernel
  · apply Equiv.ext
    intro j
    revert j
    decide +kernel

theorem cyclic_full {n : ℕ} (b : Fin n → CyclicBlocks)
    (j : Fin n) (hj : b j = cyclicRotation) : Subgroup.closure (Set.range b) = ⊤ := by
  let B := Subgroup.closure (Set.range b)
  have hr : cyclicRotation ∈ B := hj ▸ Subgroup.subset_closure (Set.mem_range_self j)
  apply top_unique
  intro r _
  obtain ⟨z,hz⟩ := Subgroup.mem_zpowers_iff.mp r.property
  have he : cyclicRotation^z = r := Subtype.ext hz
  rw [← he]
  exact B.zpow_mem hr z

theorem symmetric_full {n : ℕ} (b : Fin n → SymmetricBlocks)
    (j k : Fin n) (hj : b j = symmetricRotation) (hk : b k = symmetricReflection) :
    Subgroup.closure (Set.range b) = ⊤ := by
  have hgen : Subgroup.closure
      ({finRotate 3,Equiv.swap (0 : Fin 3) 1} : Set SymmetricBlocks) = ⊤ := by
    simpa only [show finRotate 3 (0 : Fin 3) = 1 from rfl] using
      Equiv.Perm.closure_cycle_adjacent_swap
        (isCycle_finRotate_of_le (by decide : 2 ≤ 3))
        (support_finRotate_of_le (by decide : 2 ≤ 3)) (0 : Fin 3)
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · change symmetricRotation ∈ Subgroup.closure (Set.range b)
    rw [← hj]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  · change symmetricReflection ∈ Subgroup.closure (Set.range b)
    rw [← hk]
    exact Subgroup.subset_closure (Set.mem_range_self k)

theorem symmetric_transitive (i j : Fin 3) : ∃ g : SymmetricBlocks, g • i = j :=
  ⟨Equiv.swap i j,Equiv.swap_apply_left i j⟩

theorem symmetric_cycle (j : Fin 3) :
    ∃ m : ℕ, symmetricRotation^m • (0 : Fin 3) = j :=
  ⟨j.val,(by decide +kernel : ∀ j : Fin 3, ((finRotate 3)^j.val) 0 = j) j⟩

theorem symmetric_normalGen (N : Subgroup SymmetricBlocks) (hN : N.Normal) :
    MarkedC4.normalGen N ≤ 1 := by
  obtain ⟨x,hx⟩ := normal_generating_singletons_of_finite_normal_total
    NaturalFourNormalChains.symmetric_three_normal_total N hN
  exact normalGen_le_of_fin_tuple x hx

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveThreeQuartetAlternateCore

end
