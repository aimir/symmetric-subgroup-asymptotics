import SymmetricSubgroupAsymptotics.BinarySixPointFiveCyclePolynomial
import SymmetricSubgroupAsymptotics.BinaryPairEvenKernelGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows251To301

/-! Four original capacity-one fields share a six-point five-cycle
operator and the even-pair kernel theorem. All anchors, transports and
odd offsets below are words in the original literal generators. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveFiveCyclePairNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue

abbrev pointChart := PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily.pointChart

def pairCycleA : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 3, 4, 0, 5]
  invFun := ![4, 0, 1, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairCycleB : Equiv.Perm (Fin 6) where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairMoverA : Equiv.Perm (Fin 6) where
  toFun := ![5, 4, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairMoverB : Equiv.Perm (Fin 6) where
  toFun := ![5, 2, 1, 4, 3, 0]
  invFun := ![5, 2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairThreeCycle : Equiv.Perm (Fin 6) where
  toFun := ![1, 2, 0, 3, 4, 5]
  invFun := ![2, 0, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def pairSwap : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

/-- Prefixes of adjacent flips telescope to the differences from pair zero. -/
def chain {G : Type} [Group G] (e a : G) : Fin 5 → G :=
  ![1, e, e * (a * e * a⁻¹),
    e * (a * e * a⁻¹) * (a ^ 2 * e * (a ^ 2)⁻¹),
    e * (a * e * a⁻¹) * (a ^ 2 * e * (a ^ 2)⁻¹) *
      (a ^ 3 * e * (a ^ 3)⁻¹)]

def anchorA {G : Type} [Group G] (e a b : G) (q : Fin 5) : Fin 6 → G :=
  ![chain e a 0, chain e a 1, chain e a 2, chain e a 3, chain e a 4,
    chain e a q * (b * e * b⁻¹)]

def transportA {G : Type} [Group G] (a b : G) : Fin 6 → G :=
  ![1, a, a ^ 2, a ^ 3, a ^ 4, b]

def anchorB {G : Type} [Group G] (k a : G) : Fin 6 → G :=
  ![1, k, a * k * a⁻¹, a ^ 2 * k * (a ^ 2)⁻¹,
    a ^ 3 * k * (a ^ 3)⁻¹, a ^ 4 * k * (a ^ 4)⁻¹]

def transportB {G : Type} [Group G] (a b : G) : Fin 6 → G :=
  ![1, b, a * b, a ^ 2 * b, a ^ 3 * b, a ^ 4 * b]

/-- A common literal witness interface: six anchors give every even pair
flip, six transports give transitivity, and one odd offset completes the
kernel sharing. The six-dimensional operator is attached to the actual
range of the original pair action. -/
theorem uniform_of_words {m : ℕ} (j : Fin 2)
    (gs : Fin m → Equiv.Perm (Fin 12)) (tops : Fin m → Equiv.Perm (Fin 6))
    (ai bi : Fin m)
    (anchors transports : Fin 6 → Subgroup.closure (Set.range gs))
    (u : Subgroup.closure (Set.range gs))
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (hmatrix : ∀ i x : Fin 6,
      BinarySixPointFiveCyclePolynomial.actualOperator
        BinarySixPointFiveCyclePolynomial.representation (tops ai) (tops bi)
          (Pi.single i 1) x =
        BinarySixPointFiveCyclePolynomial.operator j (Pi.single i 1) x)
    (hfix : ∀ i x : Fin 6,
      (pointChart.symm ((anchors i : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = x)
    (hbits : ∀ i x : Fin 6,
      (pointChart.symm ((anchors i : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).2 =
        (Pi.single 0 1 + Pi.single i 1 : Fin 6 → ZMod 2) x)
    (htransport : ∀ i : Fin 6,
      (pointChart.symm ((transports i : Equiv.Perm (Fin 12)) (pointChart (0, 0)))).1 = i)
    (hodd : ∑ i : Fin 6,
      (pointChart.symm ((u : Equiv.Perm (Fin 12)) (pointChart (i, 0)))).2 = 1) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (Subgroup.closure (Set.range gs)) (Fin 12)) 1 := by
  let F := BinaryPairFrame.ofGenerators pointChart gs tops hp
  let anchor (i : Fin 6) : F.top.ker := ⟨anchors i, by
    change F.top (anchors i) = 1
    apply Equiv.ext
    intro x
    exact (F.intertwine (anchors i) (x, 0)).symm.trans (hfix i x)⟩
  have hanchor (i : Fin 6) :
      F.bits (anchor i) = Pi.single 0 (1 : ZMod 2) + Pi.single i (1 : ZMod 2) := by
    funext x
    exact hbits i x
  have hflip (i l : Fin 6) : ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2) + Pi.single l (1 : ZMod 2) := by
    refine ⟨anchor i * anchor l, ?_⟩
    have he : F.bits (anchor i * anchor l) = F.bits (anchor i) + F.bits (anchor l) :=
      congrArg Multiplicative.toAdd (F.bitsHom.map_mul (anchor i) (anchor l))
    rw [he, hanchor, hanchor]
    have hz : (Pi.single 0 (1 : ZMod 2) + Pi.single 0 1 : Fin 6 → ZMod 2) = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero ((Pi.single 0 1 : Fin 6 → ZMod 2) x)
    calc
      _ = ((Pi.single 0 (1 : ZMod 2) : Fin 6 → ZMod 2) + Pi.single 0 1) +
          (Pi.single i 1 + Pi.single l 1) := by abel
      _ = _ := by rw [hz, zero_add]
  have hzero (i : Fin 6) : F.top (transports i) 0 = i :=
    (F.intertwine (transports i) (0, 0)).symm.trans (htransport i)
  have htrans (i l : Fin 6) : ∃ g, F.top g i = l := by
    refine ⟨transports l * (transports i)⁻¹, ?_⟩
    rw [map_mul, map_inv]
    change F.top (transports l) ((F.top (transports i))⁻¹ i) = l
    have hi : (F.top (transports i))⁻¹ i = 0 := by
      calc
        _ = (F.top (transports i))⁻¹ (F.top (transports i) 0) :=
          congrArg (fun x ↦ (F.top (transports i))⁻¹ x) (hzero i).symm
        _ = 0 := (F.top (transports i)).symm_apply_apply 0
    rw [hi, hzero]
  apply F.uniform_of_even_pair_kernel_and_odd_offset_coordinateTop
    hflip htrans ⟨u, hodd⟩ 1
  have action_generator (i : Fin m) :
      permutationFunctionRepresentation (ZMod 2) F.top.range (Fin 6)
        (F.top.rangeRestrict (closureGenerators gs i)) =
          BinarySixPointFiveCyclePolynomial.representation (tops i) := by
    apply LinearMap.ext
    intro v
    funext x
    change v ((F.top (closureGenerators gs i))⁻¹ x) = v ((tops i)⁻¹ x)
    have hi : F.top (closureGenerators gs i) = tops i :=
      BinaryPairFrame.ofGenerators_top_generator pointChart gs tops hp i
    rw [hi]
  exact BinarySixPointFiveCyclePolynomial.uniform_of_actions j _
    (F.top.rangeRestrict (closureGenerators gs ai))
    (F.top.rangeRestrict (closureGenerators gs bi)) (tops ai) (tops bi)
      (action_generator ai) (action_generator bi) hmatrix

def row255Tops : Fin 3 → Equiv.Perm (Fin 6) := ![1, pairCycleA, pairMoverA]

def row256Tops : Fin 3 → Equiv.Perm (Fin 6) := ![1, pairCycleA, pairMoverB]

def row270Tops : Fin 3 → Equiv.Perm (Fin 6) := ![1, pairCycleA, pairMoverB]

def row287Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, pairThreeCycle, pairCycleB, pairSwap]

theorem row255Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row255Interface.top (Fin 12)) 1 := by
  let k := closureGenerators row255Generators 0
  let a := closureGenerators row255Generators 1
  let b := closureGenerators row255Generators 2
  apply uniform_of_words 0 row255Generators row255Tops 1 2
    (anchorA (k * (a * k * a⁻¹)) a b 4) (transportA a b) k
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row256Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row256Interface.top (Fin 12)) 1 := by
  let k := closureGenerators row256Generators 0
  let a := closureGenerators row256Generators 1
  let b := closureGenerators row256Generators 2
  apply uniform_of_words 0 row256Generators row256Tops 1 2
    (anchorA k a b 2) (transportA a b) b
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row270Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row270Interface.top (Fin 12)) 1 := by
  let k := closureGenerators row270Generators 0
  let a := closureGenerators row270Generators 1
  let b := closureGenerators row270Generators 2
  apply uniform_of_words 0 row270Generators row270Tops 1 2
    (anchorA (k * (a * k * a⁻¹)) a b 2) (transportA a b) k
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row287Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row287Interface.top (Fin 12)) 1 := by
  let k := closureGenerators row287Generators 0
  let a := closureGenerators row287Generators 2
  let b := closureGenerators row287Generators 3
  apply uniform_of_words 1 row287Generators row287Tops 2 3
    (anchorB k a) (transportB a b) b
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

end PrimitiveAffineDegreeTwoTwelveFiveCyclePairNaturalFamily
end SymmetricSubgroupAsymptotics

end
