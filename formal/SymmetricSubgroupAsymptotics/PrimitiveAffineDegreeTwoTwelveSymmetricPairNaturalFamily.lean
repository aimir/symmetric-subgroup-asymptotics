import SymmetricSubgroupAsymptotics.BinarySixPointSymmetricMatrixBlocks
import SymmetricSubgroupAsymptotics.BinaryPairEvenKernelGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows51To100
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows101To150

/-! Six original natural fields share the regular six-point symmetric
matrix-block theorem. The pair-sum sequence gives four cap-two fields.
Two cap-one fields additionally provide all even pair flips and an odd
offset, so the checked kernel-sharing theorem retains the pair bound. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open BinarySixPointSymmetricMatrixBlocks

abbrev pointChart := PrimitiveAffineDegreeTwoTwelveFullPairKernelNaturalFamily.pointChart

theorem pair_uniform {m : ℕ}
    (gs : Fin m → Equiv.Perm (Fin 12)) (tops : Fin m → Equiv.Perm (Fin 6))
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (c b : Subgroup.closure (Set.range gs))
    (hc : ∀ x : Fin 6,
      (pointChart.symm ((c : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = rotation x)
    (hb : ∀ x : Fin 6,
      (pointChart.symm ((b : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = reflection x) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (BinaryPairFrame.ofGenerators pointChart gs tops hp).top.range (Fin 6)) 1 := by
  let F := BinaryPairFrame.ofGenerators pointChart gs tops hp
  apply uniform_subgroup F.top.range (F.top.rangeRestrict c) (F.top.rangeRestrict b)
  · apply Equiv.ext
    intro x
    exact (F.intertwine c (x, 0)).symm.trans (hc x)
  · apply Equiv.ext
    intro x
    exact (F.intertwine b (x, 0)).symm.trans (hb x)

theorem uniform_two {m : ℕ}
    (gs : Fin m → Equiv.Perm (Fin 12)) (tops : Fin m → Equiv.Perm (Fin 6))
    (c b : Subgroup.closure (Set.range gs))
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (hc : ∀ x : Fin 6,
      (pointChart.symm ((c : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = rotation x)
    (hb : ∀ x : Fin 6,
      (pointChart.symm ((b : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = reflection x) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (Subgroup.closure (Set.range gs)) (Fin 12)) 2 :=
  (BinaryPairFrame.ofGenerators pointChart gs tops hp).permutationFunctionRepresentation_uniform_of_coordinateTop 1
      (pair_uniform gs tops hp c b hc hb)

def transportWords {G : Type} [Group G] (c b : G) : Fin 6 → G :=
  ![1, c * b, c, c ^ 2 * b, c ^ 2, b]

theorem uniform_one {m : ℕ}
    (gs : Fin m → Equiv.Perm (Fin 12)) (tops : Fin m → Equiv.Perm (Fin 6))
    (c b u : Subgroup.closure (Set.range gs))
    (anchors : Fin 6 → Subgroup.closure (Set.range gs))
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (hc : ∀ x : Fin 6,
      (pointChart.symm ((c : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = rotation x)
    (hb : ∀ x : Fin 6,
      (pointChart.symm ((b : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = reflection x)
    (hfix : ∀ i x : Fin 6,
      (pointChart.symm ((anchors i : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).1 = x)
    (hbits : ∀ i x : Fin 6,
      (pointChart.symm ((anchors i : Equiv.Perm (Fin 12)) (pointChart (x, 0)))).2 =
        (Pi.single 0 1 + Pi.single i 1 : Fin 6 → ZMod 2) x)
    (htransport : ∀ i : Fin 6,
      (pointChart.symm (((transportWords c b i : Subgroup.closure (Set.range gs)) : Equiv.Perm (Fin 12))
        (pointChart (0, 0)))).1 = i)
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
  have hflip (i j : Fin 6) : ∃ k : F.top.ker,
      F.bits k = Pi.single i (1 : ZMod 2) + Pi.single j (1 : ZMod 2) := by
    refine ⟨anchor i * anchor j, ?_⟩
    have he : F.bits (anchor i * anchor j) = F.bits (anchor i) + F.bits (anchor j) :=
      congrArg Multiplicative.toAdd (F.bitsHom.map_mul (anchor i) (anchor j))
    rw [he, hanchor, hanchor]
    have hz : (Pi.single 0 (1 : ZMod 2) + Pi.single 0 1 : Fin 6 → ZMod 2) = 0 := by
      funext x
      exact CharTwo.add_self_eq_zero ((Pi.single 0 1 : Fin 6 → ZMod 2) x)
    calc
      _ = ((Pi.single 0 (1 : ZMod 2) : Fin 6 → ZMod 2) + Pi.single 0 1) +
          (Pi.single i 1 + Pi.single j 1) := by abel
      _ = _ := by rw [hz, zero_add]
  let tr := transportWords c b
  have hzero (i : Fin 6) : F.top (tr i) 0 = i :=
    (F.intertwine (tr i) (0, 0)).symm.trans (htransport i)
  have htrans (i j : Fin 6) : ∃ g, F.top g i = j := by
    refine ⟨tr j * (tr i)⁻¹, ?_⟩
    rw [map_mul, map_inv]
    change F.top (tr j) ((F.top (tr i))⁻¹ i) = j
    have hi : (F.top (tr i))⁻¹ i = 0 := by
      calc
        _ = (F.top (tr i))⁻¹ (F.top (tr i) 0) :=
          congrArg (fun x ↦ (F.top (tr i))⁻¹ x) (hzero i).symm
        _ = 0 := (F.top (tr i)).symm_apply_apply 0
    rw [hi, hzero]
  exact F.uniform_of_even_pair_kernel_and_odd_offset_coordinateTop
    hflip htrans ⟨u, hodd⟩ 1 (pair_uniform gs tops hp c b hc hb)

def reflectionA : Equiv.Perm (Fin 6) where
  toFun := ![1, 0, 5, 4, 3, 2]
  invFun := ![1, 0, 5, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extra65 : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 5, 1, 3]
  invFun := ![2, 4, 0, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def extra112 : Equiv.Perm (Fin 6) where
  toFun := ![0, 1, 5, 3, 4, 2]
  invFun := ![0, 1, 5, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def kleinMover : Equiv.Perm (Fin 6) where
  toFun := ![0, 4, 5, 3, 1, 2]
  invFun := ![0, 4, 5, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def oddMover : Equiv.Perm (Fin 6) where
  toFun := ![3, 5, 4, 0, 2, 1]
  invFun := ![3, 5, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row65Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, rotation, reflectionA, extra65]
def row68Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, kleinMover, rotation, oddMover]
def row69Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, 1, rotation, reflection]
def row107Tops : Fin 5 → Equiv.Perm (Fin 6) := ![1, 1, 1, rotation, reflection]
def row112Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, rotation, reflectionA, extra112]
def row192Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, kleinMover, rotation, oddMover]

theorem row65Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row65Interface.top (Fin 12)) 2 := by
  let c := closureGenerators row65Generators 1
  apply uniform_two row65Generators row65Tops c (c ^ 2 * closureGenerators row65Generators 2)
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row68Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row68Interface.top (Fin 12)) 2 := by
  let c := closureGenerators row68Generators 2
  apply uniform_two row68Generators row68Tops c
    (c * closureGenerators row68Generators 1 * closureGenerators row68Generators 3)
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row69Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row69Interface.top (Fin 12)) 2 := by
  apply uniform_two row69Generators row69Tops
    (closureGenerators row69Generators 2) (closureGenerators row69Generators 3)
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row112Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row112Interface.top (Fin 12)) 2 := by
  let c := closureGenerators row112Generators 1
  apply uniform_two row112Generators row112Tops c (c ^ 2 * closureGenerators row112Generators 2)
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

def anchors107 {G : Type} [Group G] (k l m c : G) : Fin 6 → G :=
  ![1, k, l, m, l * (c * l * c⁻¹), l * (c * m * c⁻¹)]

def anchors192 {G : Type} [Group G] (k a c : G) : Fin 6 → G :=
  let v4 := a * k * a⁻¹
  let v5 := v4 * (c ^ 2 * k * (c ^ 2)⁻¹)
  let v3 := v5 * ((a * c) * k * (a * c)⁻¹)
  let v2 := v3 * (c * k * c⁻¹)
  ![1, k, v2, v3, v4, v5]

theorem row107Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row107Interface.top (Fin 12)) 1 := by
  let c := closureGenerators row107Generators 3
  let b := closureGenerators row107Generators 4
  apply uniform_one row107Generators row107Tops c b b
    (anchors107 (closureGenerators row107Generators 0) (closureGenerators row107Generators 1)
      (closureGenerators row107Generators 2) c)
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row192Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row192Interface.top (Fin 12)) 1 := by
  let a := closureGenerators row192Generators 1
  let c := closureGenerators row192Generators 2
  let b := closureGenerators row192Generators 3
  apply uniform_one row192Generators row192Tops c (c * a * b) b
    (anchors192 (closureGenerators row192Generators 0) a c)
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricPairNaturalFamily

end
