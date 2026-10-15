import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily
import SymmetricSubgroupAsymptotics.BinaryPairEvenKernelGenerators

/-! Three further original capacity-one fields use the same six-point
operator as the capacity-two family. Their literal cross-block double
flip and its prescribed conjugates span every even pair flip; an original
odd-offset mover then permits generator sharing across pair-sum. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics
namespace PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue
open PrimitiveAffineDegreeTwoTwelveTwoTernaryPairNaturalFamily

def anchorWord {G : Type} [Group G] (j : Fin 3) (k t c : G) : Fin 6 → G :=
  let s := c * t * c⁻¹
  ![1, k, k * (t * k * t⁻¹),
    if j = 1 then s * k * s⁻¹ else s ^ 2 * k * (s ^ 2)⁻¹,
    k * (t ^ 2 * k * (t ^ 2)⁻¹),
    if j = 1 then s ^ 2 * k * (s ^ 2)⁻¹ else s * k * s⁻¹]

def transportWord {G : Type} [Group G] (j : Fin 3) (t c : G) (i : Fin 6) : G :=
  (![1, c, t, c * t, t ^ 2, c * t ^ 2] : Fin 6 → G)
    ((BinaryTwoTernaryPairOperator.pointCycle j).symm i)

theorem anchorWord_top {G H : Type} [Group G] [Group H]
    (f : G →* H) (j : Fin 3) (k t c : G) (hk : f k = 1) (i : Fin 6) :
    f (anchorWord j k t c i) = 1 := by
  fin_cases i <;> by_cases hj : j = 1 <;>
    simp [anchorWord, hj, map_mul, map_inv, map_pow, hk]

theorem uniform_one (j : Fin 3)
    (gs : Fin 4 → Equiv.Perm (Fin 12)) (tops : Fin 4 → Equiv.Perm (Fin 6))
    (hp : ∀ i, BinaryPairFrame.Preserves pointChart (gs i) (tops i))
    (ht : tops 1 = BinaryTwoTernaryPairOperator.rotation)
    (hc : tops 3 = BinaryTwoTernaryPairOperator.mover j)
    (hk : tops 0 = 1)
    (hb : ∀ i x : Fin 6,
      (pointChart.symm
        (((anchorWord j (closureGenerators gs 0) (closureGenerators gs 1)
          (closureGenerators gs 3) i : Subgroup.closure (Set.range gs)) :
            Equiv.Perm (Fin 12)) (pointChart (x, 0)))).2 =
        (Pi.single 0 1 + Pi.single i 1 : Fin 6 → ZMod 2) x)
    (htr : ∀ i : Fin 6,
      (pointChart.symm
        (((transportWord j (closureGenerators gs 1) (closureGenerators gs 3) i :
          Subgroup.closure (Set.range gs)) : Equiv.Perm (Fin 12))
            (pointChart (0, 0)))).1 = i)
    (ho : ∑ i : Fin 6, (pointChart.symm (gs 3 (pointChart (i, 0)))).2 = 1) :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2)
        (Subgroup.closure (Set.range gs)) (Fin 12)) 1 := by
  let F := frame gs tops hp
  let t : Subgroup.closure (Set.range gs) := closureGenerators gs 1
  let c : Subgroup.closure (Set.range gs) := closureGenerators gs 3
  let k : Subgroup.closure (Set.range gs) := closureGenerators gs 0
  have hk0 : F.top k = 1 :=
    (BinaryPairFrame.ofGenerators_top_generator pointChart gs tops hp 0).trans hk
  let anchor (i : Fin 6) : F.top.ker :=
    ⟨anchorWord j k t c i, anchorWord_top F.top j k t c hk0 i⟩
  have hanchor (i : Fin 6) :
      F.bits (anchor i) = Pi.single 0 (1 : ZMod 2) + Pi.single i (1 : ZMod 2) := by
    funext x
    exact hb i x
  have hflip (i l : Fin 6) : ∃ a : F.top.ker,
      F.bits a = Pi.single i (1 : ZMod 2) + Pi.single l (1 : ZMod 2) := by
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
  let tr : Fin 6 → Subgroup.closure (Set.range gs) := transportWord j t c
  have hzero (i : Fin 6) : F.top (tr i) 0 = i :=
    (F.intertwine (tr i) (0, 0)).symm.trans (htr i)
  have htrans (i l : Fin 6) : ∃ u, F.top u i = l := by
    refine ⟨tr l * (tr i)⁻¹, ?_⟩
    rw [map_mul, map_inv]
    change F.top (tr l) ((F.top (tr i))⁻¹ i) = l
    have hi : (F.top (tr i))⁻¹ i = 0 := by
      calc
        _ = (F.top (tr i))⁻¹ (F.top (tr i) 0) :=
          congrArg (fun x ↦ (F.top (tr i))⁻¹ x) (hzero i).symm
        _ = 0 := (F.top (tr i)).symm_apply_apply 0
    rw [hi, hzero]
  exact F.uniform_of_even_pair_kernel_and_odd_offset_coordinateTop
    hflip htrans ⟨closureGenerators gs 3, ho⟩ 1
    (pair_uniform j gs tops 1 3 hp ht hc)

open BinaryTwoTernaryPairOperator in
def row159Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, rotation, oddRotation, mover 2]

open BinaryTwoTernaryPairOperator in
def row197Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, rotation, reflection, mover 1]

open BinaryTwoTernaryPairOperator in
def row198Tops : Fin 4 → Equiv.Perm (Fin 6) := ![1, rotation, reflection, mover 0]

theorem row159Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row159Interface.top (Fin 12)) 1 := by
  apply uniform_one 2 row159Generators row159Tops
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row197Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row197Interface.top (Fin 12)) 1 := by
  apply uniform_one 1 row197Generators row197Tops
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

theorem row198Natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row198Interface.top (Fin 12)) 1 := by
  apply uniform_one 0 row198Generators row198Tops
  · unfold BinaryPairFrame.Preserves
    decide +kernel
  all_goals decide +kernel

end PrimitiveAffineDegreeTwoTwelveEvenTwoTernaryPairNaturalFamily
end SymmetricSubgroupAsymptotics

end
