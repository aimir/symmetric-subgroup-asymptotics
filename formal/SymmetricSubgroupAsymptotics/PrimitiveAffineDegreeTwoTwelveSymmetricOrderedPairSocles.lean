import SymmetricSubgroupAsymptotics.GeneratedLiteralImage
import SymmetricSubgroupAsymptotics.NaturalFourNormalChains
import SymmetricSubgroupAsymptotics.FiniteNormalRegistrySocleOfQuotientBounds
import SymmetricSubgroupAsymptotics.LiteralCyclicOrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelvePairFiniteCatalogueRows1To50
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveFlexibleProfiles

/-! The ordered-pair action supplies the other faithful transitive
twelve-point action of the literal `S₄`.  The group normal-chain argument
handles every quotient at once, and a single original four-cycle gives
three natural-module generators. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricOrderedPairSocles

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open DegreeTwoTwelvePairFiniteCatalogue DegreeTwoTwelveJointFiniteRows

abbrev Point := {p : Fin 4 × Fin 4 // p.1 ≠ p.2}

def pairList : Fin 12 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,0), (1,2), (1,3),
    (2,0), (2,1), (2,3), (3,0), (3,1), (3,2)]

def pairCode : Fin 4 → Fin 4 → Fin 12 :=
  ![![0,0,1,2], ![3,0,4,5], ![6,7,0,8], ![9,10,11,0]]

def pairChart : Fin 12 ≃ Point where
  toFun i := ⟨pairList i, (by decide +kernel : ∀ j, (pairList j).1 ≠ (pairList j).2) i⟩
  invFun p := pairCode p.1.1 p.1.2
  left_inv := by decide +kernel
  right_inv := by
    intro p
    apply Subtype.ext
    exact (by decide +kernel : ∀ a b : Fin 4, a ≠ b → pairList (pairCode a b) = (a,b))
      p.1.1 p.1.2 p.2

def orderedPerm (g : Equiv.Perm (Fin 4)) : Equiv.Perm Point where
  toFun p := ⟨(g p.1.1, g p.1.2), fun h => p.2 (g.injective h)⟩
  invFun p := ⟨(g.symm p.1.1, g.symm p.1.2), fun h => p.2 (g.symm.injective h)⟩
  left_inv p := by apply Subtype.ext; simp
  right_inv p := by apply Subtype.ext; simp

def orderedAction : Equiv.Perm (Fin 4) →* Equiv.Perm Point where
  toFun := orderedPerm
  map_one' := by apply Equiv.ext; intro p; apply Subtype.ext; rfl
  map_mul' g h := by apply Equiv.ext; intro p; apply Subtype.ext; rfl

def labels : Fin 12 ≃ Fin 12 where
  toFun := ![2, 3, 8, 4, 5, 6, 9, 7, 11, 0, 1, 10]
  invFun := ![9, 10, 0, 1, 3, 4, 5, 7, 2, 6, 11, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def points : Point ≃ Fin 12 := pairChart.symm.trans labels

def literalAction : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 12) :=
  points.permCongrHom.toMonoidHom.comp orderedAction

def generators : Fin 2 → Equiv.Perm (Fin 4) := ![Equiv.swap 0 1, finRotate 4]

theorem generates : Subgroup.closure (Set.range generators) = ⊤ := by
  have hset : Set.range generators =
      ({finRotate 4, Equiv.swap (0 : Fin 4) 1} : Set (Equiv.Perm (Fin 4))) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp [generators]
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact ⟨1, rfl⟩
      · exact ⟨0, rfl⟩
  rw [hset]
  simpa only [show finRotate 4 (0 : Fin 4) = 1 from rfl] using
    Equiv.Perm.closure_cycle_adjacent_swap
      (isCycle_finRotate_of_le (by decide : 2 ≤ 4))
      (support_finRotate_of_le (by decide : 2 ≤ 4)) (0 : Fin 4)

theorem bindings (i : Fin 2) : literalAction (generators i) = row8Generators i := by
  apply Equiv.ext
  intro x
  revert i x
  decide +kernel

theorem original_quotientSocle (N : Subgroup Row8Top) [N.Normal] :
    SocleNormalGeneratorBound (Row8Top ⧸ N) 1 := by
  let q := GeneratedLiteralImage.toTop literalAction generators row8Generators
    (Equiv.refl _) generates (by simpa using bindings)
  have hq : Function.Surjective q := GeneratedLiteralImage.toTop_surjective
    literalAction generators row8Generators (Equiv.refl _) generates (by simpa using bindings)
  exact quotientSocleNormalGeneratorBound_one_of_normal_total
    (normalSubgroups_total_of_surjective q hq NaturalFourNormalChains.symmetric_normal_total) N

def witness : LiteralCyclicOrbitWitness Row8Top 3 where
  element := closureGenerators row8Generators 1
  representative := ![0, 1, 4]
  orbitIndex := ![0, 1, 0, 1, 2, 0, 1, 2, 2, 1, 2, 0]
  exponent := ![0, 0, 1, 1, 0, 2, 2, 1, 3, 3, 2, 3]
  point_eq := by decide +kernel

theorem natural : UniformSubrepresentationGeneratorBound
    (permutationFunctionRepresentation (ZMod 2) row8Interface.top (Fin 12)) 3 :=
  witness.uniform _

def family : row8Interface.normalRegistry.QuotientSocleGeneratorFamily 1 :=
  .ofQuotientBounds _ (fun N => by letI := N.2; exact original_quotientSocle N.1)

def rowData : DegreeTwoTwelveJointFiniteRowData row8Interface 1 3 where
  topSocle := family
  natural := natural

def data : DegreeTwoTwelveFlexibleProfiles.Data row8Interface :=
  .ofExact rowData (by decide +kernel)

end SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoTwelveSymmetricOrderedPairSocles

end
