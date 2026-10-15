import SymmetricSubgroupAsymptotics.CoinducedOddPointOrbitCover
import SymmetricSubgroupAsymptotics.QuotientSocleRelativeHead
import SymmetricSubgroupAsymptotics.BinaryFourAffineImage
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow1OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow2OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow5OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow11OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow13OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow15OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow16OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow17OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow18OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow19OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow20OrbitWitness

/-! The eleven remaining cyclic-odd primitive-sixteen literals need no
local quotient exclusions. Their retained five- or seven-cycle witness
has at most four point orbits. Every original local binary-plane head is
at most eight, and the checked all-original-quotient socle bound gives
relative rank at most two on the same original normal subgroup. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenRemainingOddFrames
open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourAffineImage

def top : Fin 11 → Subgroup (Equiv.Perm (Fin 16)) :=
  ![DegreeTwoPrimitiveSixteenInterfaces.Row1Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row2Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row5Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row11Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row13Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row15Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row16Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row17Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row18Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row19Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row20Top]

def witness : (j : Fin 11) → LiteralCyclicOrbitWitness (top j) 4 :=
  Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow1OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow2OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow5OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow11OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow13OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow15OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow16OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow17OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow18OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow19OrbitWitness.witness
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow20OrbitWitness.witness
    (fun i => Fin.elim0 i)))))))))))

/-- Both possible odd orders divide thirty-five. The exact original
permutation equation is the only additional finite check. -/
theorem witness_pow (j : Fin 11) : (witness j).element ^ 35 = 1 := by
  fin_cases j <;> apply Subtype.ext <;> apply Equiv.ext <;> intro x <;>
    revert x <;> decide +kernel

theorem translations_mem (j : Fin 11) (v : Multiplicative Vector) :
    translationPerm v ∈ top j := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.translation_mem v
  · have he : translationPerm v =
        PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.translationPerm
          (Multiplicative.ofAdd
            (PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.chartRotation.symm v.toAdd)) := by
      apply Equiv.ext
      intro x
      revert v x
      decide +kernel
    rw [he]
    exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.translation_mem _
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.translation_mem v

instance top_pretransitive (j : Fin 11) : MulAction.IsPretransitive (top j) (Fin 16) := by
  constructor
  intro x y
  let v : Multiplicative Vector :=
    Multiplicative.ofAdd (pointEquiv.symm y - pointEquiv.symm x)
  refine ⟨⟨translationPerm v, translations_mem j v⟩, ?_⟩
  change pointEquiv ((pointEquiv.symm y - pointEquiv.symm x) + pointEquiv.symm x) = y
  rw [sub_add_cancel, pointEquiv.apply_symm_apply]

theorem quotientSocle (j : Fin 11)
    (N : {N : Subgroup (top j) // N.Normal}) :
    SocleNormalGeneratorBound (top j ⧸ N.1) 2 := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow1AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow2AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow5AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow11AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow13AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow15AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow16AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow17AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow18AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow19AffineSocles.topSocle N
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow20AffineSocles.topSocle N

theorem relative_head_le_two (j : Fin 11)
    (N : Subgroup (top j)) [N.Normal] :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) ≤ 2 :=
  primeRelativeHead_le_of_all_quotient_socles 2 2 (quotientSocle j) N

theorem original_head_le_eight (j : Fin 11)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 8 := by
  simpa only [hdim, Nat.reduceMul] using
    CoinducedOddPointOrbitCover.binary_head_le_of_odd_cyclic_cover
      x (witness j).element 35 (by decide) (witness_pow j)
      (witness j).representative (witness j).orbit_cover rho B

theorem original_frame_sum_le_ten (j : Fin 11)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (N : Subgroup (top j)) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 10 := by
  have hn := relative_head_le_two j N
  have hb := original_head_le_eight j x rho hdim B
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenRemainingOddFrames
end
