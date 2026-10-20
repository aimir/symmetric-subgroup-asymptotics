import SymmetricSubgroupAsymptotics.CoinducedOddPointOrbitCover
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadNormalGenerators
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow3OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow6OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow9OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow12OrbitWitness
import SymmetricSubgroupAsymptotics.PrimitiveAffineDegreeTwoPrimitiveSixteenRow14OrbitWitness

/-! Five eligible primitive-sixteen literals have the displayed order-
dividing-fifteen generator with two physical point orbits. The original
local coinduced head is at most four for every two-dimensional local
representation, with no local epimorphism-kernel classification. Together
with the checked original all-normal width two, the total is at most six. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOddOrbitFrames

open Non2UnipotentPrefixFiniteMenu.PrimitiveAffineImprimitiveBlockTransfer
open BinaryFourAffineImage

def top : Fin 5 → Subgroup (Equiv.Perm (Fin 16)) :=
  ![DegreeTwoPrimitiveSixteenInterfaces.Row3Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row6Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row9Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row12Top,
    DegreeTwoPrimitiveSixteenInterfaces.Row14Top]

def element : (j : Fin 5) → top j :=
  Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow3OrbitWitness.element
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow6OrbitWitness.element
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow9OrbitWitness.element
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow12OrbitWitness.element
    (Fin.cases PrimitiveAffineDegreeTwoPrimitiveSixteenRow14OrbitWitness.element
    (fun i => Fin.elim0 i)))))

theorem element_pow_fifteen (j : Fin 5) : element j ^ 15 = 1 := by
  fin_cases j <;> apply Subtype.ext <;> apply Equiv.ext <;> intro x <;>
    revert x <;> decide +kernel

def representatives : Fin 2 → Fin 16 := ![0, 1]

/-- Five fixed original generator witnesses; only sixteen-point equations
and exponents below fifteen are checked. No group elements are enumerated. -/
theorem point_cover (j : Fin 5) : ∀ x : Fin 16,
    ∃ i : Fin 2, ∃ m : Fin 15, element j ^ m.val • representatives i = x := by
  fin_cases j <;> decide +kernel

theorem translations_mem (j : Fin 5) (v : Multiplicative Vector) :
    translationPerm v ∈ top j := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.translation_mem v
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.translation_mem v

instance top_pretransitive (j : Fin 5) : MulAction.IsPretransitive (top j) (Fin 16) := by
  constructor
  intro x y
  let v : Multiplicative Vector :=
    Multiplicative.ofAdd (pointEquiv.symm y - pointEquiv.symm x)
  refine ⟨⟨translationPerm v, translations_mem j v⟩, ?_⟩
  change pointEquiv ((pointEquiv.symm y - pointEquiv.symm x) + pointEquiv.symm x) = y
  rw [sub_add_cancel, pointEquiv.apply_symm_apply]

theorem normal_generating_pairs (j : Fin 5) :
    ∀ N : Subgroup (top j), N.Normal →
      ∃ z : Fin 2 → top j, Subgroup.normalClosure (Set.range z) = N := by
  fin_cases j
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow3AffineSocles.top_normal_generating_pairs
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow6AffineSocles.top_normal_generating_pairs
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow9AffineSocles.top_normal_generating_pairs
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow12AffineSocles.top_normal_generating_pairs
  · exact PrimitiveAffineDegreeTwoPrimitiveSixteenRow14AffineSocles.top_normal_generating_pairs

theorem original_head_le_four (j : Fin 5)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap
        (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 4 := by
  have hcover : ∀ z : Fin 16, ∃ i : Fin 2, ∃ m : ℕ,
      element j ^ m • representatives i = z := by
    intro z
    obtain ⟨i, m, hm⟩ := point_cover j z
    exact ⟨i, m.val, hm⟩
  simpa only [hdim, Nat.reduceMul] using
    CoinducedOddPointOrbitCover.binary_head_le_of_odd_cyclic_cover
      x (element j) 15 (by decide) (element_pow_fifteen j) representatives hcover rho B

theorem original_frame_sum_le_six (j : Fin 5)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (x : Fin 16) (rho : Representation (ZMod 2) (MulAction.stabilizer (top j) x) V)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (N : Subgroup (top j)) [N.Normal]
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer (top j) x).subtype rho)) :
    Module.finrank (ZMod 2) (primeRelativeCharacters 2 N) +
      Module.finrank (ZMod 2)
        (B.toRepresentation.IntertwiningMap
          (Representation.trivial (ZMod 2) (top j) (ZMod 2))) ≤ 6 := by
  obtain ⟨z, hz⟩ := normal_generating_pairs j N inferInstance
  have hn := primeRelativeHead_le_normal_generating_tuple 2 N z hz
  have hb := original_head_le_four j x rho hdim B
  omega

end SymmetricSubgroupAsymptotics.PrimitiveAffineSixteenOddOrbitFrames

end
