import SymmetricSubgroupAsymptotics.BinaryCoinducedOddOvergroupHead
import SymmetricSubgroupAsymptotics.SylowInsideCoprimeIndex

/-! Original-point version of the odd fifteen-orbit head bound. The odd
subgroup's coprime index supplies its ambient Sylow internally. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCoinducedOddOvergroupHead

local instance fifteenPoint_primeThree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem head_le_two_on_points
    {G X L V : Type} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [Finite X]
    [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (A : Subgroup G) (hodd : ¬ 2 ∣ Nat.card A) (hindex : ¬ 3 ∣ A.index)
    (hX : Nat.card X = 16) (y : X) (hy : 15 ≤ Nat.card (MulAction.orbit A y))
    (x : X) (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2 := by
  obtain ⟨P, hPA⟩ := exists_sylow_le_of_not_dvd_index A hindex
  let H := MulAction.stabilizer G x
  let e : (G ⧸ H) ≃ X := BinaryPairTernaryOrbitHead.pointCosetEquiv x
  have he (a : A) (z : G ⧸ H) : e (a • z) = a • e z :=
    BinaryPairTernaryOrbitHead.pointCosetEquiv_smul x (a : G) z
  let oe : MulAction.orbit A (e.symm y) ≃ MulAction.orbit A y :=
    e.subtypeEquiv (by
      intro z
      constructor
      · intro hz
        obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hz
        refine MulAction.mem_orbit_iff.mpr ⟨a, ?_⟩
        simpa only [ha, e.apply_symm_apply] using (he a (e.symm y)).symm
      · intro hz
        obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hz
        refine MulAction.mem_orbit_iff.mpr ⟨a, ?_⟩
        apply e.injective
        rw [he, e.apply_symm_apply]
        exact ha)
  apply head_le_two_of_fifteen_orbit H P A hPA hodd f hf rho hL hdim hrho
    ((Nat.card_congr e).trans hX) (e.symm y) _ B
  exact (Nat.card_congr oe).symm ▸ hy

end SymmetricSubgroupAsymptotics.BinaryCoinducedOddOvergroupHead

end
