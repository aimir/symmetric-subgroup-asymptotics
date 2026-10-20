import SymmetricSubgroupAsymptotics.BinaryCoinducedLargeOrbitHead

/-! Transport a large Sylow orbit on the original transitive point set to
the original point-stabilizer cosets. Both actions and the local quotient
remain unchanged. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SymmetricSubgroupAsymptotics.BinaryCoinducedLargeOrbitHead

local instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable {G X L V : Type} [Group G] [Finite G] [MulAction G X]
    [MulAction.IsPretransitive G X] [Finite X]
    [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- The orbit in the hypothesis is on the original physical points. -/
theorem head_le_six_on_points (x : X) (P : Sylow 3 G)
    (hX : Nat.card X = 16) (y : X) (hy : 9 ≤ Nat.card (MulAction.orbit P y))
    (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 6 := by
  let H := MulAction.stabilizer G x
  let e : (G ⧸ H) ≃ X := BinaryPairTernaryOrbitHead.pointCosetEquiv x
  have he (p : P) (z : G ⧸ H) : e (p • z) = p • e z :=
    BinaryPairTernaryOrbitHead.pointCosetEquiv_smul x (p : G) z
  let oe : MulAction.orbit P (e.symm y) ≃ MulAction.orbit P y :=
    e.subtypeEquiv (by
      intro z
      constructor
      · intro hz
        obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp hz
        refine MulAction.mem_orbit_iff.mpr ⟨p, ?_⟩
        simpa only [hp, e.apply_symm_apply] using (he p (e.symm y)).symm
      · intro hz
        obtain ⟨p, hp⟩ := MulAction.mem_orbit_iff.mp hz
        refine MulAction.mem_orbit_iff.mpr ⟨p, ?_⟩
        apply e.injective
        rw [he, e.apply_symm_apply]
        exact hp)
  apply head_le_six H P f hf rho hL hdim hrho
    ((Nat.card_congr e).trans hX) (e.symm y) _ B
  exact (Nat.card_congr oe).symm ▸ hy

end SymmetricSubgroupAsymptotics.BinaryCoinducedLargeOrbitHead

end
