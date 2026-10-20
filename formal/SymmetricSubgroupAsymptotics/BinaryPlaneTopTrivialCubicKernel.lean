import SymmetricSubgroupAsymptotics.BinaryPlaneWreathActualOddKernel

/-! A top-trivial cubic element of the actual linear image belongs to
its literal odd kernel. No coordinate independence is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.BinaryPlaneTopTrivialCubicKernel
open BinaryPlanePermutationAffineEquiv BinaryPlaneWreathIrreducible
open BinaryPlaneWreathActualOddKernel BinaryPlaneWreathNormalGenerators

private theorem cubic_even : ∀ p : Equiv.Perm (Fin 3),
    p^3=1 → oddMarkerSign p=1 := by decide +kernel

variable {R I : Type} [Group R] [MulAction R I] [Fintype I] [DecidableEq I]

theorem mem_oddKernel (C : Subgroup (W (R := R) (I := I))) (g : C)
    (ht : (g : W (R := R) (I := I)).right=1) (hc : g^3=1) : g∈oddKernel C := by
  change signProjection C g=1
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    change (oddMarkerSign (toThree ((g : W (R := R) (I := I)).left i))).toAdd=0
    have hl : (g : W (R := R) (I := I)).left i^3=1 := by
      have hh := congrArg (fun z : C => (z : W (R := R) (I := I)).left i) hc
      simpa [pow_succ,PermutationalWreathProduct.mul_left,
        PermutationalWreathProduct.mul_right,ht] using hh
    have he : toThree ((g : W (R := R) (I := I)).left i)^3=1 := by
      rw [← map_pow,hl,map_one]
    rw [cubic_even _ he]
    rfl
  · exact ht

end SymmetricSubgroupAsymptotics.BinaryPlaneTopTrivialCubicKernel
