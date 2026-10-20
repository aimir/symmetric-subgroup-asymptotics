import SymmetricSubgroupAsymptotics.TransitiveSixSylowTrivialQuotient
import SymmetricSubgroupAsymptotics.PermutationOrbitCoverGenerators

/-! Every transitive six-point action has a uniform binary natural-module
bound two. Restriction to the actual Sylow three has at most two original
point orbits, and its order is invertible in the original binary field. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics

 theorem transitiveSix_binary_natural_uniform_two
    {G : Type} [Group G] [Finite G] [MulAction G (Fin 6)]
    [MulAction.IsPretransitive G (Fin 6)] :
    UniformSubrepresentationGeneratorBound
      (permutationFunctionRepresentation (ZMod 2) G (Fin 6)) 2 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := Classical.choice inferInstance
  let O := MulAction.orbitRel.Quotient P (Fin 6)
  letI : Fintype O := Fintype.ofFinite O
  letI : NeZero (Nat.card P : ZMod 2) := ⟨sylowThree_card_binary_neZero P⟩
  have hcount := traceySylow_orbit_count 3 P (X := Fin 6)
  have hle : Fintype.card O ≤ 2 := by
    have h : Fintype.card O*3 ≤ 6 := by
      simpa only [O,Nat.card_fin,show Nat.factorization 6 3=1 by decide +kernel,
        pow_one,Fintype.card_fin] using hcount
    omega
  let e : O ≃ Fin (Fintype.card O) := Fintype.equivFin O
  let orbitAt : Fin 2 → O := fun j =>
    if hj : j.val < Fintype.card O then e.symm ⟨j.val,hj⟩ else Quotient.mk'' (0 : Fin 6)
  have honto : Function.Surjective orbitAt := by
    intro o
    let j : Fin 2 := ⟨(e o).val,lt_of_lt_of_le (e o).isLt hle⟩
    refine ⟨j,?_⟩
    have hj : j.val < Fintype.card O := (e o).isLt
    simp only [orbitAt,dif_pos hj]
    exact e.symm_apply_apply o
  apply permutationFunctionRepresentation_uniform_of_restricted_orbitCover
    (k := ZMod 2) (Subgroup.subtype (P : Subgroup G))
    (fun j => (orbitAt j).out)
  intro x
  let o : O := Quotient.mk'' x
  obtain ⟨j,hj⟩ := honto o
  have heq : (Quotient.mk'' (orbitAt j).out : O)=Quotient.mk'' x :=
    (Quotient.out_eq' (orbitAt j)).trans hj
  obtain ⟨g,hg⟩ := (Quotient.exact heq.symm : x ∈ MulAction.orbit P (orbitAt j).out)
  exact ⟨j,g,hg⟩

end SymmetricSubgroupAsymptotics
