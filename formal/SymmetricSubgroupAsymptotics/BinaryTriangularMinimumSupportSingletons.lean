import SymmetricSubgroupAsymptotics.BinaryTriangularMinimumSingletonsElementary

/-! Reindexing a minimum tuple changes only the names of its four
original vectors. Singleton leading supports force exponent two without
permuting point coordinates or assuming pure translations. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
open BinaryBooleanFourPolynomialCoordinates BinaryElementaryPairMonomialWidth

private theorem singleton_index_exists : ∀ a : Fin 16, (support a).card = 1 →
    ∃ i : Fin 4, a = variableIndex i := by decide

theorem singleton_label_reindex (label : Fin 4 → Fin 16)
    (hinj : Function.Injective label) (hcard : ∀ j, (support (label j)).card = 1) :
    ∃ e : Equiv.Perm (Fin 4), ∀ i, label (e i) = variableIndex i := by
  let f : Fin 4 → Fin 4 := fun j => (singleton_index_exists (label j) (hcard j)).choose
  have hf (j : Fin 4) : label j = variableIndex (f j) :=
    (singleton_index_exists (label j) (hcard j)).choose_spec
  have hfi : Function.Injective f := by
    intro i j he
    apply hinj
    rw [hf i, hf j, he]
  let e := Equiv.ofBijective f hfi.bijective_of_finite
  refine ⟨e.symm, ?_⟩
  intro i
  rw [hf]
  change variableIndex (e (e.symm i)) = variableIndex i
  rw [Equiv.apply_symm_apply]

namespace BinaryTriangularPointCoordinates
variable {G X : Type} [Group G] [MulAction G X]
    (T : BinaryTriangularPointCoordinates G X 4)
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

theorem squaresActTrivially_of_minimum_singleton_supports
    (W : Subrepresentation (permutationFunctionRepresentation (ZMod 2) G X))
    (v : Fin 4 → W.toRepresentation.asModule) (label : Fin 4 → Fin 16)
    (hlead : ∀ i, FiniteRowLeadingWeight.HasLeading
      (T.subrepresentationModuleCoordinates W (v i)) (label i))
    (hinj : Function.Injective label) (hcard : ∀ i, (support (label i)).card = 1)
    (hnocollision : ∀ i j : Fin 4, i ≠ j → ∀ r : (ZMod 2)[G],
      ¬FiniteRowLeadingWeight.HasLeading
        (T.subrepresentationModuleCoordinates W (r • v i)) (label j)) :
    BinarySquareActionStructure.SquaresActTrivially (G := G) (X := X) := by
  obtain ⟨e, he⟩ := singleton_label_reindex label hinj hcard
  apply T.squaresActTrivially_of_minimum_singleton_generators W (fun i => v (e i))
  · intro i
    simpa only [he] using hlead (e i)
  · intro i j hij r hr
    apply hnocollision (e i) (e j) (fun h => hij (e.injective h)) r
    simpa only [he] using hr

end BinaryTriangularPointCoordinates
end SymmetricSubgroupAsymptotics
