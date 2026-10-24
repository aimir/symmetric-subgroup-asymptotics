import SymmetricSubgroupAsymptotics.FiniteFamilyCharacteristicPolynomial
import Mathlib.Logic.Equiv.Fin.Basic

/-! Reindexing an actual coordinate product conjugates the actual
coordinatewise operator. The checked Fin-family characteristic
polynomial formula therefore holds for every finite indexing type. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped BigOperators

namespace SymmetricSubgroupAsymptotics.FiniteIndexedCharacteristicPolynomial
universe u v w z
variable (K : Type u) [Field K]

theorem reindex_conj_piMap {ι : Type w} {κ : Type z} (M : ι → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    (A : (i : ι) → Module.End K (M i)) (e : ι ≃ κ) :
    (LinearEquiv.piCongrLeft' K M e).conj (LinearMap.piMap A) =
      LinearMap.piMap (fun j : κ => A (e.symm j)) := by
  let L := LinearEquiv.piCongrLeft' K M e
  apply LinearMap.ext
  intro x
  funext j
  change A (e.symm j) ((L.symm x) (e.symm j)) = A (e.symm j) (x j)
  have he := congrFun (L.apply_symm_apply x) j
  change (L.symm x) (e.symm j) = x j at he
  exact congrArg (A (e.symm j)) he

theorem charpoly_pi {ι : Type w} [Fintype ι] (M : ι → Type v)
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [∀ i, Module.Finite K (M i)] (A : (i : ι) → Module.End K (M i)) :
    (LinearMap.piMap A).charpoly = ∏ i : ι, (A i).charpoly := by
  let e := Fintype.equivFin ι
  let L := LinearEquiv.piCongrLeft' K M e
  have hc : L.conj (LinearMap.piMap A) =
      LinearMap.piMap (fun j : Fin (Fintype.card ι) => A (e.symm j)) :=
    reindex_conj_piMap K M A e
  calc
    _ = (L.conj (LinearMap.piMap A)).charpoly :=
      (L.charpoly_conj (LinearMap.piMap A)).symm
    _ = (LinearMap.piMap (fun j : Fin (Fintype.card ι) => A (e.symm j))).charpoly := by
      rw [hc]
    _ = ∏ j : Fin (Fintype.card ι), (A (e.symm j)).charpoly :=
      FiniteFamilyCharacteristicPolynomial.charpoly_pi_fin K (Fintype.card ι)
        (fun j => M (e.symm j)) (fun j => A (e.symm j))
    _ = _ := e.symm.prod_comp (fun i => (A i).charpoly)

end SymmetricSubgroupAsymptotics.FiniteIndexedCharacteristicPolynomial
