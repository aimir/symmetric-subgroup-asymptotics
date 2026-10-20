import SymmetricSubgroupAsymptotics.SimpleProductAutomorphismWreath
import Mathlib.GroupTheory.Index

/-! Coordinate projection products and their behavior under the literal
automorphism wreath chart. These lemmas retain the original subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

def coordinateImage {I T : Type} [Group T]
    (K : Subgroup (I → T)) (i : I) : Subgroup T :=
  K.map (Pi.evalMonoidHom (fun _ : I => T) i)

def projectionClosure {I T : Type} [Group T]
    (K : Subgroup (I → T)) : Subgroup (I → T) :=
  Subgroup.pi Set.univ (coordinateImage K)

theorem mem_projectionClosure {I T : Type} [Group T]
    (K : Subgroup (I → T)) (z : I → T) :
    z∈projectionClosure K ↔ ∀ i, z i∈coordinateImage K i := by
  simp only [projectionClosure,Subgroup.mem_pi,Set.mem_univ,forall_const]

theorem le_projectionClosure {I T : Type} [Group T]
    (K : Subgroup (I → T)) : K≤projectionClosure K := by
  intro z hz
  exact (mem_projectionClosure K z).mpr (fun i => ⟨z,hz,rfl⟩)

/-- A coordinate automorphism carries exactly the corresponding original
coordinate image, including all correlations still present in K. -/
theorem coordinateImage_automorphism
    {I T : Type} [Fintype I] [Group T] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (K : Subgroup (I → T)) (e : MulAut (I → T))
    (hK : ∀ z, e z∈K ↔ z∈K) (i : I) :
    (coordinateImage K ((SimpleProductAutomorphismWreath.routingHom hT e).symm i)).map
      ((SimpleProductAutomorphismWreath.equiv hT e).left i).toMonoidHom=
      coordinateImage K i := by
  let q := SimpleProductAutomorphismWreath.routingHom hT e
  let a := (SimpleProductAutomorphismWreath.equiv hT e).left i
  apply le_antisymm
  · rintro t ⟨u,⟨z,hz,hzu⟩,hut⟩
    refine ⟨e z,(hK z).mpr hz,?_⟩
    change e z i=t
    rw [SimpleProductAutomorphismWreath.coordinateFormula hT e z i]
    exact (congrArg a hzu).trans hut
  · rintro t ⟨z,hz,hzt⟩
    refine ⟨(e.symm z) (q.symm i),⟨e.symm z,?_,rfl⟩,?_⟩
    · exact (hK (e.symm z)).mp (by simpa only [MulEquiv.apply_symm_apply] using hz)
    · have h := SimpleProductAutomorphismWreath.coordinateFormula hT e (e.symm z) i
      change a ((e.symm z) (q.symm i))=t
      exact h.symm.trans ((congrFun (e.apply_symm_apply z) i).trans hzt)

theorem coordinateImage_index_automorphism
    {I T : Type} [Fintype I] [Group T] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (K : Subgroup (I → T)) (e : MulAut (I → T))
    (hK : ∀ z, e z∈K ↔ z∈K) (i : I) :
    (coordinateImage K ((SimpleProductAutomorphismWreath.routingHom hT e).symm i)).index=
      (coordinateImage K i).index := by
  have he := coordinateImage_automorphism hT K e hK i
  have hi := (coordinateImage K
    ((SimpleProductAutomorphismWreath.routingHom hT e).symm i)).index_map_equiv
      ((SimpleProductAutomorphismWreath.equiv hT e).left i)
  change ((coordinateImage K
    ((SimpleProductAutomorphismWreath.routingHom hT e).symm i)).map
      ((SimpleProductAutomorphismWreath.equiv hT e).left i).toMonoidHom).index=_ at hi
  rw [he] at hi
  exact hi.symm

theorem projectionClosure_automorphism
    {I T : Type} [Fintype I] [Group T] [Finite T] [IsSimpleGroup T]
    (hT : IsCenterless T) (K : Subgroup (I → T)) (e : MulAut (I → T))
    (hK : ∀ z, e z∈K ↔ z∈K) {z : I → T} (hz : z∈projectionClosure K) :
    e z∈projectionClosure K := by
  apply (mem_projectionClosure K (e z)).mpr
  intro i
  rw [SimpleProductAutomorphismWreath.coordinateFormula hT e z i]
  rw [←coordinateImage_automorphism hT K e hK i]
  exact ⟨z _,(mem_projectionClosure K z).mp hz _,rfl⟩

theorem projectionClosure_index
    {T : Type} [Group T] (k : ℕ) (K : Subgroup (Fin k → T))
    (d : ℕ) (hd : ∀ i, (coordinateImage K i).index=d) :
    (projectionClosure K).index=d^k := by
  simp only [projectionClosure,Subgroup.index_pi,hd,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin]

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
