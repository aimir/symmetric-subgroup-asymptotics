import SymmetricSubgroupAsymptotics.CFSGTypeAColumnRootConjugacy
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal simultaneous row/column reindexing of SL and its central
quotient, transporting the proved column-root degree bound to Fin. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGTypeAIndexReindex
open Matrix
variable {F m n : Type*} [Field F] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

def slReindex (e : m≃n) : Matrix.SpecialLinearGroup m F≃*Matrix.SpecialLinearGroup n F where
  toFun A := ⟨Matrix.reindex e e A.val,(Matrix.det_reindex_self e A.val).trans A.property⟩
  invFun A := ⟨Matrix.reindex e.symm e.symm A.val,
    (Matrix.det_reindex_self e.symm A.val).trans A.property⟩
  left_inv A := by
    apply Subtype.ext
    ext i j
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,Equiv.symm_apply_apply]
  right_inv A := by
    apply Subtype.ext
    ext i j
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,Equiv.apply_symm_apply]
  map_mul' A B := by
    apply Subtype.ext
    exact (Matrix.reindexAlgEquiv F F e).map_mul A.val B.val

private theorem map_center_eq {G K : Type*} [Group G] [Group K] (e : G≃*K) :
    (Subgroup.center G).map e.toMonoidHom=Subgroup.center K := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    exact (Subgroup.centerCongr e ⟨y,hy⟩).property
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    exact ((Subgroup.centerCongr e).symm ⟨x,hx⟩).property

def pslReindex (e : m≃n) : Matrix.ProjectiveSpecialLinearGroup m F≃*
    Matrix.ProjectiveSpecialLinearGroup n F :=
  QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup m F))
    (Subgroup.center (Matrix.SpecialLinearGroup n F)) (slReindex e)
    (map_center_eq (slReindex e))

def splitCoordinates (d : ℕ) : Unit ⊕ Fin d≃Fin (d+1) :=
  (Equiv.sumCongr (Equiv.ofUnique Unit (Fin 1)) (Equiv.refl (Fin d))).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 d)))

theorem field_power_le_proper_index [Finite F] (d : ℕ) (hd : 2≤d)
    [IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin (d+1)) F)]
    (H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin (d+1)) F)) (hH : H≠⊤) :
    Nat.card F^d≤H.index := by
  let e := pslReindex (F:=F) (splitCoordinates d)
  letI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Unit ⊕ Fin d) F) :=
    e.isSimpleGroup
  have hK : H.comap e.toMonoidHom≠⊤ := by
    intro he
    apply hH
    apply top_unique
    intro x _
    have hx : e.symm x∈H.comap e.toMonoidHom := by rw [he];exact Subgroup.mem_top _
    change e (e.symm x)∈H at hx
    simpa only [MulEquiv.apply_symm_apply] using hx
  have hh := CFSGTypeAColumnRootConjugacy.field_power_le_proper_index
    (F:=F) (⟨0,by omega⟩ : Fin d) (⟨1,by omega⟩ : Fin d)
    (by
      intro he
      have hv := congrArg (fun i : Fin d => i.val) he
      change (0 : ℕ)=1 at hv
      omega)
    (H.comap e.toMonoidHom) hK
  have hi : (H.comap e.toMonoidHom).index=H.index :=
    H.index_comap_of_surjective (f:=e.toMonoidHom) e.surjective
  simpa only [Fintype.card_fin] using hh.trans_eq hi

end SymmetricSubgroupAsymptotics.CFSGTypeAIndexReindex
