import SymmetricSubgroupAsymptotics.PrimitiveSocleSubdirectDegree
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index

/-! The stabilizer is retained from the original faithful transitive
action. In homogeneous coordinates it contains no whole simple factor. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

/-- A whole coordinate factor cannot fix one point of a faithful
transitive action: its conjugates are the same coordinate factor. -/
theorem coordinate_factor_not_in_stabilizer
    {E X T : Type} [Group E] [Group T] [Nontrivial T]
    [MulAction E X] [FaithfulSMul E X] [MulAction.IsPretransitive E X]
    (k : ℕ) (e : E ≃* (Fin k → T)) (x : X) (i : Fin k) :
    ¬ ∀ t : T, e.symm (Pi.mulSingle i t)∈MulAction.stabilizer E x := by
  intro hall
  obtain ⟨t,ht⟩ := exists_ne (1 : T)
  let h : E := e.symm (Pi.mulSingle i t)
  have hone : h=1 := by
    apply eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨u,hu⟩ := MulAction.exists_smul_eq E x y
    let v := e.symm (Pi.mulSingle i ((e u i)⁻¹*t*(e u i)))
    have hv : v • x=x := hall _
    have hmul : h*u=u*v := by
      apply e.injective
      ext j
      by_cases hj : j=i
      · subst j
        simp only [map_mul,h,v,MulEquiv.apply_symm_apply,Pi.mul_apply,
          Pi.mulSingle_eq_same]
        group
      · simp only [map_mul,h,v,MulEquiv.apply_symm_apply,Pi.mul_apply,
          Pi.mulSingle_eq_of_ne hj,one_mul,mul_one]
    calc
      h • y = h • (u • x) := by rw [hu]
      _ = u • (v • x) := by rw [←mul_smul,hmul,mul_smul]
      _ = y := by rw [hv,hu]
      _ = (1 : E) • y := (one_smul E y).symm
  have he : (Pi.mulSingle i t : Fin k → T)=1 := by
    simpa only [h,MulEquiv.apply_symm_apply,map_one] using congrArg e hone
  exact ht (by simpa only [Pi.mulSingle_eq_same,Pi.one_apply] using congrFun he i)

/-- Literal homogeneous coordinates on the original point stabilizer. -/
def pointStabilizerCoordinates
    {E X T : Type} [Group E] [Group T] [MulAction E X]
    (k : ℕ) (e : E ≃* (Fin k → T)) (x : X) : Subgroup (Fin k → T) :=
  (MulAction.stabilizer E x).map e.toMonoidHom

theorem pointStabilizerCoordinates_no_factor
    {E X T : Type} [Group E] [Group T] [Nontrivial T]
    [MulAction E X] [FaithfulSMul E X] [MulAction.IsPretransitive E X]
    (k : ℕ) (e : E ≃* (Fin k → T)) (x : X) (i : Fin k) :
    ¬ ∀ t : T, Pi.mulSingle i t∈pointStabilizerCoordinates k e x := by
  intro hall
  apply coordinate_factor_not_in_stabilizer k e x i
  intro t
  obtain ⟨u,hu,he⟩ := hall t
  have heq : e.symm (Pi.mulSingle i t)=u := by
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply] using he.symm
  exact heq.symm ▸ hu

theorem pointStabilizerCoordinates_index
    {E X T : Type} [Group E] [Group T] [MulAction E X]
    [MulAction.IsPretransitive E X]
    (k : ℕ) (e : E ≃* (Fin k → T)) (x : X) :
    (pointStabilizerCoordinates k e x).index=Nat.card X := by
  change ((MulAction.stabilizer E x).map (e : E →* (Fin k → T))).index=Nat.card X
  rw [Subgroup.index_map_equiv,MulAction.index_stabilizer_of_transitive E x]

/-- If the actual stabilizer is full subdirect, its original action degree
has the diagonal form required by the raw O'Nan--Scott interface. -/
theorem subdirect_pointStabilizer_degree
    {E X T : Type} [Group E] [Group T] [Finite T] [IsSimpleGroup T]
    [MulAction E X] [FaithfulSMul E X] [MulAction.IsPretransitive E X]
    (hT : IsCenterless T) (k : ℕ) (e : E ≃* (Fin k → T)) (x : X)
    (honto : ∀ i, Function.Surjective
      ((Pi.evalMonoidHom (fun _ : Fin k => T) i).comp
        (pointStabilizerCoordinates k e x).subtype)) :
    ∃ a : ℕ, k≤2*a ∧ Nat.card X=Nat.card T ^ a := by
  obtain ⟨a,ha,he⟩ := subdirect_index_form hT k
    (pointStabilizerCoordinates k e x) honto
    (pointStabilizerCoordinates_no_factor k e x)
  exact ⟨a,ha,(pointStabilizerCoordinates_index k e x).symm.trans he⟩

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
