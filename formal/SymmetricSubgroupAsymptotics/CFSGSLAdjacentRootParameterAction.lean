import SymmetricSubgroupAsymptotics.CFSGSLRootParameterAction
import SymmetricSubgroupAsymptotics.CFSGOrthogonalDGenerationAdjacentSL

/-! Adjacent row conjugators suffice for the actual SL parameter action.
All other rows are obtained from proved adjacent generation inside the
intertwining-pair group, so ambient central discrepancies do not require
an SL embedding or a presentation hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSLAdjacentRootParameterAction
open CFSGTypeAElementaryMatrices CFSGSLRootParameterAction
variable {F : Type} {G : Type*} [Field F] [Group G] {n : ℕ}
    (psi : Multiplicative (Fin n→F)→*G)

private def adjacentRows : Set (Matrix.SpecialLinearGroup (Fin n) F) :=
  {A | ∃(i j:Fin n)(hij:i≠j)(a:F),
    (i.val+1=j.val ∨ j.val+1=i.val) ∧ A=elementary hij a}

private theorem adjacentRows_generate : Subgroup.closure (adjacentRows (F:=F) (n:=n))=⊤ := by
  apply CFSGOrthogonalDGenerationAdjacentSL.eq_top_of_adjacent
  intro i j hij hadj a
  exact Subgroup.subset_closure ⟨i,j,hij,a,hadj,rfl⟩

theorem rows_of_adjacent
    (hadj : ∀i j:Fin n,∀(hij:i≠j), (i.val+1=j.val ∨ j.val+1=i.val)→∀a:F,
      ∃g:G,∀v:Fin n→F,g*psi (Multiplicative.ofAdd v)=
        psi (Multiplicative.ofAdd ((elementary hij a).toLin' v))*g)
    (i j:Fin n)(hij:i≠j)(a:F) :
    ∃g:G,∀v:Fin n→F,g*psi (Multiplicative.ofAdd v)=
      psi (Multiplicative.ofAdd ((elementary hij a).toLin' v))*g := by
  have hs : ∀A∈adjacentRows (F:=F) (n:=n),∃g:G,
      ∀p:Multiplicative (Fin n→F),g*psi p=psi (parameterAction A p)*g := by
    rintro A ⟨i,j,hij,a,hijadj,rfl⟩
    obtain ⟨g,hg⟩ := hadj i j hij hijadj a
    exact ⟨g,fun p=>hg p.toAdd⟩
  obtain ⟨g,hg⟩ := CFSGConjugationActionGraph.lift_every_of_generators
    parameterAction psi (adjacentRows (F:=F) (n:=n)) adjacentRows_generate hs (elementary hij a)
  exact ⟨g,fun v=>hg (Multiplicative.ofAdd v)⟩

theorem field_power_le_proper_index [Finite F] [Finite G] [IsSimpleGroup G]
    (b c:Fin n)(hbc:b≠c)(hpsi:Function.Injective psi)
    (hadj : ∀i j:Fin n,∀(hij:i≠j), (i.val+1=j.val ∨ j.val+1=i.val)→∀a:F,
      ∃g:G,∀v:Fin n→F,g*psi (Multiplicative.ofAdd v)=
        psi (Multiplicative.ofAdd ((elementary hij a).toLin' v))*g)
    (H:Subgroup G)(hH:H≠⊤) : Nat.card F^n≤H.index := by
  simpa only [Fintype.card_fin] using CFSGSLRootParameterAction.field_power_le_proper_index
    psi b c hbc hpsi (rows_of_adjacent psi hadj) H hH

end SymmetricSubgroupAsymptotics.CFSGSLAdjacentRootParameterAction
