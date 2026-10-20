import SymmetricSubgroupAsymptotics.PrimitiveSocleProjectionClosure
import SymmetricSubgroupAsymptotics.ZmudFaithfulCharacterInput
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! A coordinate coloring invariant under the original point stabilizer
is constant on a homogeneous minimal normal subgroup. The proof constructs
an actual ambient normal support subgroup. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers

def coordinateConjugation
    {G T : Type} [Group G] [Group T]
    (E : Subgroup G) [E.Normal] (k : ℕ) (e : E ≃* (Fin k → T))
    (g : G) : MulAut (Fin k → T) :=
  (e.symm.trans (MulAut.conjNormal (H := E) g)).trans e

theorem transitive_sup_stabilizer_eq_top
    {G X : Type} [Group G] [MulAction G X]
    (E : Subgroup G) [MulAction.IsPretransitive E X] (x : X) :
    E⊔MulAction.stabilizer G x=⊤ := by
  apply top_unique
  intro g _
  obtain ⟨u,hu⟩ := MulAction.exists_smul_eq E x (g • x)
  change (u : G) • x=g • x at hu
  have hp : (u : G)⁻¹*g∈MulAction.stabilizer G x := by
    change ((u : G)⁻¹*g) • x=x
    rw [mul_smul,←hu,inv_smul_smul]
  have hm := (E⊔MulAction.stabilizer G x).mul_mem
    (Subgroup.mem_sup_left u.property) (Subgroup.mem_sup_right hp)
  simpa only [mul_inv_cancel_left] using hm

def coordinateSupport
    {I T C : Type} [Group T] (c : I → C) (v : C) : Subgroup (I → T) where
  carrier := {z | ∀ i, c i≠v → z i=1}
  one_mem' := by intro i _; rfl
  mul_mem' := by intro z w hz hw i hi; exact (congrArg₂ (·*·) (hz i hi) (hw i hi)).trans (one_mul 1)
  inv_mem' := by intro z hz i hi; exact (congrArg Inv.inv (hz i hi)).trans inv_one

/-- Minimality in the actual ambient group rules out every nonconstant
point-stabilizer-invariant coloring of the simple factors. -/
theorem minimalNormal_invariant_color_constant
    {G X T C : Type} [Group G] [Group T] [Finite T] [IsSimpleGroup T]
    [MulAction G X] (E : Subgroup G) [E.Normal]
    (hE : IsMinimalNormalSubgroup E) [MulAction.IsPretransitive E X]
    (hT : IsCenterless T) (k : ℕ) (e : E ≃* (Fin k → T)) (x : X)
    (c : Fin k → C)
    (hc : ∀ p∈MulAction.stabilizer G x, ∀ i,
      c ((SimpleProductAutomorphismWreath.routingHom hT
        (coordinateConjugation E k e p)).symm i)=c i) :
    ∀ i j, c i=c j := by
  intro i j
  let L : Subgroup E := (coordinateSupport c (c i)).comap e.toMonoidHom
  let M : Subgroup G := L.map E.subtype
  have hME : M≤E := by rintro m ⟨u,_,rfl⟩; exact u.property
  have hEnorm : E≤Subgroup.normalizer M := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro g hg m ⟨u,hu,rfl⟩
    let v : E := ⟨g,hg⟩
    refine ⟨v*u*v⁻¹,?_,rfl⟩
    change ∀ q, c q≠c i → e (v*u*v⁻¹) q=1
    intro q hq
    have huq : e u q=1 := hu q hq
    simp only [map_mul,map_inv,Pi.mul_apply,Pi.inv_apply,huq,mul_one,mul_inv_cancel]
  have hPnorm : MulAction.stabilizer G x≤Subgroup.normalizer M := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro p hp m ⟨u,hu,rfl⟩
    refine ⟨MulAut.conjNormal p u,?_,rfl⟩
    change ∀ q, c q≠c i → e (MulAut.conjNormal p u) q=1
    intro q hq
    let a := coordinateConjugation E k e p
    have hroute : c ((SimpleProductAutomorphismWreath.routingHom hT a).symm q)≠c i := by
      rw [hc p hp q]
      exact hq
    have huq := hu _ hroute
    change e u ((SimpleProductAutomorphismWreath.routingHom hT a).symm q)=1 at huq
    have he := SimpleProductAutomorphismWreath.coordinateFormula hT a (e u) q
    change e (MulAut.conjNormal p (e.symm (e u))) q=_ at he
    rw [e.symm_apply_apply] at he
    rw [he,huq,map_one]
  have hMnormal : M.Normal := Subgroup.normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [←transitive_sup_stabilizer_eq_top E x]
    exact sup_le hEnorm hPnorm)
  obtain ⟨t,ht⟩ := exists_ne (1 : T)
  have hMne : M≠⊥ := by
    intro hm
    have hmem : ((e.symm (Pi.mulSingle i t) : E) : G)∈M := by
      refine ⟨e.symm (Pi.mulSingle i t),?_,rfl⟩
      change ∀ q, c q≠c i → e (e.symm (Pi.mulSingle i t)) q=1
      intro q hq
      rw [e.apply_symm_apply]
      exact Pi.mulSingle_eq_of_ne (M := fun _ : Fin k => T) (fun h => hq (congrArg c h)) t
    rw [hm,Subgroup.mem_bot] at hmem
    have he : e.symm (Pi.mulSingle i t)=(1 : E) := Subtype.ext hmem
    have hf := congrFun (congrArg e he) i
    exact ht (by simpa only [MulEquiv.apply_symm_apply,Pi.mulSingle_eq_same,map_one,Pi.one_apply] using hf)
  have hMEq : M=E := hE.2.2 M hMnormal hMne hME
  by_contra hij
  have hmem : ((e.symm (Pi.mulSingle j t) : E) : G)∈M := by
    rw [hMEq]
    exact (e.symm _).property
  obtain ⟨u,hu,he⟩ := hmem
  have heq : u=e.symm (Pi.mulSingle j t) := Subtype.ext he
  have hq := hu j (Ne.symm hij)
  change e u j=1 at hq
  rw [heq,e.apply_symm_apply,Pi.mulSingle_eq_same] at hq
  exact ht hq

end SymmetricSubgroupAsymptotics.PrimitiveSocleONanScottHelpers
