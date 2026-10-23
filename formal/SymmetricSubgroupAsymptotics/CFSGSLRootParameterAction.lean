import SymmetricSubgroupAsymptotics.CFSGConjugationActionGraph
import SymmetricSubgroupAsymptotics.CFSGTypeAElementaryGeneration
import SymmetricSubgroupAsymptotics.CFSGTypeAVectorTransitivity
import SymmetricSubgroupAsymptotics.CFSGConjugateSubgroupDegree
import Mathlib.Algebra.Group.Equiv.TypeTags

/-! An actual additive root-star chart with elementary row conjugators
has one nonidentity conjugacy class, hence gives a field-power proper
index. The acting SL group is used only through its proved generation
and nonzero-vector transitivity; no SL hom into the ambient group is
assumed. Concrete exceptional root charts discharge the row equations. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGSLRootParameterAction
open CFSGTypeAElementaryMatrices
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

local instance parameterCommGroup : CommGroup (Multiplicative (n→F)) := inferInstance

def parameterAction : Matrix.SpecialLinearGroup n F →* MulAut (Multiplicative (n→F)) where
  toFun A := AddEquiv.toMultiplicative A.toLin'.toAddEquiv
  map_one' := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd ((1 : Matrix.SpecialLinearGroup n F).toLin' v.toAdd)=
      Multiplicative.ofAdd v.toAdd
    rw [map_one]
    rfl
  map_mul' A B := by
    apply MulEquiv.ext
    intro v
    change Multiplicative.ofAdd ((A*B).toLin' v.toAdd)=
      Multiplicative.ofAdd (A.toLin' (B.toLin' v.toAdd))
    rw [map_mul,LinearEquiv.mul_apply]

theorem parameterAction_apply (A : Matrix.SpecialLinearGroup n F) (v : Multiplicative (n→F)) :
    parameterAction A v=Multiplicative.ofAdd (A.toLin' v.toAdd) := rfl

variable {G : Type*} [Group G] (psi : Multiplicative (n→F) →* G)

theorem range_nonidentity_conjugate (b c:n) (hbc:b≠c)
    (hrows : ∀ i j:n, ∀ (hij:i≠j) (a:F), ∃ g:G, ∀ v:n→F,
      g*psi (Multiplicative.ofAdd v)=
        psi (Multiplicative.ofAdd ((elementary hij a).toLin' v))*g)
    (x y:psi.range) (hx:x≠1) (hy:y≠1) : ∃ g:G,g*(x:G)*g⁻¹=(y:G) := by
  apply CFSGConjugationActionGraph.range_nonidentity_conjugate parameterAction psi
    {A | ∃ (i j:n) (hij:i≠j) (a:F),A=elementary hij a}
    CFSGTypeAElementaryGeneration.closure_elementary_eq_top _ _ x y hx hy
  · rintro A ⟨i,j,hij,a,rfl⟩
    obtain ⟨g,hg⟩ := hrows i j hij a
    exact ⟨g,fun v => hg v.toAdd⟩
  · intro u v hu hv
    have hu0 : u.toAdd≠0 := by
      intro he
      apply hu
      exact congrArg Multiplicative.ofAdd he
    have hv0 : v.toAdd≠0 := by
      intro he
      apply hv
      exact congrArg Multiplicative.ofAdd he
    obtain ⟨A,hA⟩ := CFSGTypeAVectorTransitivity.exists_map_nonzero b c hbc
      u.toAdd v.toAdd hu0 hv0
    exact ⟨A,congrArg Multiplicative.ofAdd hA⟩

theorem field_power_le_proper_index [Finite F] [Finite G] [IsSimpleGroup G]
    (b c:n) (hbc:b≠c) (hpsi:Function.Injective psi)
    (hrows : ∀ i j:n, ∀ (hij:i≠j) (a:F), ∃ g:G, ∀ v:n→F,
      g*psi (Multiplicative.ofAdd v)=
        psi (Multiplicative.ofAdd ((elementary hij a).toLin' v))*g)
    (H:Subgroup G) (hH:H≠⊤) : Nat.card F^Fintype.card n ≤ H.index := by
  have hcard : Nat.card psi.range=Nat.card F^Fintype.card n := by
    calc
      Nat.card psi.range=Nat.card (Multiplicative (n→F)) :=
        (Nat.card_congr (MonoidHom.ofInjective hpsi).toEquiv).symm
      _ = Nat.card (n→F) := Nat.card_congr (Multiplicative.toAdd : Multiplicative (n→F)≃(n→F))
      _ = _ := by rw [Nat.card_fun,Nat.card_eq_fintype_card (α:=n)]
  letI : Nonempty n := ⟨b⟩
  letI : Nontrivial psi.range := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard]
    exact Nat.one_lt_pow (by exact Fintype.card_pos.ne') (Finite.one_lt_card (α:=F)))
  have hh := CFSGConjugateSubgroupDegree.card_le_index_of_nonidentity_conjugate psi.range
    (range_nonidentity_conjugate psi b c hbc hrows) H hH
  exact hcard.symm.trans_le hh

end SymmetricSubgroupAsymptotics.CFSGSLRootParameterAction
