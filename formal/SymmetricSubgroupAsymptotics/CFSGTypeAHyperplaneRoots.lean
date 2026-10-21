import SymmetricSubgroupAsymptotics.CFSGTypeAPointRootCardinality
import SymmetricSubgroupAsymptotics.CFSGTypeAProjectiveTransvectionGeometry

/-! The actual hyperplane-root groups: all original transvections with
one fixed linear form and vectors in its original kernel. Their image
in PSL is injectively parametrized by that additive kernel and has the
same q^(n-1) cardinality as an original point-root group. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeAHyperplaneRoots
open Matrix Module LinearMap CFSGTypeAProjectivePointRoots
variable {F n : Type*} [Field F] [Fintype n] [DecidableEq n]

local instance hyperplaneRootParameterCommGroup (f : Dual F (n→F)) :
    CommGroup (Multiplicative (LinearMap.ker f)) := inferInstance

theorem transvectionSL_mul_vectors (f : Dual F (n→F)) {v w : n→F}
    (hv : f v=0) (hw : f w=0) :
    transvectionSL hv*transvectionSL hw=
      transvectionSL (show f (v+w)=0 by simp only [map_add,hv,hw,add_zero]) := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  rw [map_mul]
  apply LinearEquiv.ext
  intro x
  change (transvectionSL hv).toLin' ((transvectionSL hw).toLin' x)=
    (transvectionSL (show f (v+w)=0 by simp only [map_add,hv,hw,add_zero])).toLin' x
  simp only [transvectionSL_apply,map_add,map_smul,hw,zero_smul,smul_zero,add_zero,smul_add]
  abel

theorem transvectionSL_zero_vector (f : Dual F (n→F)) :
    transvectionSL (show f 0=0 from map_zero f)=1 := by
  apply Matrix.SpecialLinearGroup.toLin'_injective
  rw [map_one]
  apply LinearEquiv.ext
  intro x
  change (transvectionSL (show f 0=0 from map_zero f)).toLin' x=x
  simp only [transvectionSL_apply,smul_zero,add_zero]

def hyperplaneRootSLHom (f : Dual F (n→F)) :
    Multiplicative (LinearMap.ker f)→*SL (F:=F) (n:=n) where
  toFun v := transvectionSL (show f v.toAdd.val=0 from v.toAdd.property)
  map_one' := transvectionSL_zero_vector f
  map_mul' v w := (transvectionSL_mul_vectors f v.toAdd.property w.toAdd.property).symm

@[simp] theorem hyperplaneRootSLHom_apply (f : Dual F (n→F))
    (v : Multiplicative (LinearMap.ker f)) (x : n→F) :
    (hyperplaneRootSLHom f v).toLin' x=x+f x • v.toAdd.val :=
  transvectionSL_apply v.toAdd.property x

def hyperplaneRootHom (f : Dual F (n→F)) :
    Multiplicative (LinearMap.ker f)→*PSL (F:=F) (n:=n) :=
  (projection (F:=F) (n:=n)).comp (hyperplaneRootSLHom f)

omit [Fintype n] [DecidableEq n] in
private theorem exists_nonzero_value {f : Dual F (n→F)} (hf : f≠0) : ∃x,f x≠0 := by
  by_contra h
  simp only [not_exists,not_not] at h
  apply hf
  apply LinearMap.ext
  intro x
  exact h x

theorem hyperplaneRootSL_eq_one_of_mem_center {f : Dual F (n→F)} (hf : f≠0)
    (v : Multiplicative (LinearMap.ker f))
    (hv : hyperplaneRootSLHom f v∈Subgroup.center (SL (F:=F) (n:=n))) :
    hyperplaneRootSLHom f v=1 := by
  obtain ⟨r,_hr,he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hv
  obtain ⟨x,hx⟩ := exists_nonzero_value hf
  have hlin : (hyperplaneRootSLHom f v).toLin' x=r • x := by
    change Matrix.toLin' (hyperplaneRootSLHom f v).val x=r • x
    rw [←he,scalar_toLin'_apply]
  have hz : f v.toAdd.val=0 := v.toAdd.property
  have hh := congrArg f hlin
  simp only [hyperplaneRootSLHom_apply,map_add,map_smul,hz,smul_eq_mul,
    mul_zero,add_zero] at hh
  have hr : r=1 := by
    have hzero : (r-1)*f x=0 := by rw [sub_mul,one_mul,←hh,sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hx)
  apply Subtype.ext
  rw [←he,hr]
  exact map_one (Matrix.scalar n)

theorem hyperplaneRootHom_injective {f : Dual F (n→F)} (hf : f≠0) :
    Function.Injective (hyperplaneRootHom f) := by
  apply (MonoidHom.ker_eq_bot_iff (hyperplaneRootHom f)).mp
  apply bot_unique
  intro v hv
  have hc : hyperplaneRootSLHom f v∈Subgroup.center (SL (F:=F) (n:=n)) :=
    (QuotientGroup.eq_one_iff _).mp hv
  have he := hyperplaneRootSL_eq_one_of_mem_center hf v hc
  obtain ⟨x,hx⟩ := exists_nonzero_value hf
  have hh := congrArg (fun A : SL (F:=F) (n:=n) => A.toLin' x) he
  dsimp only at hh
  rw [map_one,hyperplaneRootSLHom_apply] at hh
  change x+f x • v.toAdd.val=x at hh
  have hz : f x • v.toAdd.val=0 := add_left_cancel (hh.trans (add_zero x).symm)
  have hv0 : v.toAdd=0 := by
    apply Subtype.ext
    exact (smul_eq_zero.mp hz).resolve_left hx
  apply (Subgroup.mem_bot).mpr
  exact congrArg Multiplicative.ofAdd hv0

def hyperplaneRoot (f : Dual F (n→F)) : Subgroup (PSL (F:=F) (n:=n)) :=
  (hyperplaneRootHom f).range

def hyperplaneRootEquiv {f : Dual F (n→F)} (hf : f≠0) :
    Multiplicative (LinearMap.ker f)≃*hyperplaneRoot f :=
  MonoidHom.ofInjective (hyperplaneRootHom_injective hf)

theorem hyperplaneRoot_card {f : Dual F (n→F)} (hf : f≠0) :
    Nat.card (hyperplaneRoot f)=Nat.card F^(Fintype.card n-1) := by
  have hd : Module.finrank F (LinearMap.ker f)=Fintype.card n-1 := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    rw [Module.finrank_fintype_fun_eq_card] at hh
    omega
  let e : Multiplicative (LinearMap.ker f)≃LinearMap.ker f :=
    ⟨Multiplicative.toAdd,Multiplicative.ofAdd,fun _ => rfl,fun _ => rfl⟩
  calc
    Nat.card (hyperplaneRoot f)=Nat.card (Multiplicative (LinearMap.ker f)) :=
      Nat.card_congr (hyperplaneRootEquiv hf).toEquiv.symm
    _=Nat.card (LinearMap.ker f) := Nat.card_congr e
    _=Nat.card F^Module.finrank F (LinearMap.ker f) :=
      Module.natCard_eq_pow_finrank (K:=F) (V:=LinearMap.ker f)
    _=Nat.card F^(Fintype.card n-1) := by rw [hd]

end SymmetricSubgroupAsymptotics.CFSGTypeAHyperplaneRoots
