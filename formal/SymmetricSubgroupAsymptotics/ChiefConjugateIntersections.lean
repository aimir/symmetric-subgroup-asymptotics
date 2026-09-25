import SymmetricSubgroupAsymptotics.ChiefNormalStep

/-! Literal ambient-normal chief intersections from an original local
coordinate. Their monotonicity and normality are proved, and the top
intersection is the complete original source subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {A R : Type} [Group A] [Group R]
variable (N : Subgroup A) [N.Normal] (θ : N→*R)

def localChiefIntersection (L : Subgroup R) : Subgroup A :=
  (⨅a:A,L.comap (θ.comp (MulAut.conjNormal a).toMonoidHom)).map N.subtype

theorem localChiefIntersection_le (L : Subgroup R) : localChiefIntersection N θ L≤N := by
  rintro _ ⟨n,_,rfl⟩
  exact n.2

theorem mem_localChiefIntersection (L : Subgroup R) (n:N) :
    (n:A)∈localChiefIntersection N θ L ↔ ∀a:A,θ (MulAut.conjNormal a n)∈L := by
  constructor
  · rintro ⟨m,hm,he⟩
    have hmn : m=n := Subtype.ext he
    subst m
    exact fun a=>(Subgroup.mem_iInf.mp hm) a
  · intro h
    refine ⟨n,?_,rfl⟩
    exact Subgroup.mem_iInf.mpr h

instance localChiefIntersection_normal (L : Subgroup R) : (localChiefIntersection N θ L).Normal := by
  constructor
  intro x hx g
  have hxN := localChiefIntersection_le N θ L hx
  let n : N := ⟨x,hxN⟩
  have hn := (mem_localChiefIntersection N θ L n).mp hx
  change (MulAut.conjNormal g n:A)∈localChiefIntersection N θ L
  apply (mem_localChiefIntersection N θ L (MulAut.conjNormal g n)).mpr
  intro a
  have h := hn (a*g)
  simpa only [map_mul,MulAut.mul_apply] using h

theorem localChiefIntersection_mono {L M : Subgroup R} (hLM : L≤M) :
    localChiefIntersection N θ L≤localChiefIntersection N θ M := by
  intro x hx
  let n : N := ⟨x,localChiefIntersection_le N θ L hx⟩
  exact (mem_localChiefIntersection N θ M n).mpr (fun a=>
    hLM ((mem_localChiefIntersection N θ L n).mp hx a))

theorem localChiefIntersection_top : localChiefIntersection N θ ⊤=N := by
  apply le_antisymm (localChiefIntersection_le N θ ⊤)
  intro n hn
  exact (mem_localChiefIntersection N θ ⊤ ⟨n,hn⟩).mpr (fun _=>Subgroup.mem_top _)

theorem localChiefIntersection_bot
    (hsep : ∀n:N,(∀a:A,θ (MulAut.conjNormal a n)=1)→n=1) :
    localChiefIntersection N θ ⊥=⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  let n : N := ⟨x,localChiefIntersection_le N θ ⊥ hx⟩
  have hn : ∀a:A,θ (MulAut.conjNormal a n)=1 :=
    (mem_localChiefIntersection N θ ⊥ n).mp hx
  have he := congrArg Subtype.val (hsep n hn)
  exact he

end SymmetricSubgroupAsymptotics
