import SymmetricSubgroupAsymptotics.ElementaryQuotientRepresentation
import SymmetricSubgroupAsymptotics.PrimeRelativeHeadChain

/-! The representation on an actual elementary local normal section is
constructed from its original conjugation action and actual quotient
chart. Its kernel is the literal preceding local normal subgroup. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SymmetricSubgroupAsymptotics
variable {p : ℕ} [Fact p.Prime] {R H V : Type} [Group R] [Group H]
variable [AddCommGroup V] [Module (ZMod p) V]
variable (B L : Subgroup R) [B.Normal] [L.Normal]
variable (e : normalChainQuotient B L ≃* Multiplicative V)

def localChiefSectionMap : L→*Multiplicative V :=
  e.toMonoidHom.comp (normalChainMap B L)

theorem localChiefSectionMap_surjective : Function.Surjective (localChiefSectionMap B L e) :=
  e.surjective.comp (normalChainMap_surjective B L)

theorem localChiefSectionMap_kernel (l:L) : localChiefSectionMap B L e l=1 ↔ (l:R)∈B := by
  constructor
  · intro h
    have he : normalChainMap B L l=1 := e.injective (h.trans e.map_one.symm)
    exact (QuotientGroup.eq_one_iff (N:=B) (l:R)).mp (congrArg Subtype.val he)
  · intro h
    have he : normalChainMap B L l=1 := Subtype.ext
      ((QuotientGroup.eq_one_iff (N:=B) (l:R)).mpr h)
    change e (normalChainMap B L l)=1
    rw [he,map_one]

variable (β : H→*R)

def localChiefSectionAction : H→*MulAut L := (normalChainSourceAction L).comp β

theorem localChiefSection_kernel_stable (h:H) (l:L)
    (hl : localChiefSectionMap B L e l=1) :
    localChiefSectionMap B L e (localChiefSectionAction L β h l)=1 := by
  apply (localChiefSectionMap_kernel B L e _).mpr
  exact Subgroup.Normal.conj_mem inferInstance _
    ((localChiefSectionMap_kernel B L e l).mp hl) (β h)

def localChiefSectionRepresentation : Representation (ZMod p) H V :=
  elementaryQuotientRepresentation (p:=p) (localChiefSectionAction L β)
    (localChiefSectionMap B L e) (localChiefSectionMap_surjective B L e)
    (localChiefSection_kernel_stable B L e β)

theorem localChiefSectionRepresentation_equivariant (h:H) (l:L) :
    (localChiefSectionMap B L e (localChiefSectionAction L β h l)).toAdd=
      localChiefSectionRepresentation (p:=p) B L e β h (localChiefSectionMap B L e l).toAdd :=
  elementaryQuotientRepresentation_equivariant (p:=p) (localChiefSectionAction L β)
    (localChiefSectionMap B L e) (localChiefSectionMap_surjective B L e)
    (localChiefSection_kernel_stable B L e β) h l

end SymmetricSubgroupAsymptotics
