import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Basic

/-! Actual conjugation lifts of generators suffice to realize an
entire parameter action. No homomorphism from the acting group into
the ambient group is required: the literal intertwining pairs form a
subgroup of their product. This keeps all relations and possible
central discrepancies in the original ambient group. -/
set_option autoImplicit false
namespace SymmetricSubgroupAsymptotics.CFSGConjugationActionGraph
variable {P L G : Type*} [Group P] [Group L] [Group G]
    (rho : L →* MulAut P) (psi : P →* G)

def intertwiningPairs : Subgroup (L×G) where
  carrier := {u | ∀ p, u.2*psi p=psi (rho u.1 p)*u.2}
  one_mem' := by
    intro p
    change (1:G)*psi p=psi (rho (1:L) p)*(1:G)
    rw [map_one,MulAut.one_apply,one_mul,mul_one]
  mul_mem' := by
    intro a b ha hb p
    change (a.2*b.2)*psi p=psi (rho (a.1*b.1) p)*(a.2*b.2)
    rw [map_mul,MulAut.mul_apply]
    calc
      (a.2*b.2)*psi p=a.2*(b.2*psi p) := mul_assoc _ _ _
      _ = a.2*(psi (rho b.1 p)*b.2) := by rw [hb p]
      _ = (a.2*psi (rho b.1 p))*b.2 := (mul_assoc _ _ _).symm
      _ = (psi (rho a.1 (rho b.1 p))*a.2)*b.2 := by rw [ha (rho b.1 p)]
      _ = psi (rho a.1 (rho b.1 p))*(a.2*b.2) := mul_assoc _ _ _
  inv_mem' := by
    intro a ha p
    have hh := ha ((rho a.1).symm p)
    rw [MulEquiv.apply_symm_apply] at hh
    have he := congrArg (fun z:G => a.2⁻¹*z*a.2⁻¹) hh
    dsimp only at he
    change a.2⁻¹*psi p=psi (rho (a.1⁻¹) p)*a.2⁻¹
    simpa only [map_inv,MulAut.coe_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel,mul_one]
      using he.symm

theorem lift_every_of_generators (S : Set L) (hgen : Subgroup.closure S=⊤)
    (hS : ∀ a∈S, ∃ g:G, ∀ p, g*psi p=psi (rho a p)*g) (a:L) :
    ∃ g:G, ∀ p, g*psi p=psi (rho a p)*g := by
  let J := (intertwiningPairs rho psi).map (MonoidHom.fst L G)
  have hSJ : S⊆J := by
    intro x hx
    obtain ⟨g,hg⟩ := hS x hx
    exact ⟨(x,g),hg,rfl⟩
  have hle : Subgroup.closure S≤J := (Subgroup.closure_le J).2 hSJ
  rw [hgen] at hle
  have ha : a∈J := hle (Subgroup.mem_top a)
  obtain ⟨u,hu,he⟩ := ha
  change u.1=a at he
  refine ⟨u.2,?_⟩
  change ∀ p, u.2*psi p=psi (rho u.1 p)*u.2 at hu
  rw [he] at hu
  exact hu

theorem conjugate_of_generators (S : Set L) (hgen : Subgroup.closure S=⊤)
    (hS : ∀ a∈S, ∃ g:G, ∀ p, g*psi p=psi (rho a p)*g)
    (x y:P) (hxy : ∃ a:L,rho a x=y) : ∃ g:G,g*psi x*g⁻¹=psi y := by
  obtain ⟨a,ha⟩ := hxy
  obtain ⟨g,hg⟩ := lift_every_of_generators rho psi S hgen hS a
  refine ⟨g,?_⟩
  rw [hg x,ha,mul_assoc,mul_inv_cancel,mul_one]

theorem range_nonidentity_conjugate (S : Set L) (hgen : Subgroup.closure S=⊤)
    (hS : ∀ a∈S, ∃ g:G, ∀ p, g*psi p=psi (rho a p)*g)
    (htrans : ∀ x y:P,x≠1→y≠1→∃ a:L,rho a x=y)
    (a b:psi.range) (ha:a≠1) (hb:b≠1) :
    ∃ g:G,g*(a:G)*g⁻¹=(b:G) := by
  obtain ⟨x,hx⟩ := a.property
  obtain ⟨y,hy⟩ := b.property
  have hx1 : x≠1 := by
    intro he
    apply ha
    apply Subtype.ext
    simpa only [he,map_one] using hx.symm
  have hy1 : y≠1 := by
    intro he
    apply hb
    apply Subtype.ext
    simpa only [he,map_one] using hy.symm
  obtain ⟨g,hg⟩ := conjugate_of_generators rho psi S hgen hS x y (htrans x y hx1 hy1)
  exact ⟨g,by rw [←hx,←hy]; exact hg⟩

end SymmetricSubgroupAsymptotics.CFSGConjugationActionGraph
