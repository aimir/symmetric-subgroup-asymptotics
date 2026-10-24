import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Group

/-! Unique actual Bruhat factors detect diagonal-normalizing elements.
No torus recognition or Weyl census is part of this abstract statement. -/
set_option autoImplicit false
set_option Elab.async false
namespace SymmetricSubgroupAsymptotics.CFSGUniqueBruhatDiagonalNormalizer
variable {G : Type*} [Group G]

def factorMap (U D R : Subgroup G) (w : G) : U×D×R → G :=
  fun z=>z.1.val*z.2.1.val*w*z.2.2.val

private theorem conjugate_mem (H : Subgroup G) {g x : G}
    (hg : g∈Subgroup.normalizer (H : Set G)) (hx : x∈H) : g*x*g⁻¹∈H :=
  (Subgroup.mem_normalizer_iff.mp hg x).mp hx

theorem eq_diagonal_word_of_normalizes_diagonal (U D R : Subgroup G) (w g u d v : G)
    (hDU : D≤Subgroup.normalizer (U : Set G))
    (hDR : D≤Subgroup.normalizer (R : Set G)) (hRU : R≤U)
    (hw : w∈Subgroup.normalizer (D : Set G))
    (hg : g∈Subgroup.normalizer (D : Set G))
    (hunique : Function.Injective (factorMap U D R w))
    (hfixed : ∀ x∈U,(∀ t∈D,t*x*t⁻¹=x) → x=1)
    (hu : u∈U) (hd : d∈D) (hv : v∈R) (hprod : g=u*d*w*v) : g=d*w := by
  have hcoords (t : G) (ht : t∈D) :
      t*u*t⁻¹=u ∧ (g⁻¹*t*g)*v*(g⁻¹*t*g)⁻¹=v := by
    let tp := g⁻¹*t*g
    have htp : tp∈D := by
      have he := conjugate_mem D ((Subgroup.normalizer (D : Set G)).inv_mem hg) ht
      simpa only [inv_inv] using he
    have hu' : t*u*t⁻¹∈U := conjugate_mem U (hDU ht) hu
    have hv' : tp*v*tp⁻¹∈R := conjugate_mem R (hDR htp) hv
    have hd' : t*d*(w*tp⁻¹*w⁻¹)∈D :=
      D.mul_mem (D.mul_mem ht hd) (conjugate_mem D hw (D.inv_mem htp))
    let z : U×D×R :=
      (⟨t*u*t⁻¹,hu'⟩,⟨t*d*(w*tp⁻¹*w⁻¹),hd'⟩,⟨tp*v*tp⁻¹,hv'⟩)
    let z0 : U×D×R := (⟨u,hu⟩,⟨d,hd⟩,⟨v,hv⟩)
    have he : factorMap U D R w z=factorMap U D R w z0 := by
      change (t*u*t⁻¹)*(t*d*(w*tp⁻¹*w⁻¹))*w*(tp*v*tp⁻¹)=u*d*w*v
      calc
        _=t*(u*d*w*v)*tp⁻¹ := by group
        _=t*g*tp⁻¹ := by rw [←hprod]
        _=g := by dsimp only [tp];group
        _=u*d*w*v := hprod
    have hz := hunique he
    exact ⟨congrArg (fun a : U×D×R=>a.1.val) hz,
      congrArg (fun a : U×D×R=>a.2.2.val) hz⟩
  have hu1 : u=1 := hfixed u hu (fun t ht=>(hcoords t ht).1)
  have hv1 : v=1 := by
    apply hfixed v (hRU hv)
    intro s hs
    have ht : g*s*g⁻¹∈D := conjugate_mem D hg hs
    have he := (hcoords (g*s*g⁻¹) ht).2
    have hc : g⁻¹*(g*s*g⁻¹)*g=s := by group
    rwa [hc] at he
  rw [hprod,hu1,hv1,one_mul,mul_one]

end SymmetricSubgroupAsymptotics.CFSGUniqueBruhatDiagonalNormalizer
