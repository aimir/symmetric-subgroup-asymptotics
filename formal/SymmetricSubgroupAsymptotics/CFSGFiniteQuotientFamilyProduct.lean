import Mathlib.GroupTheory.NoncommPiCoprod

/-! A fixed ordered product lifts the coproduct of a finite family whose
IMAGES commute. The factors themselves need not commute. This is the
elementary quotient-to-remainder step used in actual height collection. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGFiniteQuotientFamilyProduct
variable {I G Q : Type*} [Fintype I] [Group G] [Group Q]

def orderedFamilyProduct (f : I→G) : G := by
  classical
  exact ((Finset.univ : Finset I).toList.map f).prod

theorem orderedFamilyProduct_image {P : I→Type*} [∀i,Group (P i)]
    (q : G→*Q) (f : ∀i,P i→*G)
    (hc : Pairwise (fun i j=>∀a b,Commute (q (f i a)) (q (f j b)))) (a : ∀i,P i) :
    q (orderedFamilyProduct (fun i=>f i (a i)))=
      MonoidHom.noncommPiCoprod (fun i=>q.comp (f i)) hc a := by
  classical
  rw [orderedFamilyProduct,map_list_prod,List.map_map]
  symm
  change Finset.univ.noncommProd (fun i=>q (f i (a i)))
    (fun i _ j _ hij=>hc hij (a i) (a j)) = _
  simpa only [Finset.toList_toFinset,Function.comp_apply] using
    (Finset.noncommProd_toFinset (Finset.univ.toList) (fun i=>q (f i (a i)))
      (fun i _ j _ hij=>hc hij (a i) (a j)) (Finset.nodup_toList _))

theorem exists_ordered_factor_and_kernel {P : I→Type*} [∀i,Group (P i)]
    (q : G→*Q) (f : ∀i,P i→*G)
    (hc : Pairwise (fun i j=>∀a b,Commute (q (f i a)) (q (f j b))))
    (x : G) (hx : q x∈(MonoidHom.noncommPiCoprod (fun i=>q.comp (f i)) hc).range) :
    ∃a : ∀i,P i,∃y : G,y∈q.ker ∧
      x=orderedFamilyProduct (fun i=>f i (a i))*y := by
  obtain ⟨a,ha⟩ := hx
  let p := orderedFamilyProduct (fun i=>f i (a i))
  have hp : q p=q x := (orderedFamilyProduct_image q f hc a).trans ha
  refine ⟨a,p⁻¹*x,?_,?_⟩
  · change q (p⁻¹*x)=1
    rw [map_mul,map_inv,hp,inv_mul_cancel]
  · dsimp only [p]
    exact (mul_inv_cancel_left _ _).symm

end SymmetricSubgroupAsymptotics.CFSGFiniteQuotientFamilyProduct
