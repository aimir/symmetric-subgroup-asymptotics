import SymmetricSubgroupAsymptotics.CFSGTypeATransvectionProductGeometry

/-! Pairwise rank-one products force a whole transvection family to
have one common centre or one common fixed hyperplane. This includes
empty families without choosing a nonexistent point or hyperplane. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGTypeATransvectionFamilies

section Coordinates
variable {ι A B : Type*}

theorem uniform_coordinate_of_pairwise (a : ι→A) (b : ι→B)
    (hp : ∀i j,a i=a j ∨ b i=b j) :
    (∀i j,a i=a j) ∨ (∀i j,b i=b j) := by
  classical
  by_cases ha : ∀i j,a i=a j
  · exact Or.inl ha
  · right
    obtain ⟨i,hi⟩ := not_forall.mp ha
    obtain ⟨j,hij⟩ := not_forall.mp hi
    have hbij : b i=b j := (hp i j).resolve_left hij
    have hk : ∀k,b k=b i := by
      intro k
      rcases hp k i with hki|hki
      · rcases hp k j with hkj|hkj
        · exact (hij (hki.symm.trans hkj)).elim
        · exact hkj.trans hbij.symm
      · exact hki
    intro k l
    exact (hk k).trans (hk l).symm
end Coordinates

open Module LinearMap Submodule CFSGTypeATransvectionProductGeometry
variable {F V ι : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem common_centre_or_axis_of_rank_one_products (f : ι→Dual F V) (v : ι→V)
    (hf : ∀i,f i≠0) (hv : ∀i,v i≠0)
    (hprod : ∀i j,∃h : Dual F V,∃u : V,
      (LinearMap.transvection (f i) (v i)).comp (LinearMap.transvection (f j) (v j))=
        LinearMap.transvection h u) :
    (∀i j,(F ∙ v i)=(F ∙ v j)) ∨ (∀i j,LinearMap.ker (f i)=LinearMap.ker (f j)) := by
  apply uniform_coordinate_of_pairwise (fun i => F ∙ v i) (fun i => LinearMap.ker (f i))
  intro i j
  obtain ⟨h,u,he⟩ := hprod i j
  exact product_transvection_common_centre_or_axis (hf i) (hf j) (hv i) (hv j) he

end SymmetricSubgroupAsymptotics.CFSGTypeATransvectionFamilies
