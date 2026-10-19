import SymmetricSubgroupAsymptotics.FiniteGeneratedKernelTable

/-! Literal finite coordinate receipts define a homomorphism on the actual
original kernel chart. A zero receipt identifies the same supplied denominator. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics.FiniteGeneratedKernelTable
variable {G I J A : Type} [Group G] [Group A] {source : J → G}
  (T : FiniteGeneratedKernelTable (I := I) source)
  (coordinate : I → A)
  (hone : coordinate T.identity=1)
  (hmul : ∀ i j, coordinate (T.multiply i j)=coordinate i*coordinate j)

def coordinateHom : T.subgroup →* A where
  toFun k := coordinate (T.chartEquiv.symm k)
  map_one' := by
    have hi : T.chartEquiv T.identity=1 := Subtype.ext T.identity_eq
    change coordinate (T.chartEquiv.symm 1)=1
    rw [←hi,T.chartEquiv.symm_apply_apply]
    exact hone
  map_mul' x y := by
    obtain ⟨i,rfl⟩ := T.chartEquiv.surjective x
    obtain ⟨j,rfl⟩ := T.chartEquiv.surjective y
    have hij : T.chartEquiv (T.multiply i j)=T.chartEquiv i*T.chartEquiv j :=
      Subtype.ext (T.multiply_eq i j)
    change coordinate (T.chartEquiv.symm (T.chartEquiv i*T.chartEquiv j))=
      coordinate (T.chartEquiv.symm (T.chartEquiv i))*
        coordinate (T.chartEquiv.symm (T.chartEquiv j))
    rw [←hij,T.chartEquiv.symm_apply_apply,T.chartEquiv.symm_apply_apply,
      T.chartEquiv.symm_apply_apply]
    exact hmul i j

theorem coordinateHom_chart (i : I) :
    T.coordinateHom coordinate hone hmul (T.chartEquiv i)=coordinate i := by
  change coordinate (T.chartEquiv.symm (T.chartEquiv i))=coordinate i
  rw [T.chartEquiv.symm_apply_apply]

theorem coordinateHom_ker (N : Subgroup G)
    (hzero : ∀ i, coordinate i=1 ↔ T.element i∈N) :
    (T.coordinateHom coordinate hone hmul).ker=N.subgroupOf T.subgroup := by
  ext k
  obtain ⟨i,rfl⟩ := T.chartEquiv.surjective k
  change T.coordinateHom coordinate hone hmul (T.chartEquiv i)=1 ↔
    (T.chartEquiv i).val∈N
  rw [T.coordinateHom_chart]
  exact hzero i

end SymmetricSubgroupAsymptotics.FiniteGeneratedKernelTable
