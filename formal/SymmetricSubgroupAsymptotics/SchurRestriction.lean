import SymmetricSubgroupAsymptotics.SchurCapacity

/-!
# Schur capacity under a surjective acting-algebra map

Changing the acting algebra along a surjection preserves the actual
simple submodule lattice and every simple-source Hom space. In particular,
normalizer inflation introduces no new target capacity.
-/

set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics
universe u
variable {k R T A : Type u} [Field k] [Ring R] [Ring T]
    [Algebra k R] [Algebra k T] [AddCommGroup A]
    [Module R A] [Module T A] [Module k A]
    [IsScalarTower k R A] [IsScalarTower k T A]
    (φ : R →+* T) (hφ : Function.Surjective φ)
    (ha : ∀ r : R, ∀ a : A, r • a = φ r • a)

/-- The literal submodule lattice is unchanged by a surjective action map. -/
def schurSubmoduleOrderIso : Submodule R A ≃o Submodule T A where
  toFun S :=
    { __ := S.toAddSubmonoid
      smul_mem' t a ha' := by
        obtain ⟨r,rfl⟩ := hφ t
        rw [← ha]
        exact S.smul_mem r ha' }
  invFun S :=
    { __ := S.toAddSubmonoid
      smul_mem' r a ha' := by rw [ha]; exact S.smul_mem (φ r) ha' }
  left_inv S := by ext; rfl
  right_inv S := by ext; rfl
  map_rel_iff' := Iff.rfl

/-- Corresponding simple submodules remain simple for the quotient action. -/
theorem schurSubmodule_isSimple (S : Submodule R A) [IsSimpleModule R S] :
    IsSimpleModule T (schurSubmoduleOrderIso φ hφ ha S) := by
  rw [isSimpleModule_iff_isAtom]
  exact ((schurSubmoduleOrderIso φ hφ ha).isAtom_iff S).mpr
    (isSimpleModule_iff_isAtom.mp inferInstance)

/-- Actual Hom maps from a retained submodule are unchanged under
surjective change of the acting algebra. -/
def schurSubmoduleHomEquiv (S : Submodule R A) :
    (S →ₗ[R] A) ≃ₗ[k] ((schurSubmoduleOrderIso φ hφ ha S) →ₗ[T] A) where
  toFun f :=
    { toFun := fun x ↦ f ⟨x.1, x.2⟩
      map_add' x y := f.map_add _ _
      map_smul' t x := by
        obtain ⟨r,rfl⟩ := hφ t
        change f ⟨φ r • x.1, _⟩ = φ r • f ⟨x.1,x.2⟩
        have hx : (⟨φ r • x.1, (φ r • x).property⟩ : S) = r • (⟨x.1,x.2⟩ : S) :=
          Subtype.ext (ha r x.1).symm
        rw [hx, f.map_smul, ha] }
  invFun f :=
    { toFun := fun x ↦ f ⟨x.1,x.2⟩
      map_add' x y := f.map_add _ _
      map_smul' r x := by
        change f ⟨r • x.1, _⟩ = r • f ⟨x.1,x.2⟩
        have hx : (⟨r • x.1, (r • x).property⟩ : schurSubmoduleOrderIso φ hφ ha S) =
            φ r • (⟨x.1,x.2⟩ : schurSubmoduleOrderIso φ hφ ha S) :=
          Subtype.ext (ha r x.1)
        rw [hx, f.map_smul, ha] }
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by ext x; rfl

/-- The original field dimensions of the same literal submodule agree. -/
def schurSubmoduleFieldEquiv (S : Submodule R A) :
    S ≃ₗ[k] schurSubmoduleOrderIso φ hφ ha S where
  toFun x := ⟨x.1,x.2⟩
  invFun x := ⟨x.1,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include φ hφ ha in
/-- The capacity of the original quotient target also bounds the
inflated target's capacity; no action on the source is descended. -/
theorem schurCapacity_le_of_surjective_action [FiniteDimensional k A] :
    schurCapacity k R A ≤ schurCapacity k T A := by
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨S,hS,rfl⟩)
  · exact schurCapacity_nonneg
  · letI := hS
    haveI := schurSubmodule_isSimple φ hφ ha S
    rw [(schurSubmoduleHomEquiv φ hφ ha S).finrank_eq,
      (schurSubmoduleFieldEquiv φ hφ ha S).finrank_eq]
    exact le_csSup schurCapacity_bddAbove
      (Set.mem_insert_of_mem _ ⟨_,inferInstance,rfl⟩)

include φ hφ ha in
/-- Surjective inflation preserves the full intrinsic capacity exactly. -/
theorem schurCapacity_eq_of_surjective_action [FiniteDimensional k A] :
    schurCapacity k R A = schurCapacity k T A := by
  apply le_antisymm (schurCapacity_le_of_surjective_action φ hφ ha)
  apply csSup_le (Set.insert_nonempty _ _)
  rintro x (rfl | ⟨S,hS,rfl⟩)
  · exact schurCapacity_nonneg
  · let e := schurSubmoduleOrderIso φ hφ ha
    let S' := e.symm S
    have hS' : IsSimpleModule R S' := by
      rw [isSimpleModule_iff_isAtom]
      exact (e.isAtom_iff S').mp (by simpa only [S', OrderIso.apply_symm_apply] using
        (isSimpleModule_iff_isAtom.mp hS))
    letI := hS'
    have hcard := (schurSubmoduleHomEquiv (k := k) φ hφ ha S').finrank_eq
    have hdim := (schurSubmoduleFieldEquiv (k := k) φ hφ ha S').finrank_eq
    have he : e S' = S := e.apply_symm_apply S
    change Module.finrank k (S' →ₗ[R] A) = Module.finrank k (e S' →ₗ[T] A) at hcard
    change Module.finrank k S' = Module.finrank k (e S') at hdim
    rw [he] at hcard hdim
    rw [← hcard, ← hdim]
    exact le_csSup schurCapacity_bddAbove
      (Set.mem_insert_of_mem _ ⟨S',inferInstance,rfl⟩)

end SymmetricSubgroupAsymptotics
