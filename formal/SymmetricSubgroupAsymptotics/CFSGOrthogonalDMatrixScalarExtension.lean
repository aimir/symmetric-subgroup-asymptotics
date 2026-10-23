import SymmetricSubgroupAsymptotics.CFSGOrthogonalDBinaryElements

/-! Scalar extension of the independently defined literal D matrix-root
group. Every parameter is mapped by the specified field homomorphism;
the source and target groups are linked by their defining root closure. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixScalarExtension
open CFSGOrthogonalDSerreMatrices CFSGOrthogonalDBinaryElements
variable {F K : Type} [Field F] [Field K]

def scalarUnitHom (f : F →+* K) (r : ℕ) : (Mat F r)ˣ →* (Mat K r)ˣ :=
  Units.map (f.mapMatrix.toMonoidHom)

theorem scalarUnitHom_val (f : F →+* K) (r : ℕ) (g : (Mat F r)ˣ) :
    (scalarUnitHom f r g : Mat K r) = (g : Mat F r).map f := rfl

theorem scalarUnitHom_root (f : F →+* K) (r : ℕ) (neg : Bool)
    (i : Fin r) (a : F) :
    scalarUnitHom f r (rootTransvection F r neg i a) =
      rootTransvection K r neg i (f a) := by
  apply Units.ext
  rw [scalarUnitHom_val, rootTransvection_val, rootTransvection_val]
  have hm : (1 + a • rootMatrix F r neg i).map f =
      1 + f a • f.mapMatrix (rootMatrix F r neg i) := by
    ext x y
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul]
    congr 1
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  rw [hm, map_rootMatrix]

theorem scalarUnitHom_maps_elementary (f : F →+* K) (r : ℕ) :
    elementaryRootGroup F r ≤ (elementaryRootGroup K r).comap (scalarUnitHom f r) := by
  apply (Subgroup.closure_le _).mpr
  rintro g ⟨neg, i, a, rfl⟩
  change scalarUnitHom f r (rootTransvection F r neg i a) ∈ elementaryRootGroup K r
  rw [scalarUnitHom_root]
  exact rootTransvection_mem K r neg i (f a)

def scalarElementaryHom (f : F →+* K) (r : ℕ) :
    elementaryRootGroup F r →* elementaryRootGroup K r where
  toFun g := ⟨scalarUnitHom f r g.val, scalarUnitHom_maps_elementary f r g.property⟩
  map_one' := Subtype.ext ((scalarUnitHom f r).map_one)
  map_mul' g h := Subtype.ext ((scalarUnitHom f r).map_mul g.val h.val)

theorem scalarElementaryHom_root (f : F →+* K) (r : ℕ) (neg : Bool)
    (i : Fin r) (a : F) :
    scalarElementaryHom f r (rootElement F r neg i a) =
      rootElement K r neg i (f a) :=
  Subtype.ext (scalarUnitHom_root f r neg i a)

theorem scalarUnitHom_injective (f : F →+* K) (r : ℕ) :
    Function.Injective (scalarUnitHom f r) := by
  intro g h he
  apply Units.ext
  ext i j
  apply f.injective
  exact congrArg (fun u : (Mat K r)ˣ => (u : Mat K r) i j) he

end SymmetricSubgroupAsymptotics.CFSGOrthogonalDMatrixScalarExtension
