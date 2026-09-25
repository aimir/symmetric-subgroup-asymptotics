import SymmetricSubgroupAsymptotics.SchurRepresentation
import SymmetricSubgroupAsymptotics.Non2SharedC3Audit

/-!
# Fractional Schur audit on the actual shared-C3 action

The audit keeps the binary ground field. The scalar action factors through
the genuine F4 algebra, so its fractional Schur capacity is m, even though
the target has binary dimension 2m. The independent translation factor is
still present in every actual fixed-top homomorphism count.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics
universe u
variable {k K A : Type u} [Field k] [Field K] [Algebra k K]
    [AddCommGroup A] [Module k A] [Module K A] [IsScalarTower k K A]

/-- A field extension acting by scalars has its exact fractional capacity,
computed over the original ground field. -/
theorem schurCapacity_extension_eq_dimension [FiniteDimensional k K]
    [FiniteDimensional k A] :
    schurCapacity k K A = Module.finrank K A := by
  letI : FiniteDimensional K A := Module.Finite.of_restrictScalars_finite k K A
  have hK : (0 : ℝ) < Module.finrank k K := by
    exact_mod_cast (Module.finrank_pos (R := k) (M := K))
  apply le_antisymm
  · apply csSup_le (Set.insert_nonempty _ _)
    rintro x (rfl | ⟨S,hS,rfl⟩)
    · positivity
    · letI : FiniteDimensional k S := FiniteDimensional.of_injective
        (S.subtype.restrictScalars k) S.subtype_injective
      letI : FiniteDimensional K S := Module.Finite.of_restrictScalars_finite k K S
      have hh : Module.finrank k (S →ₗ[K] A) =
          Module.finrank K S * Module.finrank k A :=
        Module.finrank_linearMap K k S A
      have hs : Module.finrank k S = Module.finrank k K * Module.finrank K S :=
        (Module.finrank_mul_finrank k K S).symm
      have ha : Module.finrank k A = Module.finrank k K * Module.finrank K A :=
        (Module.finrank_mul_finrank k K A).symm
      rw [hh,hs,ha, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
      by_cases h : Module.finrank K S = 0
      · simp [h]
      · have hr : (Module.finrank K S : ℝ) ≠ 0 := by exact_mod_cast h
        have he : ((Module.finrank K S : ℝ) *
            ((Module.finrank k K : ℝ) * Module.finrank K A)) /
            ((Module.finrank k K : ℝ) * Module.finrank K S) = Module.finrank K A := by
          field_simp
        exact he.le
  · have hb := schurHom_finrank_le_capacity (k := k) (R := K) (A := A) (M := K)
    rw [Module.finrank_linearMap, Module.finrank_self, one_mul,
      ← Module.finrank_mul_finrank k K A, Nat.cast_mul] at hb
    nlinarith

/-- The scalar unit action viewed over the original ground field. -/
def scalarUnitGroundRepresentation : Representation k Kˣ A where
  toFun t := (Algebra.lsmul k k A) (t : K)
  map_one' := by ext a; simp
  map_mul' s t := by ext a; simp [smul_smul]

/-- The genuine scalar character from the group algebra is surjective. -/
theorem scalarUnitAlgebra_surjective : Function.Surjective
    ((MonoidAlgebra.lift k K Kˣ) (Units.coeHom K)) := by
  intro a
  by_cases ha : a = 0
  · subst a; exact ⟨0, map_zero _⟩
  · refine ⟨MonoidAlgebra.single (Units.mk0 a ha) 1, ?_⟩
    simp

/-- The binary/ground-field Schur constant sees the extension-field
multiplicity, not the ambient ground-field dimension. -/
theorem scalarUnitGround_schurCapacity [FiniteDimensional k K]
    [FiniteDimensional k A] :
    representationSchurCapacity (scalarUnitGroundRepresentation (k := k) (K := K) (A := A)) =
      Module.finrank K A := by
  let σ := scalarUnitGroundRepresentation (k := k) (K := K) (A := A)
  letI : Module K σ.asModule := ‹Module K A›
  letI : IsScalarTower k K σ.asModule := ‹IsScalarTower k K A›
  have ha : ∀ r : k[Kˣ], ∀ a : σ.asModule,
      r • a = ((MonoidAlgebra.lift k K Kˣ) (Units.coeHom K)) r • a := by
    intro r a
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [add_smul,hx,hy]
    | single g t =>
      rw [Representation.single_smul, MonoidAlgebra.lift_single]
      change t • ((g : K) • a) = (t • (g : K)) • a
      exact (smul_assoc t (g : K) a).symm
  calc
    representationSchurCapacity σ = schurCapacity k K σ.asModule :=
      schurCapacity_eq_of_surjective_action
        ((MonoidAlgebra.lift k K Kˣ) (Units.coeHom K)).toRingHom
        scalarUnitAlgebra_surjective ha
    _ = Module.finrank K A := schurCapacity_extension_eq_dimension

/-- The actual F4 scalar C3 target has fractional binary Schur capacity m. -/
theorem sharedC3_binary_schurCapacity (m : ℕ) :
    representationSchurCapacity
      (scalarUnitGroundRepresentation (k := ZMod 2) (K := SharedF4)
        (A := Fin m → SharedF4)) = m := by
  rw [scalarUnitGround_schurCapacity, Module.finrank_fin_fun]

/-- Its source has the exact binary dimension 2r. -/
theorem sharedC3_binary_source_finrank (r : ℕ) :
    Module.finrank (ZMod 2) (Fin r → SharedF4) = 2*r := by
  rw [← Module.finrank_mul_finrank (ZMod 2) SharedF4 (Fin r → SharedF4),
    Module.finrank_fin_fun, GaloisField.finrank 2 (by norm_num : (2 : ℕ) ≠ 0)]

/-- Mandatory shared-source audit: the Schur exponent and the full
translation contribution agree with the already proved actual lift count. -/
theorem sharedC3_fractional_schur_audit (r m : ℕ) :
    representationSchurCapacity
      (scalarUnitGroundRepresentation (k := ZMod 2) (K := SharedF4)
        (A := Fin m → SharedF4)) = m ∧
    Nat.card (SharedC3FixedTopHom r m) = 4^m * 2^(2*m*r) := by
  refine ⟨sharedC3_binary_schurCapacity m, ?_⟩
  rw [sharedC3_fixedTopHom_card]
  have he : 2^(2*m*r) = 4^(m*r) := by
    rw [show 2*m*r = 2*(m*r) by ring, pow_mul]
    norm_num
  rw [he, ← pow_add]
  congr 1
  ring

/-- The two marks use the same source and each keeps its own translation
factor. Their Schur capacities add; no independent source is substituted. -/
theorem sharedC3_double_fractional_schur_audit (r m₁ m₂ : ℕ) :
    representationSchurCapacity
      (scalarUnitGroundRepresentation (k := ZMod 2) (K := SharedF4)
        (A := Fin m₁ → SharedF4)) +
    representationSchurCapacity
      (scalarUnitGroundRepresentation (k := ZMod 2) (K := SharedF4)
        (A := Fin m₂ → SharedF4)) = m₁ + m₂ ∧
    Nat.card (SharedC3FixedTopHom r m₁ × SharedC3FixedTopHom r m₂) =
      (4^m₁ * 4^m₂) * 2^(2*(m₁+m₂)*r) := by
  constructor
  · rw [sharedC3_binary_schurCapacity,sharedC3_binary_schurCapacity]
  · rw [Nat.card_prod, (sharedC3_fractional_schur_audit r m₁).2,
      (sharedC3_fractional_schur_audit r m₂).2]
    rw [show 2*(m₁+m₂)*r = 2*m₁*r + 2*m₂*r by ring, pow_add]
    ring

/-- For trivial actions equivariance imposes no equation on the linear
map. This prevents odd order by itself from being used as capacity loss. -/
def trivialIntertwiningEquiv {k G V W : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] :
    (Representation.trivial k G V).IntertwiningMap (Representation.trivial k G W) ≃ₗ[k]
      (V →ₗ[k] W) where
  toFun f := f.toLinearMap
  invFun f := f.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ ↦ rfl)
  left_inv f := by apply Representation.IntertwiningMap.ext; rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The capacity itself is full target dimension for a trivial action. -/
theorem trivial_representationSchurCapacity {k G V : Type u} [Field k] [Group G]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V] :
    representationSchurCapacity (Representation.trivial k G V) = Module.finrank k V := by
  apply le_antisymm
  · calc
      _ ≤ (Module.finrank k (Representation.trivial k G V).asModule : ℝ) :=
        schurCapacity_le_dimension
      _ = _ := by rw [(Representation.trivial k G V).asModuleEquiv.finrank_eq]
  · have h := intertwiningMap_finrank_le_schur
      (Representation.trivial k G k) (Representation.trivial k G V)
    rw [trivialIntertwiningEquiv.finrank_eq,Module.finrank_linearMap,
      Module.finrank_self,one_mul,Nat.cast_one,mul_one] at h
    exact h

/-- The literal odd C3 group acting trivially attains the full t²
binary exponent. The same Schur theorem accommodates this fixture. -/
theorem trivialC3_intertwining_full_capacity (t : ℕ) :
    Nat.card ((Representation.trivial (ZMod 2) SharedF4ˣ (Fin t → ZMod 2)).IntertwiningMap
      (Representation.trivial (ZMod 2) SharedF4ˣ (Fin t → ZMod 2))) = 2^(t*t) := by
  rw [Nat.card_congr trivialIntertwiningEquiv.toEquiv]
  simpa using finiteField_linearMap_card (ZMod 2) t t

end SymmetricSubgroupAsymptotics
