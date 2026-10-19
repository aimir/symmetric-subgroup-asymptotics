import SymmetricSubgroupAsymptotics.BinaryQuadraticField
import SymmetricSubgroupAsymptotics.RepresentationDualSubquotientGenerators

/-! Actual scalar coefficients cost no extra binary generators when
omega is itself an actual acting element. This is the restriction-of-
scalars bridge for the literal polynomial/PID witness route. -/
set_option autoImplicit false
noncomputable section
open scoped MonoidAlgebra
namespace SymmetricSubgroupAsymptotics.BinaryCubicScalarGeneratorTransfer
open BinaryQuadraticField (Scalar omega)

variable {H V : Type} [Group H] [AddCommGroup V]
  [Module (ZMod 2) V] [Module Scalar V] [IsScalarTower (ZMod 2) Scalar V]
  (rho2 : Representation (ZMod 2) H V) (rho4 : Representation Scalar H V)
  (hact : ∀ h v, rho4 h v=rho2 h v)
  (k : H) (hk : ∀ v, rho2 k v=omega • v)

/-- The actual binary carrier is already scalar closed because its
omega action is the action of k, not an externally supplied scalar. -/
def scalarUpgrade (S : Subrepresentation rho2) : Subrepresentation rho4 where
  toSubmodule :=
    { carrier := S
      zero_mem' := S.toSubmodule.zero_mem
      add_mem' := S.toSubmodule.add_mem
      smul_mem' a v hv := by
        have he : a • v=a.re • v+a.im • (omega • v) := by
          calc
            a • v=(a.re • (1 : Scalar)+a.im • omega) • v :=
              congrArg (fun z : Scalar => z • v) (BinaryQuadraticField.scalar_eq a)
            _=a.re • v+a.im • (omega • v) := by
              simp only [add_smul,smul_assoc,one_smul]
        rw [he]
        exact S.toSubmodule.add_mem (S.toSubmodule.smul_mem a.re hv)
          (S.toSubmodule.smul_mem a.im (by
            rw [← hk]
            exact S.apply_mem_toSubmodule k hv)) }
  apply_mem_toSubmodule h v hv := by
    change rho4 h v∈S
    rw [hact]
    exact S.apply_mem_toSubmodule h hv

include hact k hk in
/-- A scalar group-algebra generating tuple remains a binary generating
tuple of the SAME length, using the actual omega element k. -/
theorem generatedBy {n : ℕ} (hgen : RepresentationGeneratedBy rho4 n) :
    RepresentationGeneratedBy rho2 n := by
  obtain ⟨v,hv⟩ := hgen
  let w : Fin n → rho2.asModule := fun i =>
    rho2.asModuleEquiv.symm (rho4.asModuleEquiv (v i))
  let P : Submodule (ZMod 2)[H] rho2.asModule := Submodule.span _ (Set.range w)
  let S : Subrepresentation rho2 := Subrepresentation.ofSubmodule' P
  let Q := scalarUpgrade rho2 rho4 hact k hk S
  have hle : Submodule.span Scalar[H] (Set.range v) ≤ Q.asSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change w i∈P
    exact Submodule.subset_span ⟨i,rfl⟩
  refine ⟨w,top_unique ?_⟩
  intro x _
  have hy : rho4.asModuleEquiv.symm (rho2.asModuleEquiv x)∈Q.asSubmodule := by
    apply hle
    rw [hv]
    trivial
  change rho4.asModuleEquiv (rho4.asModuleEquiv.symm (rho2.asModuleEquiv x))∈S at hy
  rw [LinearEquiv.apply_symm_apply] at hy
  exact hy

include hact k hk in
/-- Uniform scalar generation transfers to every actual binary invariant
subspace, because scalarUpgrade preserves that subspace's carrier. -/
theorem uniform {n : ℕ} (hu : UniformSubrepresentationGeneratorBound rho4 n) :
    UniformSubrepresentationGeneratorBound rho2 n := by
  intro S
  let Q := scalarUpgrade rho2 rho4 hact k hk S
  letI : Module Scalar S.toSubmodule := inferInstanceAs (Module Scalar (scalarUpgrade rho2 rho4 hact k hk S).toSubmodule)
  letI : IsScalarTower (ZMod 2) Scalar S.toSubmodule :=
    ⟨fun a b v => Subtype.ext (smul_assoc a b (v : V))⟩
  let rhoQ : Representation Scalar H S.toSubmodule := Q.toRepresentation
  have hq : RepresentationGeneratedBy rhoQ n := hu Q
  exact generatedBy S.toRepresentation rhoQ
    (fun h v => Subtype.ext (hact h v)) k
    (fun v => Subtype.ext (hk v)) hq

end SymmetricSubgroupAsymptotics.BinaryCubicScalarGeneratorTransfer
