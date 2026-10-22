import Mathlib.RepresentationTheory.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.GroupTheory.Coset.Card

/-! A group whose actual block maps are scalars acts faithfully on the
multiplicity space. This constructs the multiplicity representation and
its order divisor without assuming a centralizer order formula. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGScalarBlockRepresentation

variable {k H I W : Type*} [Field k] [Group H] [Fintype I] [DecidableEq I]
    [AddCommGroup W] [Module k W]

def pureCoordinates (w : W) : (I → k) →ₗ[k] (I → W) where
  toFun a i := a i • w
  map_add' a b := by ext i; exact add_smul _ _ _
  map_smul' a b := by ext i; exact mul_smul _ _ _

def readCoordinates (ell : W →ₗ[k] k) : (I → W) →ₗ[k] (I → k) where
  toFun v i := ell (v i)
  map_add' v z := by ext i; exact map_add ell _ _
  map_smul' a v := by ext i; exact map_smul ell _ _

variable (rho : Representation k H (I → W))
    (w : W) (ell : W →ₗ[k] k) (hell : ell w = 1)
    (hblock : ∀ (g : H) (i j : I),
      ∃ a : k, ∀ v : W, rho g (Pi.single j v) i = a • v)

def coefficientMap (g : H) : (I → k) →ₗ[k] (I → k) :=
  (readCoordinates ell).comp ((rho g).comp (pureCoordinates w))

include hell in
omit [Fintype I] [DecidableEq I] in
theorem read_pure (a : I → k) : readCoordinates ell (pureCoordinates w a) = a := by
  ext i
  change ell (a i • w) = a i
  simp [hell]

omit [Fintype I] in
theorem pure_single (j : I) : pureCoordinates w (Pi.single j (1 : k)) =
    Pi.single j w := by
  ext i
  by_cases hji : j = i
  · subst i
    simp [pureCoordinates]
  · simp [pureCoordinates, hji]

include hell hblock in
omit [Fintype I] in
theorem block_eq_coefficient (g : H) (i j : I) (v : W) :
    rho g (Pi.single j v) i = coefficientMap rho w ell g (Pi.single j 1) i • v := by
  obtain ⟨a,ha⟩ := hblock g i j
  change rho g (Pi.single j v) i =
    ell (rho g (pureCoordinates w (Pi.single j 1)) i) • v
  rw [pure_single w j, ha, ha]
  simp [hell]

include hell hblock in
theorem apply_eq_sum (g : H) (v : I → W) (i : I) :
    rho g v i = ∑ j, coefficientMap rho w ell g (Pi.single j 1) i • v j := by
  conv_lhs => rw [← Finset.univ_sum_single v, map_sum]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _ => block_eq_coefficient rho w ell hell hblock g i j (v j))

theorem coefficientMap_apply (g : H) (a : I → k) (i : I) :
    coefficientMap rho w ell g a i =
      ∑ j, a j * coefficientMap rho w ell g (Pi.single j 1) i := by
  have hh := congrArg (fun f : I → k => f i)
    (LinearMap.pi_apply_eq_sum_univ (coefficientMap rho w ell g) a)
  have hs (j : I) : (fun t : I => if j = t then (1:k) else 0) = Pi.single j 1 := by
    ext t
    by_cases hjt : j = t
    · subst t
      simp
    · simp [hjt, Ne.symm hjt]
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hs] using hh

include hell hblock in
theorem pure_stable (g : H) (a : I → k) :
    rho g (pureCoordinates w a) = pureCoordinates w (coefficientMap rho w ell g a) := by
  ext i
  rw [apply_eq_sum rho w ell hell hblock]
  change (∑ j, coefficientMap rho w ell g (Pi.single j 1) i • (a j • w)) =
    coefficientMap rho w ell g a i • w
  rw [coefficientMap_apply, Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_smul, mul_comm]

/-- The actual action on the multiplicity space. -/
def multiplicityRepresentation : Representation k H (I → k) where
  toFun := coefficientMap rho w ell
  map_one' := by
    apply LinearMap.ext
    intro a
    funext i
    change ell (rho 1 (pureCoordinates w a) i) = a i
    rw [map_one]
    exact congrFun (read_pure w ell hell a) i
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    funext i
    change ell (rho (g*h) (pureCoordinates w a) i) =
      ell (rho g (pureCoordinates w (coefficientMap rho w ell h a)) i)
    rw [map_mul]
    change ell (rho g (rho h (pureCoordinates w a)) i) = _
    rw [pure_stable rho w ell hell hblock]

include hell hblock in
theorem multiplicityRepresentation_injective (hfaithful : Function.Injective rho) :
    Function.Injective (multiplicityRepresentation rho w ell hell hblock) := by
  intro g h he
  apply hfaithful
  apply LinearMap.ext
  intro v
  funext i
  rw [apply_eq_sum rho w ell hell hblock, apply_eq_sum rho w ell hell hblock]
  apply Finset.sum_congr rfl
  intro j _
  have hh := congrArg (fun f : (I → k) →ₗ[k] (I → k) => f (Pi.single j 1) i) he
  change coefficientMap rho w ell g (Pi.single j 1) i =
    coefficientMap rho w ell h (Pi.single j 1) i at hh
  rw [hh]

include hell hblock in
theorem card_dvd_multiplicity_linearGroup [Finite H] [Finite k]
    (hfaithful : Function.Injective rho) :
    Nat.card H ∣ Nat.card ((I → k) ≃ₗ[k] (I → k)) := by
  let sigma := multiplicityRepresentation rho w ell hell hblock
  let phi := (LinearMap.GeneralLinearGroup.generalLinearEquiv k (I → k)).toMonoidHom.comp
    sigma.asGroupHom
  apply Subgroup.card_dvd_of_injective phi
  intro g h he
  apply multiplicityRepresentation_injective rho w ell hell hblock hfaithful
  have hu : sigma.asGroupHom g = sigma.asGroupHom h :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv k (I → k)).injective he
  exact congrArg Units.val hu

end SymmetricSubgroupAsymptotics.CFSGScalarBlockRepresentation
