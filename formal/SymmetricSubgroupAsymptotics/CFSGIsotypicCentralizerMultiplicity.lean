import SymmetricSubgroupAsymptotics.CFSGScalarBlockRepresentation
import SymmetricSubgroupAsymptotics.CFSGIrreducibleLinearCentralizer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! When the constituent endomorphism algebra consists of scalars, its
actual isotypic centralizer embeds in the general linear group of the
multiplicity space. The block intertwiners are constructed from the literal
coordinate maps and the actual commuting linear automorphism. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerMultiplicity
open CFSGIrreducibleLinearCentralizer CFSGScalarBlockRepresentation

variable {k S I W : Type} [Field k] [Group S] [Fintype I] [DecidableEq I]
    [AddCommGroup W] [Module k W]

def repeated (tau : Representation k S W) : Representation k S (I → W) where
  toFun s := LinearMap.pi (fun i => (tau s).comp (LinearMap.proj i))
  map_one' := by
    apply LinearMap.ext
    intro v
    funext i
    change tau 1 (v i) = v i
    rw [map_one]
    rfl
  map_mul' s t := by
    apply LinearMap.ext
    intro v
    funext i
    change tau (s*t) (v i) = tau s (tau t (v i))
    rw [map_mul]
    rfl

def blockIntertwiner (tau : Representation k S W)
    (e : linearCentralizer (repeated (I:=I) tau)) (i j : I) :
    tau.IntertwiningMap tau :=
  ((LinearMap.proj i).comp (e.val.toLinearMap.comp (LinearMap.single k _ j))).intertwiningMap_of_isIntertwiningMap
    tau tau (by
      intro s w
      change e.val (Pi.single j (tau s w)) i = tau s (e.val (Pi.single j w) i)
      have hs : (Pi.single j (tau s w) : I → W) =
          repeated tau s (Pi.single j w) := by
        funext t
        by_cases hjt : j = t
        · subst t
          simp [repeated]
        · simp [repeated, hjt]
      rw [hs]
      exact congrFun (e.property s (Pi.single j w)) i)

def centralizerRepresentation (tau : Representation k S W) :
    Representation k (linearCentralizer (repeated (I:=I) tau)) (I → W) where
  toFun e := e.val.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Fintype I] [DecidableEq I] in
theorem centralizerRepresentation_injective (tau : Representation k S W) :
    Function.Injective (centralizerRepresentation (I:=I) tau) := by
  intro e f he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact congrArg (fun a : (I → W) →ₗ[k] (I → W) => a v) he

/-- The order divisor is proved for the literal centralizer, without
assuming an isomorphism with a matrix group. -/
theorem centralizer_card_dvd_multiplicity [Finite k] [Finite W] [Nontrivial W]
    (tau : Representation k S W)
    (hscalar : ∀ f : tau.IntertwiningMap tau, ∃ a : k, ∀ w, f w = a • w) :
    Nat.card (linearCentralizer (repeated (I:=I) tau)) ∣
      Nat.card ((I → k) ≃ₗ[k] (I → k)) := by
  letI : Finite (linearCentralizer (repeated (I:=I) tau)) :=
    Finite.of_injective (fun e : linearCentralizer (repeated (I:=I) tau) =>
      (e.val : (I → W) → (I → W))) (by
        intro e f he
        apply Subtype.ext
        exact LinearEquiv.ext (congrFun he))
  obtain ⟨w,hw⟩ := exists_ne (0 : W)
  obtain ⟨ell,hell⟩ := Module.Projective.exists_dual_eq_one k hw
  apply card_dvd_multiplicity_linearGroup (centralizerRepresentation tau) w ell hell
    (fun e i j => hscalar (blockIntertwiner tau e i j))
  exact centralizerRepresentation_injective tau

theorem scalar_intertwiners_of_finrank_one
    (tau : Representation k S W)
    (hfin : Module.finrank k (tau.IntertwiningMap tau) = 1) :
    ∀ f : tau.IntertwiningMap tau, ∃ a : k, ∀ w, f w = a • w := by
  letI : Nontrivial (tau.IntertwiningMap tau) :=
    Module.nontrivial_of_finrank_pos (R:=k) (by rw [hfin]; decide)
  intro f
  obtain ⟨a,ha⟩ := exists_smul_eq_of_finrank_eq_one hfin
    (one_ne_zero : (1 : tau.IntertwiningMap tau) ≠ 0) f
  refine ⟨a,fun w => ?_⟩
  have hh := congrArg (fun g : tau.IntertwiningMap tau => g w) ha
  simpa using hh.symm

theorem centralizer_card_dvd_multiplicity_of_finrank_one
    [Finite k] [Finite W] [Nontrivial W]
    (tau : Representation k S W)
    (hfin : Module.finrank k (tau.IntertwiningMap tau) = 1) :
    Nat.card (linearCentralizer (repeated (I:=I) tau)) ∣
      Nat.card ((I → k) ≃ₗ[k] (I → k)) :=
  centralizer_card_dvd_multiplicity tau (scalar_intertwiners_of_finrank_one tau hfin)

end SymmetricSubgroupAsymptotics.CFSGIsotypicCentralizerMultiplicity
