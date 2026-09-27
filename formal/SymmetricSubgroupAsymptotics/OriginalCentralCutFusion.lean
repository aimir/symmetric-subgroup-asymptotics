import SymmetricSubgroupAsymptotics.OriginalCentralCutExtension
import SymmetricSubgroupAsymptotics.PermutationTwoGroupRank
import SymmetricSubgroupAsymptotics.FusionDirectKernelAssembly

/-! Original central-cut fusion with an actual faithful cover of the top.
The original quotient, nonsplit extension, full cohomology coefficient and
common-source character columns are retained. The top quotient itself is
not required to have a faithful permutation action of the cover degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Classical MonoidAlgebra

namespace SymmetricSubgroupAsymptotics.OriginalCentralCutFusion
open OriginalCentralCutExtension

variable {B : Type} [Group B] (A : Rep (ZMod 2) B)
    (C : {C : Submodule (ZMod 2) A // C ≤ A.ρ.invariants})

def capacity : ℝ := representationSchurCapacity (quotientModule A C).ρ

def liftConstant : ℝ :=
  (Nat.card (quotientModule A C) * Nat.card (groupCohomology.H1 (quotientModule A C)) : ℝ)

def prefixDegree (s : ℕ) : ℕ := s+2*Module.finrank (ZMod 2) C.1

def gapParameter (w s : ℕ) : ℝ :=
  ((w:ℝ)-(prefixDegree A C s:ℝ)-4*capacity A C)/16

def momentWeight (J : Type*) [Group J] : ℝ :=
  fusionCentralPrefixWeight (Module.finrank (ZMod 2) C.1) J B

theorem liftConstant_nonneg : 0 ≤ liftConstant A C := by
  unfold liftConstant
  positivity

theorem capacity_nonneg [Finite A] : 0 ≤ capacity A C := by
  letI : Finite (quotientModule A C) :=
    Finite.of_surjective C.1.mkQ C.1.mkQ_surjective
  letI : Module (MonoidAlgebra (ZMod 2) B) (quotientModule A C).ρ.asModule :=
    Representation.instModuleMonoidAlgebraAsModule (quotientModule A C).ρ
  unfold capacity representationSchurCapacity
  exact schurCapacity_nonneg

theorem prefixDegree_lt_of_cost [Finite A] (h : ℕ)
    (hcost : (2*Module.finrank (ZMod 2) C.1:ℝ)+4*capacity A C < (h:ℝ)) :
    prefixDegree A C h < 2*h := by
  have hc := capacity_nonneg A C
  have hn : (2*Module.finrank (ZMod 2) C.1:ℝ) < (h:ℝ) := by linarith
  have hn' : 2*Module.finrank (ZMod 2) C.1 < h := by exact_mod_cast hn
  unfold prefixDegree
  omega

theorem gapParameter_pos_of_cost (h : ℕ)
    (hcost : (2*Module.finrank (ZMod 2) C.1:ℝ)+4*capacity A C < (h:ℝ)) :
    0 < gapParameter A C (2*h) h := by
  unfold gapParameter prefixDegree
  push_cast
  linarith

/-- One original faithful cover supplies every common-source moment. -/
theorem momentWeight_moment_le {T : Type*} [Group T] {s : ℕ}
    (ρ : T →* Equiv.Perm (Fin s)) (hρ : Function.Injective ρ)
    (σ : T →* B) (hσ : Function.Surjective σ) (b q : ℕ) :
    (∑ J : Subgroup (Equiv.Perm (Fin b)), momentWeight A C J^q) ≤
      (subgroupCount (b+q*prefixDegree A C s):ℝ) :=
  fusionCentralPrefixWeight_moment_le ρ hρ σ hσ b
    (Module.finrank (ZMod 2) C.1) q

variable {Q : Type} [Group Q] [Finite Q] [Finite B] [Finite A]
    (π : Q →* B) (hπ : Function.Surjective π) (E : OriginalKernelModuleChart π A)

include hπ E in
/-- The whole actual surviving family uses the unchanged original quotient. -/
theorem original_survival_card_le {b : ℕ}
    (J : Subgroup (Equiv.Perm (Fin b))) (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f}:ℝ) ≤
      liftConstant A C * (2:ℝ)^((capacity A C/2)*(b:ℝ)) * momentWeight A C J := by
  letI : Finite (quotientModule A C) :=
    Finite.of_surjective C.1.mkQ C.1.mkQ_surjective
  let P : ∀ β : GroupEpimorphism J B, Sylow 2 β.1.ker :=
    fun _ => Classical.arbitrary _
  exact fusionCentralPrefix_survival_card_le
    (first π A E C) (first_surjective π A E C) (first_central π A E C)
    (centralEquiv π A E C) (base π A E C) (base_surjective π A E C hπ)
    (quotientModule A C) (quotientChart π A E C) P S (b:ℝ)
    (fun β => permutationTwoGroup_sylowKernel_primeAbelianizationRank_le J β.1 (P β))

omit [Finite B] [Finite A] in
theorem localFactor_eq (b h s : ℕ) :
    fusionLocalFactor b h (prefixDegree A C s) (liftConstant A C)
      (gapParameter A C (2*h) s) =
        liftConstant A C * (2:ℝ)^((capacity A C/2)*(b:ℝ)) := by
  unfold fusionLocalFactor
  have he : (((2*h:ℕ):ℝ)-(prefixDegree A C s:ℝ)-16*gapParameter A C (2*h) s)/8 =
      capacity A C/2 := by
    unfold gapParameter
    ring
  rw [he]

include hπ E in
theorem original_survival_localFactor_le {b : ℕ} (h s : ℕ)
    (J : Subgroup (Equiv.Perm (Fin b))) (S : GroupEpimorphism J Q → Prop) :
    (Nat.card {f : GroupEpimorphism J Q // S f}:ℝ) ≤
      fusionLocalFactor b h (prefixDegree A C s) (liftConstant A C)
        (gapParameter A C (2*h) s) * momentWeight A C J := by
  rw [localFactor_eq]
  exact original_survival_card_le A C π hπ E J S

end SymmetricSubgroupAsymptotics.OriginalCentralCutFusion
