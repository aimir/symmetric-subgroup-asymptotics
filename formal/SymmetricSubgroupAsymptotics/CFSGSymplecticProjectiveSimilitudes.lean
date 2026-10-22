import SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeCardinality
import Mathlib.GroupTheory.Index

/-! Scalar linear maps are exactly the kernel of the actual similitude
point action. Cancelling this literal kernel yields the projective
similitude order, without counting the larger projective linear group. -/
set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeGroup
open CFSGSymplecticSerreMatrices CFSGSymplecticTransvectionGeometry
variable {K : Type} [Field K]

abbrev Points (n : ℕ) := ℙ K (Index n → K)

def pointHom (n : ℕ) : similitudes (K := K) n →* Equiv.Perm (Points (K := K) n) :=
  (MulAction.toPermHom (LinearGroup (K := K) n) (Points (K := K) n)).comp
    (similitudes n).subtype

def scalarElement (n : ℕ) (c : Kˣ) : similitudes (K := K) n :=
  ⟨LinearEquiv.smulOfUnit c,
    ⟨(c : K) ^ 2, pow_ne_zero 2 c.ne_zero, fun v w => by
      change pairing n ((c : K) • v) ((c : K) • w) = _
      rw [pairing_smul_left, pairing_smul_right]
      ring⟩⟩

theorem scalar_mem_ker (n : ℕ) (c : Kˣ) : scalarElement n c ∈ (pointHom n).ker := by
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro p
  rw [← Projectivization.mk_rep p]
  change (LinearEquiv.smulOfUnit c : LinearGroup (K := K) n) • Projectivization.mk K p.rep p.rep_nonzero = _
  rw [Projectivization.smul_mk]
  apply (Projectivization.mk_eq_mk_iff K _ _ _ _).mpr
  exact ⟨c, rfl⟩

theorem exists_scalar_of_mem_ker (n : ℕ) (hn : 0 < n)
    (g : similitudes (K := K) n) (hg : g ∈ (pointHom n).ker) :
    ∃ c : Kˣ, scalarElement n c = g := by
  have ht (v : Index n → K) : ∃ c : K, g.val v = c • v := by
    by_cases hv : v = 0
    · subst v; exact ⟨0, by rw [map_zero, zero_smul]⟩
    · have hp := congrArg (fun f : Equiv.Perm (Points (K := K) n) =>
        f (Projectivization.mk K v hv)) (MonoidHom.mem_ker.mp hg)
      change g.val • Projectivization.mk K v hv = Projectivization.mk K v hv at hp
      rw [Projectivization.smul_mk] at hp
      obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ _ _).mp hp
      exact ⟨c, hc.symm⟩
  obtain ⟨c, hc⟩ := CFSGLinePreservingLinearMap.exists_scalar g.val.toLinearMap ht (Sum.inl (⟨0, hn⟩ : Fin n))
  have hcv (v : Index n → K) : g.val v = c • v :=
    congrArg (fun T : Module.End K (Index n → K) => T v) hc
  have hc0 : c ≠ 0 := by
    intro hz
    let v : Index n → K := Pi.single (Sum.inl (⟨0, hn⟩ : Fin n)) 1
    have hv : g.val v = g.val 0 := by rw [hcv, hz, zero_smul, map_zero]
    have hh := congrFun (g.val.injective hv) (Sum.inl (⟨0, hn⟩ : Fin n))
    simp [v] at hh
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact (hcv v).symm

def scalarToKernel (n : ℕ) (c : Kˣ) : (pointHom (K := K) n).ker :=
  ⟨scalarElement n c, scalar_mem_ker n c⟩

theorem scalarToKernel_bijective (n : ℕ) (hn : 0 < n) :
    Function.Bijective (scalarToKernel (K := K) n) := by
  constructor
  · intro c d he
    apply Units.ext
    have hh := congrArg (fun z : (pointHom (K := K) n).ker =>
      z.val.val (Pi.single (Sum.inl (⟨0, hn⟩ : Fin n)) 1) (Sum.inl (⟨0, hn⟩ : Fin n))) he
    change ((c : K) • Pi.single (Sum.inl (⟨0, hn⟩ : Fin n)) 1) (Sum.inl (⟨0, hn⟩ : Fin n)) =
      ((d : K) • Pi.single (Sum.inl (⟨0, hn⟩ : Fin n)) 1) (Sum.inl (⟨0, hn⟩ : Fin n)) at hh
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one] using hh
  · intro g
    obtain ⟨c, hc⟩ := exists_scalar_of_mem_ker n hn g.val g.property
    exact ⟨c, Subtype.ext hc⟩

theorem pointHom_ker_card (n : ℕ) (hn : 0 < n) :
    Nat.card (pointHom (K := K) n).ker = Nat.card Kˣ :=
  (Nat.card_congr (Equiv.ofBijective (scalarToKernel n) (scalarToKernel_bijective n hn))).symm

variable [Finite K]

local instance finite_similitudes (n : ℕ) : Finite (similitudes (K := K) n) :=
  Finite.of_injective (fun g : similitudes (K := K) n => (g.val : (Index n → K) → (Index n → K)))
    (by intro g h he; apply Subtype.ext; exact LinearEquiv.ext (congrFun he))

theorem projectiveSimilitudes_card (n : ℕ) (hn : 0 < n) :
    Nat.card (pointHom (K := K) n).range = Nat.card (elementaryRootGroup K n) := by
  have he := (pointHom (K := K) n).ker.card_mul_index
  rw [pointHom_ker_card n hn, Subgroup.index_ker, similitudes_card n hn] at he
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos he

end SymmetricSubgroupAsymptotics.CFSGSymplecticSimilitudeGroup
