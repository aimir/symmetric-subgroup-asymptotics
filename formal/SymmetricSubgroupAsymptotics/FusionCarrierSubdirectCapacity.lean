import SymmetricSubgroupAsymptotics.FusionCarrierIncidence
import SymmetricSubgroupAsymptotics.BinaryMarkedSubdirect

/-!
# Joint capacity on the literal carrier pullback core

Every intrinsic carrier epimorphism determines a full subdirect pullback of
the carrier and the unchanged complete exterior source.  This file applies
the proved joint character, derived-normal, radical and restricted-`H²`
transition to that literal core.  In particular, a nonabelian proper
subdirect core is not replaced by a direct product or by independent maxima.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics

/-- The intrinsic pullback core attached to one carrier epimorphism.  The
second factor is the actual source subgroup `J`, not its ambient symmetric
group, so both projections are literally full. -/
def fusionCarrierSubdirectGraph
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient) :
    Subgroup (C.carrier × J) where
  carrier := {x | C.beta x.1 = δ.1 x.2}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change C.beta (x.1 * y.1) = δ.1 (x.2 * y.2)
    rw [map_mul, map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change C.beta x.1⁻¹ = δ.1 x.2⁻¹
    rw [map_inv, map_inv, hx]

@[simp] theorem mem_fusionCarrierSubdirectGraph
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient)
    (x : C.carrier × J) :
    x ∈ fusionCarrierSubdirectGraph C J δ ↔ C.beta x.1 = δ.1 x.2 :=
  Iff.rfl

/-- Surjectivity onto the whole literal carrier uses surjectivity of the
source epimorphism. -/
theorem fusionCarrierSubdirectGraph_fst_surjective
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient) :
    Function.Surjective
      (Prod.fst ∘ (fusionCarrierSubdirectGraph C J δ).subtype) := by
  intro u
  obtain ⟨j, hj⟩ := δ.2 (C.beta u)
  exact ⟨⟨(u, j), hj.symm⟩, rfl⟩

/-- Surjectivity onto the unchanged complete source uses the carrier's
specified quotient surjection. -/
theorem fusionCarrierSubdirectGraph_snd_surjective
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient) :
    Function.Surjective
      (Prod.snd ∘ (fusionCarrierSubdirectGraph C J δ).subtype) := by
  intro j
  obtain ⟨u, hu⟩ := C.beta_surjective (δ.1 j)
  exact ⟨⟨(u, j), hu⟩, rfl⟩

/-- Include the literal source subgroup into its ambient symmetric group,
leaving every carrier coordinate untouched. -/
def fusionCarrierSubdirectEmbedding
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    C.carrier × J →* C.carrier × Equiv.Perm (Fin b) :=
  (MonoidHom.id C.carrier).prodMap J.subtype

theorem fusionCarrierSubdirectEmbedding_injective
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    Function.Injective (fusionCarrierSubdirectEmbedding C J) := by
  intro x y h
  apply Prod.ext
  · exact congrArg
      (fun z : C.carrier × Equiv.Perm (Fin b) => z.1) h
  · apply Subtype.ext
    exact congrArg
      (fun z : C.carrier × Equiv.Perm (Fin b) => z.2) h

/-- The intrinsic full subdirect core maps to the exact ambient quotient
graph used by carrier survival.  Thus the capacity core and the accepted
physical graph are two literal presentations of the same state. -/
theorem fusionCarrierSubdirectGraph_map_eq_ambient
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient) :
    (fusionCarrierSubdirectGraph C J δ).map
        (fusionCarrierSubdirectEmbedding C J) =
      fusionQuotientGraph C.beta J δ.1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, rfl, hy⟩
  · rintro ⟨j, hj, hβ⟩
    refine ⟨(x.1, j), hβ, ?_⟩
    apply Prod.ext
    · rfl
    · exact hj

/-- The literal pullback core recovers its epimorphism.  This is the
reversibility needed before any coarser radical or annihilator signature is
allowed to merge cells. -/
theorem fusionCarrierSubdirectGraph_injective
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b))) :
    Function.Injective (fusionCarrierSubdirectGraph C J) := by
  intro δ ε h
  apply Subtype.ext
  apply MonoidHom.ext
  intro j
  obtain ⟨u, hu⟩ := C.beta_surjective (δ.1 j)
  have hm : (u, j) ∈ fusionCarrierSubdirectGraph C J δ := hu
  rw [h] at hm
  exact hu.symm.trans hm

/-- The literal first axis is exactly the retained carrier kernel. -/
@[simp] theorem fusionCarrierSubdirectGraph_axis
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient) :
    (fusionCarrierSubdirectGraph C J δ).goursatFst = C.beta.ker := by
  ext u
  rw [Subgroup.mem_goursatFst]
  change C.beta u = δ.1 1 ↔ C.beta u = 1
  simp

/-- Mapping the same axis back to the physical carrier recovers the exact
kernel recorded by the checked carrier certificate. -/
theorem fusionCarrierSubdirectGraph_axis_map
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient) :
    (fusionCarrierSubdirectGraph C J δ).goursatFst.map C.carrier.subtype =
      C.carrierKernel := by
  rw [fusionCarrierSubdirectGraph_axis, C.beta_kernel]

/-- The full five-part joint transition holds on every literal carrier
epimorphism core.  Its radical and restricted inflation kernel belong to
this same core, and the tail invariants belong to the unchanged source `J`.
-/
theorem fusionCarrierSubdirectGraph_joint_transition
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient) :
    let H := fusionCarrierSubdirectGraph C J δ
    letI := Subgroup.normal_goursatFst
      (fusionCarrierSubdirectGraph_fst_surjective C J δ)
    let d := Module.finrank (ZMod 2) (PrimeCharacters 2 H) -
      Module.finrank (ZMod 2) (PrimeCharacters 2 J)
    let e := primeDerivedNormalRank 2 H - primeDerivedNormalRank 2 J
    let k := Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 H.goursatFst)
    let a₂ := Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 H.goursatFst))
    Module.finrank (ZMod 2) (PrimeCharacters 2 J) ≤
        Module.finrank (ZMod 2) (PrimeCharacters 2 H) ∧
      d ≤ k ∧ e ≤ primeSubdirectAxisNormalRank 2 H ∧
      d + e ≤ Nat.log 2 (Nat.card H.goursatFst) ∧
      Module.finrank (ZMod 2) (terminalRestrictedInflationKernel H) ≤
        Module.finrank (ZMod 2) (terminalRestrictedInflationKernel J) +
          k - d + a₂ := by
  dsimp only
  exact binarySubdirect_joint_transition
    (fusionCarrierSubdirectGraph C J δ)
    (fusionCarrierSubdirectGraph_fst_surjective C J δ)
    (fusionCarrierSubdirectGraph_snd_surjective C J δ)

/-- Arbitrary marked character/normal/`H²` energy also descends through the
same literal carrier core.  The first mark may be negative; the other two
are required nonnegative exactly as in the general joint-capacity polygon.
-/
theorem fusionCarrierSubdirectGraph_marked_transition
    {w q b : ℕ}
    (C : CheckedPermutationCarrier w q)
    (J : Subgroup (Equiv.Perm (Fin b)))
    (δ : GroupEpimorphism J C.quotient)
    (x y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    let H := fusionCarrierSubdirectGraph C J δ
    letI := Subgroup.normal_goursatFst
      (fusionCarrierSubdirectGraph_fst_surjective C J δ)
    let k := Module.finrank (ZMod 2)
      (primeRelativeCharacters 2 H.goursatFst)
    let m := primeSubdirectAxisNormalRank 2 H
    let a₂ := Module.finrank (ZMod 2) (primeRelativeCharacters 2
      (primeRelativeRadical 2 H.goursatFst))
    x * (Module.finrank (ZMod 2) (PrimeCharacters 2 H) : ℝ) +
        y * (primeDerivedNormalRank 2 H : ℝ) +
        z * (Module.finrank (ZMod 2)
          (terminalRestrictedInflationKernel H) : ℝ) ≤
      x * (Module.finrank (ZMod 2) (PrimeCharacters 2 J) : ℝ) +
        y * (primeDerivedNormalRank 2 J : ℝ) +
        z * (Module.finrank (ZMod 2)
          (terminalRestrictedInflationKernel J) : ℝ) +
        z * ((k : ℝ) + (max m a₂ : ℕ)) +
        jointCapacitySupport k (Nat.log 2 (Nat.card H.goursatFst)) m
          (x - z) y := by
  dsimp only
  exact binarySubdirect_marked_transition
    (fusionCarrierSubdirectGraph C J δ)
    (fusionCarrierSubdirectGraph_fst_surjective C J δ)
    (fusionCarrierSubdirectGraph_snd_surjective C J δ)
    x y z hy hz

end SymmetricSubgroupAsymptotics

end
