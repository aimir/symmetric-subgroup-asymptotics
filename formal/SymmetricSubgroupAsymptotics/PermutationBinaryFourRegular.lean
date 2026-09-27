import SymmetricSubgroupAsymptotics.PermutationBinaryFourSection
import SymmetricSubgroupAsymptotics.RepresentationDisplacementCharacters
import SymmetricSubgroupAsymptotics.PrimeCharacterKernelOrbits
import SymmetricSubgroupAsymptotics.PermutationBinaryLargeSection

/-! An extremal fixed quotient of the original permutation module forces
the original action to be regular elementary abelian. In particular, at
four actual points, two fixed quotient directions force the actual group
to have order four and exponent two. The proof retains all displacement
characters and the original point stabilizer; no list of permutation
groups or binary-group classification is used. -/
set_option autoImplicit false
noncomputable section
open scoped Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationBinaryFourRegular

variable {G X : Type} [Group G] [MulAction G X]
    [MulAction.IsPretransitive G X]

local notation "ρ" => permutationFunctionRepresentation (ZMod 2) G X
local notation "D" => displacementSlice ρ (Representation.invariants ρ)

/-- Evaluate every original fixed-valued displacement at an actual point.
Transitivity identifies its whole fixed value with this scalar. -/
def displacementCharactersAt (x : X) : D →ₗ[ZMod 2] PrimeCharacters 2 G where
  toFun f := fixedDisplacementTranspose 2 ρ f
    (PermutationBinaryFourSection.fixedEval (k := ZMod 2) (G := G) x).toLinearMap
  map_add' f f' := by
    simp only [map_add,LinearMap.add_apply]
  map_smul' c f := by
    simp only [map_smul,LinearMap.smul_apply,RingHom.id_apply]

theorem displacementCharactersAt_injective (x : X) :
    Function.Injective (displacementCharactersAt (G := G) x) := by
  intro f f' h
  apply Subtype.ext
  funext g
  have hv : fixedDisplacementValue 2 ρ f g=fixedDisplacementValue 2 ρ f' g := by
    apply (PermutationBinaryFourSection.fixedEval (k := ZMod 2) (G := G) x).injective
    exact congrArg (fun χ : PrimeCharacters 2 G => χ (Additive.ofMul g)) h
  exact congrArg Subtype.val hv

/-- These same characters all vanish on the original point stabilizer. -/
theorem displacementCharactersAt_stabilizer (x : X) (f : D) (g : G)
    (hg : g∈MulAction.stabilizer G x) :
    displacementCharactersAt x f (Additive.ofMul g)=0 := by
  obtain ⟨a,ha⟩ := f.property.1
  change f.val g x=0
  rw [← ha]
  change a (g⁻¹ • x)-a x=0
  rw [MulAction.mem_stabilizer_iff.mp ((MulAction.stabilizer G x).inv_mem hg),
    sub_self]

/-- The actual group evaluation into the dual of its entire displacement
slice. Its surjectivity will follow from the proved character injection. -/
def displacementEvaluation (x : X) : G →* Multiplicative (Module.Dual (ZMod 2) D) :=
  retainedCharacterEvaluation 2 (displacementCharactersAt (G := G) x)

variable [Finite G] [Finite X]

theorem displacementEvaluation_surjective (x : X) :
    Function.Surjective (displacementEvaluation (G := G) x) :=
  retainedCharacterEvaluation_surjective 2 (displacementCharactersAt x)
    (displacementCharactersAt_injective x)

theorem retainedStabilizerVanishing_eq_top (x : X) :
    retainedStabilizerVanishing 2 (displacementCharactersAt (G := G) x) x=⊤ := by
  apply top_unique
  intro f _
  exact (mem_retainedStabilizerVanishing_iff 2 (displacementCharactersAt x) x f).mpr
    (fun g hg => displacementCharactersAt_stabilizer x f g hg)

variable [FaithfulSMul G X]

/-- Equality between the fixed-quotient dimension and the degree exponent
forces the literal common character kernel to be trivial. Faithfulness
is applied only after its actual original orbits have size one. -/
theorem displacementEvaluation_injective_of_maximal_fixed_quotient
    (x : X) (a : ℕ) (hcard : Nat.card X=2^a)
    (hdim : Module.finrank (ZMod 2)
      (centralQuotientRepresentation ρ (ρ).invariants le_rfl).invariants=a) :
    Function.Injective (displacementEvaluation (G := G) x) := by
  apply (MonoidHom.ker_eq_bot_iff (displacementEvaluation x)).mp
  by_contra hker
  have hne := normal_orbit_card_ne_one_of_ne_bot
    (displacementEvaluation x).ker hker x
  let o : MulAction.orbitRel.Quotient (displacementEvaluation (G := G) x).ker X :=
    Quotient.mk'' x
  have ho := retainedCharacterKernel_orbit_card 2 (displacementCharactersAt x) x
    (displacementCharactersAt_injective x) a hcard o
  rw [retainedStabilizerVanishing_eq_top,finrank_top,
    displacementSlice_invariants_finrank,hdim,Nat.sub_self,pow_zero] at ho
  exact hne ho

/-- Cardinality comes from a bijection of the original group with the
dual of the original displacement slice. -/
theorem card_eq_degree_of_maximal_fixed_quotient
    (x : X) (a : ℕ) (hcard : Nat.card X=2^a)
    (hdim : Module.finrank (ZMod 2)
      (centralQuotientRepresentation ρ (ρ).invariants le_rfl).invariants=a) :
    Nat.card G=2^a := by
  rw [Nat.card_congr (Equiv.ofBijective (displacementEvaluation x)
    ⟨displacementEvaluation_injective_of_maximal_fixed_quotient x a hcard hdim,
      displacementEvaluation_surjective x⟩)]
  change Nat.card (Module.Dual (ZMod 2) D)=2^a
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Subspace.dual_finrank_eq,displacementSlice_invariants_finrank,hdim]

theorem pow_two_eq_one_of_maximal_fixed_quotient
    (x : X) (a : ℕ) (hcard : Nat.card X=2^a)
    (hdim : Module.finrank (ZMod 2)
      (centralQuotientRepresentation ρ (ρ).invariants le_rfl).invariants=a)
    (g : G) : g^2=1 := by
  apply displacementEvaluation_injective_of_maximal_fixed_quotient x a hcard hdim
  rw [map_one]
  change (retainedCharacterEvaluation 2 (displacementCharactersAt x) (g^2)).toAdd=0
  ext f
  change displacementCharactersAt x f (Additive.ofMul (g^2))=0
  have h := (displacementCharactersAt x f).map_nsmul 2 (Additive.ofMul g)
  change displacementCharactersAt x f (Additive.ofMul (g^2))=
    2 • displacementCharactersAt x f (Additive.ofMul g) at h
  rw [h]
  exact ZModModule.char_nsmul_eq_zero 2 _

/-- Every original point stabilizer is trivial, not merely an isomorphic
replacement action's stabilizer. -/
theorem stabilizer_eq_bot_of_maximal_fixed_quotient
    (x : X) (a : ℕ) (hcard : Nat.card X=2^a)
    (hdim : Module.finrank (ZMod 2)
      (centralQuotientRepresentation ρ (ρ).invariants le_rfl).invariants=a) :
    MulAction.stabilizer G x=⊥ := by
  apply le_antisymm ?_ bot_le
  intro g hg
  apply Subgroup.mem_bot.mpr
  apply displacementEvaluation_injective_of_maximal_fixed_quotient x a hcard hdim
  rw [map_one]
  exact (mem_retainedCharacterEvaluation_ker_iff 2 (displacementCharactersAt x) g).mpr
    (fun f => displacementCharactersAt_stabilizer x f g hg)

/-- The concrete four-point conclusion used by the original rank-three
residual route. No p-group assumption or list of degree-four groups is
required: the fixed quotient itself forces regular exponent-two order four. -/
theorem regular_four_of_fixed_quotient_finrank_two (hcard : Nat.card X=4)
    (hdim : Module.finrank (ZMod 2)
      (centralQuotientRepresentation ρ (ρ).invariants le_rfl).invariants=2) :
    Nat.card G=4 ∧ (∀ g : G, g^2=1) ∧
      ∀ x : X, MulAction.stabilizer G x=⊥ := by
  haveI : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0<Nat.card X)).1
  let x : X := Classical.choice inferInstance
  have hc : Nat.card X=2^2 := by simpa using hcard
  exact ⟨by simpa using card_eq_degree_of_maximal_fixed_quotient x 2 hc hdim,
    pow_two_eq_one_of_maximal_fixed_quotient x 2 hc hdim,
    fun y => stabilizer_eq_bot_of_maximal_fixed_quotient y 2 hc hdim⟩

end SymmetricSubgroupAsymptotics.PermutationBinaryFourRegular
