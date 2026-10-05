import SymmetricSubgroupAsymptotics.FaithfulThreeOnThree
import SymmetricSubgroupAsymptotics.TraceySolubleOrbitInducedInput
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The one-orbit coefficient on a faithful binary plane

An order-three group acting faithfully on a two-dimensional binary module
has one orbit on the three nonzero vectors of the dual.  This discharges
the literal `chi(P'_N ∩ core_G(H), V*) = 1` coefficient in Tracey's
formula once the actual Hall subgroup has been shown to map onto the local
ternary core.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical

namespace SymmetricSubgroupAsymptotics

/-- Faithfulness is preserved by taking the contragredient of a
finite-dimensional representation over a field. -/
theorem dualRepresentation_injective_of_injective
    {k L V : Type} [Field k] [Group L]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (rho : Representation k L V)
    (hrho : Function.Injective rho) :
    Function.Injective rho.dual := by
  intro g h hgh
  have hinv : rho g⁻¹ = rho h⁻¹ := by
    apply LinearMap.ext
    intro v
    apply sub_eq_zero.mp
    apply (Module.forall_dual_apply_eq_zero_iff k _).mp
    intro f
    rw [map_sub, sub_eq_zero]
    have hf := DFunLike.congr_fun hgh f
    exact DFunLike.congr_fun hf v
  exact inv_injective (hrho hinv)

/-- The nonzero dual vectors of a faithful binary plane form one orbit for
an acting group of order three. -/
theorem binaryPlane_dual_nonzero_orbit_card_one
    {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (hrho : Function.Injective rho) :
    Nat.card (Quotient (representationNonzeroOrbitRel rho.dual)) = 1 := by
  letI : Finite V := Module.finite_of_finite (ZMod 2)
  letI : Finite (Module.Dual (ZMod 2) V) :=
    Module.finite_of_finite (ZMod 2)
  let X := {v : Module.Dual (ZMod 2) V // v ≠ 0}
  letI : MulAction L X := {
    smul := fun g x ↦ ⟨rho.dual g x.1, by
      intro hz
      apply x.2
      have hz' := congrArg (rho.dual g⁻¹) hz
      change (rho.dual g⁻¹ * rho.dual g) x.1 = 0 at hz'
      rw [← map_mul, inv_mul_cancel, map_one] at hz'
      exact hz'⟩
    one_smul := by
      intro x
      apply Subtype.ext
      change rho.dual 1 x.1 = x.1
      rw [map_one]
      rfl
    mul_smul := by
      intro g h x
      apply Subtype.ext
      change rho.dual (g * h) x.1 = rho.dual g (rho.dual h x.1)
      rw [map_mul]
      rfl }
  have hdual : Function.Injective rho.dual :=
    dualRepresentation_injective_of_injective rho hrho
  letI : FaithfulSMul L X := {
    eq_of_smul_eq_smul := by
      intro g h hgh
      apply hdual
      apply LinearMap.ext
      intro v
      by_cases hv : v = 0
      · simp only [hv, map_zero]
      · exact congrArg Subtype.val (hgh ⟨v, hv⟩) }
  have hdualRank :
      Module.finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 2 := by
    rw [Subspace.dual_finrank_eq, hdim]
  have hX : Nat.card X = 3 := by
    letI : Fintype (Module.Dual (ZMod 2) V) := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      ← Nat.card_eq_fintype_card,
      Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, hdualRank]
    norm_num
  have horbit := faithful_three_on_three_orbitQuotient_card L X hL hX
  let e : Quotient (representationNonzeroOrbitRel rho.dual) ≃
      MulAction.orbitRel.Quotient L X :=
    Quotient.congr (Equiv.refl X) (by
      intro x y
      constructor
      · rintro ⟨g, hg⟩
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
        refine ⟨g⁻¹, ?_⟩
        apply Subtype.ext
        calc
          rho.dual g⁻¹ y.1 = rho.dual g⁻¹ (rho.dual g x.1) :=
            congrArg (rho.dual g⁻¹) hg.symm
          _ = x.1 := by
            change (rho.dual g⁻¹ * rho.dual g) x.1 = x.1
            rw [← map_mul, inv_mul_cancel, map_one]
            rfl
      · intro hxy
        rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxy
        obtain ⟨g, hg⟩ := hxy
        refine ⟨g⁻¹, ?_⟩
        calc
          rho.dual g⁻¹ x.1 = rho.dual g⁻¹ (rho.dual g y.1) :=
            congrArg (rho.dual g⁻¹) (congrArg Subtype.val hg).symm
          _ = y.1 := by
            change (rho.dual g⁻¹ * rho.dual g) y.1 = y.1
            rw [← map_mul, inv_mul_cancel, map_one]
            rfl)
  rw [Nat.card_congr e]
  exact horbit

/-- Witness form of the preceding one-orbit theorem.  This is convenient
when the order-three action is embedded into a larger local Hall action. -/
theorem binaryPlane_dual_nonzero_transitive
    {L V : Type} [Group L] [Finite L]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) L V)
    (hL : Nat.card L = 3)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (hrho : Function.Injective rho) :
    ∀ x y : {v : Module.Dual (ZMod 2) V // v ≠ 0},
      ∃ g : L, rho.dual g x.1 = y.1 := by
  have hcard := binaryPlane_dual_nonzero_orbit_card_one rho hL hdim hrho
  have hsub :
      Subsingleton (Quotient (representationNonzeroOrbitRel rho.dual)) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  intro x y
  have heq :
      Quotient.mk (representationNonzeroOrbitRel rho.dual) x =
        Quotient.mk (representationNonzeroOrbitRel rho.dual) y :=
    Subsingleton.elim _ _
  exact Quotient.exact heq

/-- A larger local action is already transitive on nonzero dual vectors if
it contains a faithful order-three source. -/
theorem binaryPlane_dual_nonzero_transitive_of_three_source
    {C L V : Type} [Group C] [Finite C] [Group L]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) L V)
    (f : C →* L)
    (hC : Nat.card C = 3)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (hfaith : Function.Injective (rho.comp f)) :
    ∀ x y : {v : Module.Dual (ZMod 2) V // v ≠ 0},
      ∃ g : L, rho.dual g x.1 = y.1 := by
  intro x y
  obtain ⟨c, hc⟩ :=
    binaryPlane_dual_nonzero_transitive (rho.comp f) hC hdim hfaith x y
  refine ⟨f c, ?_⟩
  simpa only [Representation.dual_apply, MonoidHom.comp_apply, map_inv] using hc

/-- The literal Tracey coefficient is one once its acting subgroup contains
a faithful order-three source on the binary plane. -/
theorem traceyLocalDualOrbitCount_eq_one_of_three_source
    {G I V C : Type} [Group G] [MulAction G I]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    [Group C] [Finite C]
    (i : I)
    (rho : Representation (ZMod 2) (MulAction.stabilizer G i) V)
    (N : Subgroup G) (P : Subgroup N)
    (f : C →* traceyPrimeToCoreSubgroup i N P)
    (hC : Nat.card C = 3)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (hfaith : Function.Injective
      (rho.comp ((traceyPrimeToCoreSubgroup i N P).subtype.comp f))) :
    traceyLocalDualOrbitCount i rho N P = 1 := by
  let L := traceyPrimeToCoreSubgroup i N P
  let sigma : Representation (ZMod 2) L V := rho.comp L.subtype
  have htrans := binaryPlane_dual_nonzero_transitive_of_three_source
    sigma f hC hdim (by simpa only [sigma, L, MonoidHom.comp_assoc] using hfaith)
  have hX : Nonempty {v : Module.Dual (ZMod 2) V // v ≠ 0} := by
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : Finite (Module.Dual (ZMod 2) V) :=
      Module.finite_of_finite (ZMod 2)
    have hcard : Nat.card (Module.Dual (ZMod 2) V) = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Subspace.dual_finrank_eq, hdim]
      norm_num
    letI : Nontrivial (Module.Dual (ZMod 2) V) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : Module.Dual (ZMod 2) V)
    exact ⟨⟨v, hv⟩⟩
  unfold traceyLocalDualOrbitCount
  change Nat.card (Quotient (representationNonzeroOrbitRel sigma.dual)) = 1
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨?_⟩,
    hX.map (Quotient.mk (representationNonzeroOrbitRel sigma.dual))⟩
  intro q₁ q₂
  induction q₁ using Quotient.inductionOn with
  | _ x =>
    induction q₂ using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      exact htrans x y

/-- A surjective order-three quotient of the literal Tracey subgroup is
enough.  This is the form produced by the actual odd Hall subgroup: its
local component maps onto the displayed `C₃`, but no choice of a splitting
is made or needed. -/
theorem binaryPlane_dual_nonzero_transitive_of_surjective_three_quotient
    {C L V : Type} [Group C] [Finite C] [Group L]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (sigma : Representation (ZMod 2) C V)
    (rho : Representation (ZMod 2) L V)
    (f : L →* C) (hf : Function.Surjective f)
    (hC : Nat.card C = 3)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (hsigma : Function.Injective sigma)
    (hfactor : rho = sigma.comp f) :
    ∀ x y : {v : Module.Dual (ZMod 2) V // v ≠ 0},
      ∃ g : L, rho.dual g x.1 = y.1 := by
  intro x y
  obtain ⟨c, hc⟩ :=
    binaryPlane_dual_nonzero_transitive sigma hC hdim hsigma x y
  obtain ⟨g, rfl⟩ := hf c
  refine ⟨g, ?_⟩
  simpa only [hfactor, Representation.dual_apply,
    MonoidHom.comp_apply, map_inv] using hc

/-- Quotient form of the local Tracey coefficient.  The acting subgroup
may be much larger than order three; all that is used is its actual
surjection onto the faithful local ternary action. -/
theorem traceyLocalDualOrbitCount_eq_one_of_surjective_three_quotient
    {G I V C : Type} [Group G] [MulAction G I]
    [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    [Group C] [Finite C]
    (i : I)
    (rho : Representation (ZMod 2) (MulAction.stabilizer G i) V)
    (N : Subgroup G) (P : Subgroup N)
    (sigma : Representation (ZMod 2) C V)
    (f : traceyPrimeToCoreSubgroup i N P →* C)
    (hf : Function.Surjective f)
    (hC : Nat.card C = 3)
    (hdim : Module.finrank (ZMod 2) V = 2)
    (hsigma : Function.Injective sigma)
    (hfactor : rho.comp
        (traceyPrimeToCoreSubgroup i N P).subtype = sigma.comp f) :
    traceyLocalDualOrbitCount i rho N P = 1 := by
  let L := traceyPrimeToCoreSubgroup i N P
  let rhoL : Representation (ZMod 2) L V := rho.comp L.subtype
  have htrans :=
    binaryPlane_dual_nonzero_transitive_of_surjective_three_quotient
      sigma rhoL f hf hC hdim hsigma (by
        simpa only [rhoL, L] using hfactor)
  have hX : Nonempty {v : Module.Dual (ZMod 2) V // v ≠ 0} := by
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : Finite (Module.Dual (ZMod 2) V) :=
      Module.finite_of_finite (ZMod 2)
    have hcard : Nat.card (Module.Dual (ZMod 2) V) = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
        Subspace.dual_finrank_eq, hdim]
      norm_num
    letI : Nontrivial (Module.Dual (ZMod 2) V) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    obtain ⟨v, hv⟩ := exists_ne (0 : Module.Dual (ZMod 2) V)
    exact ⟨⟨v, hv⟩⟩
  unfold traceyLocalDualOrbitCount
  change Nat.card (Quotient (representationNonzeroOrbitRel rhoL.dual)) = 1
  apply Nat.card_eq_one_iff_unique.mpr
  refine ⟨⟨?_⟩,
    hX.map (Quotient.mk (representationNonzeroOrbitRel rhoL.dual))⟩
  intro q₁ q₂
  induction q₁ using Quotient.inductionOn with
  | _ x =>
    induction q₂ using Quotient.inductionOn with
    | _ y =>
      apply Quotient.sound
      exact htrans x y

end SymmetricSubgroupAsymptotics

end
