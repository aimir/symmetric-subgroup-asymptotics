import SymmetricSubgroupAsymptotics.NormalSubgroupOrbitIndex
import SymmetricSubgroupAsymptotics.PrimeCharacterSubgroupCapacity

/-! Exact orbit counts for the common kernel of an injected family of
original prime characters. The exponent counts exactly the retained
characters vanishing on the original point stabilizer. -/
set_option autoImplicit false
noncomputable section
namespace SymmetricSubgroupAsymptotics

variable (p : ℕ) [Fact p.Prime]
    {G X V : Type*} [Group G] [MulAction G X]
    [AddCommGroup V] [Module (ZMod p) V]
    (χ : V →ₗ[ZMod p] PrimeCharacters p G) (x : X)

/-- The image of the original point stabilizer in the dual of precisely
the retained character space. -/
def retainedStabilizerImage : Submodule (ZMod p) (Module.Dual (ZMod p) V) :=
  AddSubgroup.toZModSubmodule p (Subgroup.toAddSubgroup'
    ((MulAction.stabilizer G x).map (retainedCharacterEvaluation p χ)))

/-- The retained characters that vanish on the original point stabilizer. -/
def retainedStabilizerVanishing : Submodule (ZMod p) V :=
  (retainedStabilizerImage p χ x).dualCoannihilator

theorem mem_retainedStabilizerVanishing_iff (v : V) :
    v ∈ retainedStabilizerVanishing p χ x ↔
      ∀ g : G, g ∈ MulAction.stabilizer G x → χ v (Additive.ofMul g)=0 := by
  change v ∈ (retainedStabilizerImage p χ x).dualCoannihilator ↔ _
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro hv g hg
    exact hv ((retainedCharacterEvaluation p χ g).toAdd)
      (show (retainedCharacterEvaluation p χ g).toAdd ∈
        retainedStabilizerImage p χ x from ⟨g,hg,rfl⟩)
  · intro hv f hf
    change Multiplicative.ofAdd f ∈
      (MulAction.stabilizer G x).map (retainedCharacterEvaluation p χ) at hf
    obtain ⟨g,hg,hgf⟩ := hf
    have h := congrArg (fun y : Multiplicative (Module.Dual (ZMod p) V) => y.toAdd v) hgf
    exact h.symm.trans (hv g hg)

/-- Its group kernel is the literal common kernel of all retained
characters, including all correlations among them. -/
theorem mem_retainedCharacterEvaluation_ker_iff (g : G) :
    g ∈ (retainedCharacterEvaluation p χ).ker ↔
      ∀ v : V, χ v (Additive.ofMul g)=0 := by
  change retainedCharacterEvaluation p χ g = 1 ↔ _
  constructor
  · intro h v
    exact congrArg (fun y : Multiplicative (Module.Dual (ZMod p) V) => y.toAdd v) h
  · intro h
    change (retainedCharacterEvaluation p χ g).toAdd = 0
    ext v
    exact h v

variable [Finite G] [Finite V]

theorem retainedStabilizerImage_index :
    ((MulAction.stabilizer G x).map (retainedCharacterEvaluation p χ)).index =
      p ^ Module.finrank (ZMod p) (retainedStabilizerVanishing p χ x) := by
  let S := (MulAction.stabilizer G x).map (retainedCharacterEvaluation p χ)
  have hs : Nat.card S = p ^ Module.finrank (ZMod p) (retainedStabilizerImage p χ x) := by
    change Nat.card (retainedStabilizerImage p χ x) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod]
  have hv : Nat.card (Multiplicative (Module.Dual (ZMod p) V)) =
      p ^ Module.finrank (ZMod p) V := by
    change Nat.card (Module.Dual (ZMod p) V) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod p),Nat.card_zmod,
      Subspace.dual_finrank_eq]
  have hd := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (retainedStabilizerImage p χ x)
  change Module.finrank (ZMod p) (retainedStabilizerImage p χ x) +
    Module.finrank (ZMod p) (retainedStabilizerVanishing p χ x) =
      Module.finrank (ZMod p) V at hd
  apply Nat.eq_of_mul_eq_mul_right
    (pow_pos (Fact.out : p.Prime).pos (Module.finrank (ZMod p)
      (retainedStabilizerImage p χ x)))
  calc
    S.index * p ^ Module.finrank (ZMod p) (retainedStabilizerImage p χ x) =
        p ^ Module.finrank (ZMod p) V := by rw [← hs,S.index_mul_card,hv]
    _ = p ^ Module.finrank (ZMod p) (retainedStabilizerVanishing p χ x) *
        p ^ Module.finrank (ZMod p) (retainedStabilizerImage p χ x) := by
      rw [← pow_add,add_comm,hd]

variable [MulAction.IsPretransitive G X]

/-- The exact number of common-kernel orbits is determined by the
retained characters vanishing on the original stabilizer. -/
theorem retainedCharacterKernel_orbit_classes_card (hχ : Function.Injective χ) :
    Nat.card (MulAction.orbitRel.Quotient (retainedCharacterEvaluation p χ).ker X) =
      p ^ Module.finrank (ZMod p) (retainedStabilizerVanishing p χ x) := by
  rw [kernel_orbit_classes_card_eq_image_index x (retainedCharacterEvaluation p χ)
    (retainedCharacterEvaluation_surjective p χ hχ)]
  exact retainedStabilizerImage_index p χ x

/-- Actual orbit size times actual orbit number is the physical degree. -/
theorem retainedCharacterKernel_orbit_card_mul (hχ : Function.Injective χ)
    (o : MulAction.orbitRel.Quotient (retainedCharacterEvaluation p χ).ker X) :
    Nat.card o.orbit * p ^ Module.finrank (ZMod p)
      (retainedStabilizerVanishing p χ x) = Nat.card X := by
  rw [← retainedCharacterKernel_orbit_classes_card p χ x hχ,
    normal_orbit_card_eq (retainedCharacterEvaluation p χ).ker x o]
  exact normal_orbit_card_mul_classes (retainedCharacterEvaluation p χ).ker x

variable [Finite X]

theorem retainedStabilizerVanishing_finrank_le_degree_exponent
    (hχ : Function.Injective χ) (a : ℕ) (hdegree : Nat.card X=p^a) :
    Module.finrank (ZMod p) (retainedStabilizerVanishing p χ x) ≤ a := by
  let o : MulAction.orbitRel.Quotient (retainedCharacterEvaluation p χ).ker X :=
    Quotient.mk'' x
  haveI : Nonempty o.orbit := ⟨⟨x,MulAction.mem_orbit_self x⟩⟩
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
  calc
    _ = 1 * p ^ Module.finrank (ZMod p) (retainedStabilizerVanishing p χ x) := by
      rw [one_mul]
    _ ≤ Nat.card o.orbit * p ^ Module.finrank (ZMod p)
        (retainedStabilizerVanishing p χ x) :=
      Nat.mul_le_mul_right _ (Nat.card_pos (α := o.orbit))
    _ = p^a := (retainedCharacterKernel_orbit_card_mul p χ x hχ o).trans hdegree

/-- Every original common-kernel orbit has exactly the complementary
prime-power size. No orbit lengths are supplied as hypotheses. -/
theorem retainedCharacterKernel_orbit_card (hχ : Function.Injective χ)
    (a : ℕ) (hdegree : Nat.card X=p^a)
    (o : MulAction.orbitRel.Quotient (retainedCharacterEvaluation p χ).ker X) :
    Nat.card o.orbit = p^(a-Module.finrank (ZMod p)
      (retainedStabilizerVanishing p χ x)) := by
  have hj := retainedStabilizerVanishing_finrank_le_degree_exponent p χ x hχ a hdegree
  apply Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos
    (Module.finrank (ZMod p) (retainedStabilizerVanishing p χ x)))
  rw [retainedCharacterKernel_orbit_card_mul p χ x hχ o,hdegree,
    ← pow_add,Nat.sub_add_cancel hj]

end SymmetricSubgroupAsymptotics
