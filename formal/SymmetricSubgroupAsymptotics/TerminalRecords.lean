import SymmetricSubgroupAsymptotics.BinaryFrameIncidence

/-!
# The original terminal quotient-record divisor

For a fixed graph map into `V/U`, all linear lifts are counted, and every
ordered basis of the actual kernel `U` is retained. This gives the exact
`|GL(u,2)| 2^(ud)` multiplicity before any condition or weight on the graph
is estimated. The result does not assert that the graph's central extension
splits: that condition belongs to the retained annihilator in the next step.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace SymmetricSubgroupAsymptotics

variable {A V : Type*} [AddCommGroup A] [Module (ZMod 2) A]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Literal linear lifts of a fixed quotient graph map. -/
abbrev TerminalLinearLifts (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) :=
  {g : A →ₗ[ZMod 2] V // U.mkQ.comp g = f}

/-- A linear lift exists because the source is a vector space. -/
theorem terminalLinearLifts_nonempty (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) : Nonempty (TerminalLinearLifts U f) := by
  obtain ⟨s, hs⟩ := U.mkQ.exists_rightInverse_of_surjective U.range_mkQ
  exact ⟨⟨s.comp f, by rw [← LinearMap.comp_assoc, hs, LinearMap.id_comp]⟩⟩

/-- After one actual lift is chosen, the fibre is a torsor under maps into
the actual kernel. No lifts are identified with one another. -/
def terminalLinearLiftsEquiv (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) (g₀ : TerminalLinearLifts U f) :
    TerminalLinearLifts U f ≃ (A →ₗ[ZMod 2] U) where
  toFun g := (g.1 - g₀.1).codRestrict U (by
    intro a
    apply U.ker_mkQ ▸ show (g.1 - g₀.1) a ∈ U.mkQ.ker from ?_
    change U.mkQ (g.1 a - g₀.1 a) = 0
    have h := congrArg (fun h : A →ₗ[ZMod 2] V ⧸ U ↦ h a)
      (g.2.trans g₀.2.symm)
    simpa only [map_sub, sub_eq_zero, LinearMap.comp_apply] using h)
  invFun k := ⟨g₀.1 + U.subtype.comp k, by
    ext a
    have h := congrArg (fun h : A →ₗ[ZMod 2] V ⧸ U ↦ h a) g₀.2
    have hk : U.mkQ (k a : V) = 0 := by
      exact show (k a : V) ∈ U.mkQ.ker from U.ker_mkQ.symm ▸ (k a).2
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, map_add,
      Submodule.subtype_apply, hk, add_zero] using h⟩
  left_inv g := by apply Subtype.ext; ext a; simp
  right_inv k := by ext a; simp

/-- The original lift factor, without any quotient by automorphisms. -/
theorem terminalLinearLifts_card [Finite A] [Finite V]
    (U : Submodule (ZMod 2) V) (f : A →ₗ[ZMod 2] V ⧸ U) :
    Nat.card (TerminalLinearLifts U f) =
      2 ^ (Module.finrank (ZMod 2) A * Module.finrank (ZMod 2) U) := by
  let g₀ := Classical.choice (terminalLinearLifts_nonempty U f)
  rw [Nat.card_congr (terminalLinearLiftsEquiv U f g₀),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Module.finrank_linearMap]
  simp

/-- A quotient record consists of an ordered basis of its actual vertical
kernel and a literal lift of its actual graph map. -/
abbrev TerminalQuotientRecords (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) :=
  BinaryIncidenceFrames (Module.finrank (ZMod 2) U) (fun S ↦ S = U) ×
    TerminalLinearLifts U f

private theorem terminalOrderedBases_card [Finite V] (U : Submodule (ZMod 2) V) :
    Nat.card (BinaryIncidenceFrames (Module.finrank (ZMod 2) U) (fun S ↦ S = U)) =
      ∏ i : Fin (Module.finrank (ZMod 2) U),
        (2 ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ)) := by
  rw [binaryIncidenceFrames_card]
  have h : Nat.card {S : Submodule (ZMod 2) V //
      Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) U ∧ S = U} = 1 := by
    let e : {S : Submodule (ZMod 2) V //
        Module.finrank (ZMod 2) S = Module.finrank (ZMod 2) U ∧ S = U} ≃ Unit :=
      { toFun := fun _ ↦ ()
        invFun := fun _ ↦ ⟨U, rfl, rfl⟩
        left_inv := fun S ↦ Subtype.ext S.2.2.symm
        right_inv := fun x ↦ by cases x; rfl }
    simpa using Nat.card_congr e
  rw [h, one_mul]

/-- Exact original divisor for a fixed graph. In particular arbitrary
conditions on the graph can be imposed before this identity is used. -/
theorem terminalQuotientRecords_card [Finite A] [Finite V]
    (U : Submodule (ZMod 2) V) (f : A →ₗ[ZMod 2] V ⧸ U) :
    Nat.card (TerminalQuotientRecords U f) =
      (∏ i : Fin (Module.finrank (ZMod 2) U),
        (2 ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ))) *
      2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) A) := by
  rw [Nat.card_prod, terminalOrderedBases_card, terminalLinearLifts_card, mul_comm
    (Module.finrank (ZMod 2) A) (Module.finrank (ZMod 2) U)]

/-- The same records as literal maps on the ordered kernel coordinates and
the complete elementary quotient of the exterior. -/
abbrev TerminalRecordMaps (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) :=
  {p : ((Fin (Module.finrank (ZMod 2) U) → ZMod 2) × A) →ₗ[ZMod 2] V //
    Function.Injective (p.comp (LinearMap.inl _ _ _)) ∧
    (p.comp (LinearMap.inl _ _ _)).range = U ∧
    U.mkQ.comp (p.comp (LinearMap.inr _ _ _)) = f}

/-- Reversible conversion from ordered bases and lifts to the manuscript's
literal record map. The source coordinates are not quotiented. -/
def terminalQuotientRecordsEquivMaps (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) :
    TerminalQuotientRecords U f ≃ TerminalRecordMaps U f :=
  (Equiv.prodCongr (binaryIncidenceFramesEquivMaps _ (fun S ↦ S = U))
    (Equiv.refl _)).trans
  { toFun := fun r ↦ ⟨r.1.1.coprod r.2.1, by
      simpa using And.intro r.1.2.1 (And.intro r.1.2.2 r.2.2)⟩
    invFun := fun p ↦
      (⟨p.1.comp (LinearMap.inl _ _ _), p.2.1, p.2.2.1⟩,
       ⟨p.1.comp (LinearMap.inr _ _ _), p.2.2.2⟩)
    left_inv := fun r ↦ by
      apply Prod.ext <;> apply Subtype.ext <;> simp
    right_inv := fun p ↦ by apply Subtype.ext; simp }

theorem terminalRecordMaps_card [Finite A] [Finite V]
    (U : Submodule (ZMod 2) V) (f : A →ₗ[ZMod 2] V ⧸ U) :
    Nat.card (TerminalRecordMaps U f) =
      (∏ i : Fin (Module.finrank (ZMod 2) U),
        (2 ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ))) *
      2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) A) := by
  rw [← Nat.card_congr (terminalQuotientRecordsEquivMaps U f),
    terminalQuotientRecords_card]

/-- The actual graph image, before any central lifting condition. -/
def terminalLinearGraph (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) : Submodule (ZMod 2) (V × A) :=
  (U.mkQ.comp (LinearMap.fst _ _ _) - f.comp (LinearMap.snd _ _ _)).ker

theorem mem_terminalLinearGraph (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) (x : V × A) :
    x ∈ terminalLinearGraph U f ↔ U.mkQ x.1 = f x.2 := by
  simp [terminalLinearGraph, LinearMap.mem_ker, sub_eq_zero]

/-- Each record produces exactly its retained graph, including the whole
exterior coordinate. -/
theorem terminalRecordMaps_image (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) (p : TerminalRecordMaps U f) :
    (p.1.prod (LinearMap.snd _ _ _)).range = terminalLinearGraph U f := by
  ext x
  rw [mem_terminalLinearGraph]
  constructor
  · rintro ⟨⟨b,a⟩,rfl⟩
    have hb : p.1 (b,0) ∈ U := by
      exact p.2.2.1.le ⟨b,rfl⟩
    have hb0 : U.mkQ (p.1 (b,0)) = 0 := by
      exact show p.1 (b,0) ∈ U.mkQ.ker from U.ker_mkQ.symm ▸ hb
    have ha := congrArg (fun h : A →ₗ[ZMod 2] V ⧸ U ↦ h a) p.2.2.2
    change U.mkQ (p.1 (b,a)) = f a
    have he : (b,a) = (b,0) + (0,a) := by simp
    rw [he,map_add,map_add,hb0,zero_add]
    exact ha
  · intro hx
    have ha := congrArg (fun h : A →ₗ[ZMod 2] V ⧸ U ↦ h x.2) p.2.2.2
    have hv : x.1 - p.1 (0,x.2) ∈ U := by
      apply U.ker_mkQ ▸ show x.1 - p.1 (0,x.2) ∈ U.mkQ.ker from ?_
      change U.mkQ (x.1 - p.1 (0,x.2)) = 0
      rw [map_sub,hx,show U.mkQ (p.1 (0,x.2)) = f x.2 from ha,sub_self]
    have hv' : x.1 - p.1 (0,x.2) ∈
        (p.1.comp (LinearMap.inl _ _ _)).range := p.2.2.1.ge hv
    obtain ⟨b,hb⟩ := hv'
    refine ⟨(b,x.2),?_⟩
    apply Prod.ext
    · change p.1 (b,x.2) = x.1
      have he : (b,x.2) = (b,0) + (0,x.2) := by simp
      rw [he,map_add]
      change p.1 (b,0) = x.1 - p.1 (0,x.2) at hb
      rw [hb,sub_add_cancel]
    · rfl

instance [Finite A] [Finite V] (U : Submodule (ZMod 2) V)
    (f : A →ₗ[ZMod 2] V ⧸ U) : Finite (TerminalRecordMaps U f) :=
  Finite.of_injective (fun p : TerminalRecordMaps U f ↦ (p.1 : _ → V))
    (fun _ _ h ↦ Subtype.ext (DFunLike.coe_injective h))

/-- Any weight on the actual image (in particular one computed from its
retained annihilator) keeps the same original divisor. -/
theorem terminalRecordMaps_weight_sum [Finite A] [Finite V]
    (U : Submodule (ZMod 2) V) (f : A →ₗ[ZMod 2] V ⧸ U)
    {M : Type*} [AddCommMonoid M] (w : Submodule (ZMod 2) (V × A) → M) :
    letI := Fintype.ofFinite (TerminalRecordMaps U f)
    (∑ p : TerminalRecordMaps U f, w (p.1.prod (LinearMap.snd _ _ _)).range) =
      ((∏ i : Fin (Module.finrank (ZMod 2) U),
        (2 ^ Module.finrank (ZMod 2) U - 2 ^ (i : ℕ))) *
        2 ^ (Module.finrank (ZMod 2) U * Module.finrank (ZMod 2) A)) •
        w (terminalLinearGraph U f) := by
  classical
  letI := Fintype.ofFinite (TerminalRecordMaps U f)
  simp only [terminalRecordMaps_image, Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, terminalRecordMaps_card]

end SymmetricSubgroupAsymptotics
