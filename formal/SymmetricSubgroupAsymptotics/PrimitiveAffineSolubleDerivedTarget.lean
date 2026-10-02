import SymmetricSubgroupAsymptotics.PrimitiveAffineProfileStructure
import SymmetricSubgroupAsymptotics.Non2PreE7AffineModel

/-!
# Soluble primitive affine groups as derived cyclic targets

This file derives the sharp source exponent for a soluble primitive affine
group directly from its regular normal subgroup.  The proof is intrinsic:
the point stabilizer is the literal complement, its derived series is lifted
through the canonical semidirect projection, and a coordinate character of
the elementary-abelian regular subgroup supplies the separating character.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical IsMulCommutative commutatorElement

namespace SymmetricSubgroupAsymptotics

/-- Derived-length data for an arbitrary nontrivial finite soluble group. -/
structure SolubleDerivedLength (G : Type) [Group G] where
  t : ℕ
  top_eq : derivedSeries G (t + 1) = ⊥
  prev_ne : derivedSeries G t ≠ ⊥

namespace SolubleDerivedLength

theorem nonempty (G : Type) [Group G] [IsSolvable G] (hG : Nontrivial G) :
    Nonempty (SolubleDerivedLength G) := by
  classical
  letI : Nontrivial G := hG
  have hex : ∃ n, derivedSeries G n = ⊥ := (isSolvable_def G).mp inferInstance
  let n := Nat.find hex
  have hn : derivedSeries G n = ⊥ := Nat.find_spec hex
  have hn0 : n ≠ 0 := by
    intro h0
    have : derivedSeries G 0 = ⊥ := h0 ▸ hn
    simpa [derivedSeries_zero] using this
  refine ⟨⟨n - 1, ?_, ?_⟩⟩
  · rw [Nat.sub_add_cancel (Nat.pos_of_ne_zero hn0)]
    exact hn
  · exact Nat.find_min hex (by omega)

theorem exists_ne_one {G : Type} [Group G] (D : SolubleDerivedLength G) :
    ∃ g : G, g ∈ derivedSeries G D.t ∧ g ≠ 1 := by
  obtain ⟨⟨g, hgt⟩, hg⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.prev_ne
  exact ⟨g, hgt, fun h => hg (Subtype.ext h)⟩

end SolubleDerivedLength

namespace PrimitiveAffineProfile

variable {L Ω : Type} [Group L] [MulAction L Ω]
  (P : PrimitiveAffineProfile L Ω)

/-- The canonical quotient from the affine group to the point stabilizer. -/
def complementProjection (x : Ω) : L →* P.complement x :=
  SemidirectProduct.rightHom.comp (P.semidirectEquiv x).symm.toMonoidHom

theorem complementProjection_surjective (x : Ω) :
    Function.Surjective (P.complementProjection x) := by
  intro h
  refine ⟨P.semidirectEquiv x (SemidirectProduct.inr h), ?_⟩
  simp [complementProjection]

/-- The kernel of the canonical affine projection is exactly the regular
translation subgroup. -/
theorem complementProjection_ker (x : Ω) :
    (P.complementProjection x).ker = P.V := by
  ext g
  constructor
  · intro hg
    let z := (P.semidirectEquiv x).symm g
    have hr : z.right = 1 := by
      have hmap := (MonoidHom.mem_ker).mp hg
      change ((P.semidirectEquiv x).symm g).right = 1 at hmap
      exact hmap
    have hz : z = SemidirectProduct.inl z.left := by
      apply SemidirectProduct.ext
      · simp
      · simpa [z] using hr
    have hvalue : g = (z.left : L) := by
      calc
        g = P.semidirectEquiv x z := by simp [z]
        _ = P.semidirectEquiv x (SemidirectProduct.inl z.left) :=
          congrArg (P.semidirectEquiv x) hz
        _ = (z.left : L) := by simp [semidirectEquiv]
    rw [hvalue]
    exact z.left.2
  · intro hg
    let v : P.V := ⟨g, hg⟩
    have hvalue : P.semidirectEquiv x (SemidirectProduct.inl v) = g := by
      simp [semidirectEquiv, SemidirectProduct.mulEquivSubgroup, v]
    rw [MonoidHom.mem_ker]
    rw [← hvalue]
    change SemidirectProduct.rightHom
      ((P.semidirectEquiv x).symm
        (P.semidirectEquiv x (SemidirectProduct.inl v))) = 1
    rw [MulEquiv.symm_apply_apply]
    rfl

/-- The regular subgroup is self-centralizing in a faithful primitive affine
action. -/
theorem selfCentralizing [Finite L] [Finite Ω] [Nontrivial Ω]
    [FaithfulSMul L Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω)
    (g : L) (hg : ∀ v ∈ P.V, g * v = v * g) : g ∈ P.V := by
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  let x : Ω := Classical.arbitrary Ω
  let u : P.V := Classical.choose (P.regular x (g • x))
  have hux : (u : L) • x = g • x :=
    (Classical.choose_spec (P.regular x (g • x))).1
  have hsame : ∀ y : Ω, (u : L) • y = g • y := by
    intro y
    let v : P.V := Classical.choose (P.regular x y)
    have hvx : (v : L) • x = y :=
      (Classical.choose_spec (P.regular x y)).1
    have hcomm : g * (v : L) = (v : L) * g := hg v v.2
    calc
      (u : L) • y = (u : L) • ((v : L) • x) := by rw [hvx]
      _ = ((u : L) * (v : L)) • x := (mul_smul _ _ _).symm
      _ = ((v : L) * (u : L)) • x := by
        congr 1
        exact congrArg Subtype.val (mul_comm u v)
      _ = (v : L) • ((u : L) • x) := by rw [mul_smul]
      _ = (v : L) • (g • x) := by rw [hux]
      _ = ((v : L) * g) • x := (mul_smul _ _ _).symm
      _ = (g * (v : L)) • x := by rw [hcomm]
      _ = g • ((v : L) • x) := by rw [mul_smul]
      _ = g • y := by rw [hvx]
  have hgu : g = (u : L) := by
    apply FaithfulSMul.eq_of_smul_eq_smul (α := Ω)
    exact fun y => (hsame y).symm
  rw [hgu]
  exact u.2

/-- A nonidentity complement element has a nontrivial commutator with the
regular subgroup inside every derived term mapping onto it. -/
theorem comm_ne_bot_of_projection
    [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (H : Subgroup L) (r : P.complement x) (hr : r ≠ 1)
    (hH : ∃ y ∈ H, P.complementProjection x y = r) :
    ⁅H, P.V⁆ ≠ ⊥ := by
  obtain ⟨y, hyH, hyr⟩ := hH
  intro hbot
  have hcomm : ∀ v ∈ P.V, y * v = v * y := by
    intro v hv
    have hm : ⁅y, v⁆ ∈ ⁅H, P.V⁆ :=
      Subgroup.commutator_mem_commutator hyH hv
    rw [hbot] at hm
    have hone : ⁅y, v⁆ = 1 := Subgroup.mem_bot.mp hm
    exact commutatorElement_eq_one_iff_mul_comm.mp hone
  have hyV : y ∈ P.V := P.selfCentralizing hprimitive y hcomm
  have hyker : P.complementProjection x y = 1 := by
    rw [← MonoidHom.mem_ker, P.complementProjection_ker x]
    exact hyV
  exact hr (hyr.symm.trans hyker)

/-- The `(t+1)`-st derived subgroup is the translation subgroup when the
point stabilizer has derived length `t+1`. -/
theorem derived_eq_translation
    [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (D : SolubleDerivedLength (P.complement x)) :
    derivedSeries L (D.t + 1) = P.V := by
  let π := P.complementProjection x
  have hsurj : Function.Surjective π := P.complementProjection_surjective x
  apply le_antisymm
  · intro y hy
    have hm := map_derivedSeries_le_derivedSeries π (D.t + 1) ⟨y, hy, rfl⟩
    rw [D.top_eq] at hm
    have hyker : y ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      exact Subgroup.mem_bot.mp hm
    simpa [π, P.complementProjection_ker x] using hyker
  · have hcomm : ∀ k, k ≤ D.t → ⁅derivedSeries L k, P.V⁆ ≠ ⊥ := by
      intro k hk
      obtain ⟨r, hrt, hr⟩ := SolubleDerivedLength.exists_ne_one D
      have hrk : r ∈ derivedSeries (P.complement x) k :=
        derivedSeries_antitone _ hk hrt
      rw [← map_derivedSeries_eq hsurj k] at hrk
      obtain ⟨y, hy, hyr⟩ := hrk
      exact P.comm_ne_bot_of_projection hprimitive x (derivedSeries L k)
        r hr ⟨y, hy, hyr⟩
    have hk : ∀ k, k ≤ D.t + 1 → P.V ≤ derivedSeries L k := by
      intro k
      induction k with
      | zero =>
          intro _
          rw [derivedSeries_zero]
          exact le_top
      | succ k ih =>
          intro hkt
          have hprev := ih (by omega)
          have hne := hcomm k (by omega)
          have hnorm : (⁅derivedSeries L k, P.V⁆).Normal :=
            Subgroup.commutator_normal _ _
          rcases P.minimal hprimitive _ hnorm (Subgroup.commutator_le_right _ _) with h | h
          · exact absurd h hne
          · rw [← h, derivedSeries_succ]
            exact Subgroup.commutator_mono le_rfl hprev
    exact hk (D.t + 1) le_rfl

/-- Type-valued elementary chart extracted from the structural theorem. -/
structure ElementaryChart
    [Finite L] [Finite Ω] [Nontrivial Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) where
  [primeFact : Fact P.p.Prime]
  V : Type
  [addCommGroup : AddCommGroup V]
  [module : Module (ZMod P.p) V]
  [finiteDimensional : FiniteDimensional (ZMod P.p) V]
  [nontrivial : Nontrivial V]
  equiv : P.V ≃* Multiplicative V

attribute [instance]
  ElementaryChart.primeFact ElementaryChart.addCommGroup ElementaryChart.module
  ElementaryChart.finiteDimensional ElementaryChart.nontrivial

theorem elementaryChart_nonempty
    [Finite L] [Finite Ω] [Nontrivial Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) :
    Nonempty (P.ElementaryChart hprimitive) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  obtain ⟨V, iadd, imod, ifd, e⟩ := P.elementary hprimitive
  letI : AddCommGroup V := iadd
  letI : Module (ZMod P.p) V := imod
  letI : FiniteDimensional (ZMod P.p) V := ifd
  have hPV : Nontrivial P.V := by
    let x : Ω := Classical.arbitrary Ω
    obtain ⟨y, hy⟩ := exists_ne x
    let v : P.V := Classical.choose (P.regular x y)
    have hvxy : v • x = y := (Classical.choose_spec (P.regular x y)).1
    refine ⟨v, 1, ?_⟩
    intro hv
    apply hy
    rw [← hvxy, hv, one_smul]
  letI : Nontrivial P.V := hPV
  letI : Nontrivial V := e.some.injective.nontrivial
  exact ⟨{ V := V, equiv := e.some }⟩

/-- A chosen elementary chart. -/
noncomputable def elementaryChart
    [Finite L] [Finite Ω] [Nontrivial Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) :
    P.ElementaryChart hprimitive :=
  Classical.choice (P.elementaryChart_nonempty hprimitive)

namespace ElementaryChart

variable [Finite L] [Finite Ω] [Nontrivial Ω]
  {hprimitive : MulAction.IsPreprimitive L Ω}
  (C : P.ElementaryChart hprimitive)

def d : ℕ := by
  letI : Fact P.p.Prime := C.primeFact
  exact Module.finrank (ZMod P.p) C.V

theorem d_pos : 0 < C.d := by
  letI : Fact P.p.Prime := C.primeFact
  exact Module.finrank_pos_iff.mpr inferInstance

def standardEquiv : P.V ≃* Multiplicative (Fin C.d → ZMod P.p) := by
  letI : Fact P.p.Prime := C.primeFact
  exact C.equiv.trans
    (Module.finBasis (ZMod P.p) C.V).equivFun.toAddEquiv.toMultiplicative

def character : P.V →* Multiplicative (ZMod P.p) := by
  letI : Fact P.p.Prime := C.primeFact
  exact
    { toFun := fun v => Multiplicative.ofAdd
        (Multiplicative.toAdd (standardEquiv P C v) ⟨0, d_pos P C⟩)
      map_one' := by simp [standardEquiv]
      map_mul' := by
        intro a c
        simp [standardEquiv] }

theorem character_ne_one : character P C ≠ 1 := by
  letI : Fact P.p.Prime := C.primeFact
  let z : Fin (d P C) → ZMod P.p := Pi.single ⟨0, d_pos P C⟩ 1
  let v : P.V := (standardEquiv P C).symm (Multiplicative.ofAdd z)
  intro h
  have hv := DFunLike.congr_fun h v
  change Multiplicative.ofAdd
      (Multiplicative.toAdd (standardEquiv P C v) ⟨0, d_pos P C⟩) = 1 at hv
  have hz : z ⟨0, d_pos P C⟩ = 1 := Pi.single_eq_same _ _
  have h10 : (1 : ZMod P.p) = 0 :=
    Multiplicative.ofAdd.injective (by simpa [v, z] using hv)
  exact one_ne_zero h10

end ElementaryChart

/-- A concrete nontrivial `C_p` character of the elementary translation
subgroup. -/
def elementaryCharacter
    [Finite L] [Finite Ω] [Nontrivial Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) :
    letI : Fact P.p.Prime := ⟨P.p_prime⟩
    P.V →* Multiplicative (ZMod P.p) := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  exact ElementaryChart.character P (P.elementaryChart hprimitive)

theorem elementaryCharacter_ne_one
    [Finite L] [Finite Ω] [Nontrivial Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) :
    letI : Fact P.p.Prime := ⟨P.p_prime⟩
    P.elementaryCharacter hprimitive ≠ 1 := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  exact ElementaryChart.character_ne_one P (P.elementaryChart hprimitive)

/-- Every nontrivial soluble primitive affine group is a derived cyclic
target over the prime of its translation subgroup. -/
def derivedCyclicTarget
    [Finite L] [Finite Ω] [Nontrivial Ω] [FaithfulSMul L Ω]
    (hprimitive : MulAction.IsPreprimitive L Ω) (x : Ω)
    (D : SolubleDerivedLength (P.complement x)) :
    letI : Fact P.p.Prime := ⟨P.p_prime⟩
    DerivedHead.DerivedCyclicTarget L P.V D.t P.p := by
  letI : Fact P.p.Prime := ⟨P.p_prime⟩
  letI : IsMulCommutative P.V := P.isMulCommutative hprimitive
  exact
    { derived_eq := P.derived_eq_translation hprimitive x D
      character := P.elementaryCharacter hprimitive
      self_centralizing := P.selfCentralizing hprimitive
      absorbing := by
        intro W hW hWV
        rcases P.minimal hprimitive W hW hWV with h | h
        · rw [h]
          exact bot_le
        · obtain ⟨r, hrt, hr⟩ := SolubleDerivedLength.exists_ne_one D
          have hrmap : r ∈ (derivedSeries L D.t).map (P.complementProjection x) := by
            rw [map_derivedSeries_eq (P.complementProjection_surjective x) D.t]
            exact hrt
          obtain ⟨y, hy, hyr⟩ := hrmap
          have hne := P.comm_ne_bot_of_projection hprimitive x
            (derivedSeries L D.t) r hr ⟨y, hy, hyr⟩
          have hnorm : (⁅derivedSeries L D.t, P.V⁆).Normal :=
            Subgroup.commutator_normal _ _
          rcases P.minimal hprimitive _ hnorm
              (Subgroup.commutator_le_right _ _) with h' | h'
          · exact absurd h' hne
          · rw [h]
            exact h'.symm.le
      separating := DerivedHead.separating_of_minimal
        (P.minimal hprimitive) _ (P.elementaryCharacter_ne_one hprimitive) }

end PrimitiveAffineProfile
end SymmetricSubgroupAsymptotics

end
