import SymmetricSubgroupAsymptotics.PermutationPairOrbitMarks
import SymmetricSubgroupAsymptotics.OddCriticalProfiles
import SymmetricSubgroupAsymptotics.PrimeRelativeCharacters
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Original scalar characters and ordered independent pair-orbit marks

Each actual two-point orbit has its unique nonzero binary character. A
chosen two-point chart constructs it, but its zero set is the literal
pointwise-fixing kernel, which proves independence of chart choices and
naturality under actual point relabelling. Ordered independent selections
are finite marks of the original subgroup for weighted profile assembly.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
attribute [local instance] Fintype.ofFinite

namespace SymmetricSubgroupAsymptotics.PermutationPairOrbitCharacters

open PermutationPairOrbitMarks

variable {X Y : Type*} [Finite X] [Finite Y]
    (H : Subgroup (Equiv.Perm X))

def orbitSet (s : PairOrbit H) : SubMulAction H X where
  carrier := s.val
  smul_mem' g x hx := by
    obtain ⟨a, ha⟩ := s.property.1
    rw [ha] at hx ⊢
    exact MulAction.mem_orbit_of_mem_orbit g hx

def restriction (s : PairOrbit H) : H →* Equiv.Perm s.val :=
  MulAction.toPermHom H (orbitSet H s)

def pointChart (s : PairOrbit H) : s.val ≃ criticalActionPoints .c2 :=
  Fintype.equivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, s.property.2, criticalAction_point_card]
    rfl)

def localAction (s : PairOrbit H) : H →* criticalActionSubgroup .c2 :=
  ((pointChart H s).permCongrHom.toMonoidHom.comp (restriction H s)).codRestrict
    (criticalActionSubgroup .c2) (fun _ => by
      change _ ∈ regularBinaryPermutationGroup 1
      rw [c2_permutationGroup_eq_top]
      trivial)

def sign (s : PairOrbit H) : H →* Multiplicative (ZMod 2) :=
  binaryMarkerLocalEquiv.symm.toMonoidHom.comp (localAction H s)

def character (s : PairOrbit H) : PrimeCharacters 2 H where
  toFun g := (sign H s g.toMul).toAdd
  map_zero' := congrArg Multiplicative.toAdd (map_one (sign H s))
  map_add' g h := congrArg Multiplicative.toAdd ((sign H s).map_mul g.toMul h.toMul)

theorem restriction_eq_one_iff (s : PairOrbit H) (g : H) :
    restriction H s g = 1 ↔ Fixes g.val s.val := by
  constructor
  · intro h x hx
    exact congrArg Subtype.val (Equiv.congr_fun h (⟨x, hx⟩ : s.val))
  · intro h
    apply Equiv.ext
    intro x
    exact Subtype.ext (h x.val x.property)

/-- The original pointwise-fixing kernel characterizes the scalar map. -/
theorem sign_eq_one_iff (s : PairOrbit H) (g : H) :
    sign H s g = 1 ↔ Fixes g.val s.val := by
  change binaryMarkerLocalEquiv.symm (localAction H s g) = 1 ↔ _
  rw [binaryMarkerLocalEquiv.symm.map_eq_one_iff, Subtype.ext_iff]
  change (pointChart H s).permCongrHom (restriction H s g) = 1 ↔ _
  rw [(pointChart H s).permCongrHom.map_eq_one_iff, restriction_eq_one_iff]

theorem character_zero_iff (s : PairOrbit H) (g : H) :
    character H s (Additive.ofMul g) = 0 ↔ Fixes g.val s.val := by
  change sign H s g = 1 ↔ _
  exact sign_eq_one_iff H s g

theorem character_ne_zero (s : PairOrbit H) : character H s ≠ 0 := by
  intro hz
  obtain ⟨x, hx⟩ := s.property.1
  have hfix (g : H) : Fixes g.val s.val :=
    (character_zero_iff H s g).mp (by rw [hz]; rfl)
  have hs : s.val = {x} := by
    ext y
    rw [hx]
    constructor
    · rintro ⟨g, rfl⟩
      exact hfix g x (by rw [hx]; exact MulAction.mem_orbit_self x)
    · intro hy
      change y = x at hy
      rw [hy]
      exact MulAction.mem_orbit_self x
  have hc := s.property.2
  rw [hs] at hc
  norm_num at hc

private theorem binary_eq_iff (a b : ZMod 2) : (a = 0 ↔ b = 0) ↔ a = b := by
  have h : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) ↔ a = b := by decide
  exact h a b

/-- Any scalar construction with the same literal fixing kernel is this
character; this is useful when the original profile already has coordinates. -/
theorem character_eq_of_zero_iff (s : PairOrbit H) (ψ : PrimeCharacters 2 H)
    (hψ : ∀ g : H, ψ (Additive.ofMul g) = 0 ↔ Fixes g.val s.val) :
    ψ = character H s := by
  ext g
  apply (binary_eq_iff _ _).mp
  exact (hψ g).trans (character_zero_iff H s g).symm

/-- Equality is in the character space of the same original subgroup. -/
theorem character_eq_iff (s t : PairOrbit H) :
    character H s = character H t ↔ SameAction H s.val t.val := by
  constructor
  · intro h g hg
    rw [← character_zero_iff H s ⟨g, hg⟩, ← character_zero_iff H t ⟨g, hg⟩, h]
  · intro h
    ext g
    apply (binary_eq_iff _ _).mp
    exact (character_zero_iff H s g).trans
      ((h g.val g.property).trans (character_zero_iff H t g).symm)

def relabelGroup (e : X ≃ Y) : H ≃* relabelSubgroup e H :=
  e.permCongrHom.subgroupMap H

/-- Changing the physical point labels preserves the scalar character on
each corresponding original group element, including any chart choices. -/
theorem character_relabel (e : X ≃ Y) (s : PairOrbit H) (g : H) :
    character (relabelSubgroup e H) (pairOrbitEquiv e H s)
        (Additive.ofMul (relabelGroup H e g)) =
      character H s (Additive.ofMul g) := by
  apply (binary_eq_iff _ _).mp
  rw [character_zero_iff, character_zero_iff]
  exact fixes_image_iff e g.val s.val

@[simp] theorem character_congr (e : X ≃ Y) (s : PairOrbit H) :
    primeCharacterCongr 2 (relabelGroup H e)
      (character (relabelSubgroup e H) (pairOrbitEquiv e H s)) = character H s := by
  ext g
  exact character_relabel H e s g

/-- Ordered selections; independence itself rules out repetitions. -/
abbrev Frame (r : ℕ) :=
  {v : Fin r → PairOrbit H // LinearIndependent (ZMod 2) (fun i => character H (v i))}

theorem frame_injective {r : ℕ} (v : Frame H r) : Function.Injective v.val := by
  intro i j hij
  apply v.property.injective
  change character H (v.val i) = character H (v.val j)
  rw [hij]

theorem frame_relabel_iff (e : X ≃ Y) {r : ℕ} (v : Fin r → PairOrbit H) :
    LinearIndependent (ZMod 2) (fun i => character H (v i)) ↔
      LinearIndependent (ZMod 2)
        (fun i => character (relabelSubgroup e H) (pairOrbitEquiv e H (v i))) := by
  let f := primeCharacterCongr 2 (relabelGroup H e)
  have h := f.toLinearMap.linearIndependent_iff_of_injOn
    (v := fun i => character (relabelSubgroup e H) (pairOrbitEquiv e H (v i)))
    f.injective.injOn
  simpa only [Function.comp_def, LinearEquiv.coe_coe, f, character_congr] using h

def frameEquiv (e : X ≃ Y) (r : ℕ) : Frame H r ≃ Frame (relabelSubgroup e H) r :=
  (Equiv.piCongrRight (fun _ : Fin r => pairOrbitEquiv e H)).subtypeEquiv
    (fun v => frame_relabel_iff H e v)

theorem frame_card_relabel (e : X ≃ Y) (r : ℕ) :
    Nat.card (Frame (relabelSubgroup e H) r) = Nat.card (Frame H r) :=
  (Nat.card_congr (frameEquiv H e r)).symm

section Assembly

variable {ι : Type*} [Fintype ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, Nonempty (Ω i)] {m : ι → ℕ}
    {U : ∀ i, Subgroup (Equiv.Perm (Ω i))}
    {P : Subgroup (Equiv.Perm (OrbitProfilePoints Ω m)) → Prop}

/-- In particular r=4 is the actual ordered-independent mark needed for
the E8 incidence. The original normalizer/occurrence weights are unchanged. -/
theorem ordered_frame_assembly (r : ℕ)
    (hfull : ∀ K, P K → OrbitProfileFull U 1 K)
    (hnatural : OrbitProfileFamilyNatural Ω m U P)
    (htrans : ∀ i (x y : Ω i), ∃ u : U i, (u : Equiv.Perm (Ω i)) x = y)
    (hsep : OrbitActionTypesSeparated Ω U) :
    Nat.card (Σ H : AssembledOrbitProfile P, Frame H.val r) =
      Nat.card (LabelledOrbitAtlas Ω m U) *
        Nat.card (Σ K : {K // P K}, Frame K.val r) :=
  assembledOrbitProfile_marked_card hfull hnatural htrans hsep (fun H => Frame H r)
    (fun e K => (frameEquiv K e r).symm)

end Assembly

end SymmetricSubgroupAsymptotics.PermutationPairOrbitCharacters
