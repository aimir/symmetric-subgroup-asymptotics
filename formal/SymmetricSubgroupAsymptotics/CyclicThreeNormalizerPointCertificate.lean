import SymmetricSubgroupAsymptotics.BinaryCoinducedNormalizerPointCover

/-! Small word certificates for a cyclic Sylow-three normalizer cover.
Only physical point words and three-element cyclic subgroup data are
retained. No subgroup registry or induced-submodule census is used. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CyclicThreeNormalizerPointCertificate

variable {G : Type} [Group G]

def letter (s g : G) (i : Fin 4) : G := ![s, s⁻¹, g, g⁻¹] i
def word (s g : G) (w : List (Fin 4)) : G := (w.map (letter s g)).prod

theorem word_mem (s g : G) (w : List (Fin 4)) :
    word s g w ∈ (Subgroup.zpowers s ⊔ Subgroup.zpowers g : Subgroup G) := by
  have hs : Subgroup.zpowers s ≤ (Subgroup.zpowers s ⊔ Subgroup.zpowers g : Subgroup G) := le_sup_left
  have hg : Subgroup.zpowers g ≤ (Subgroup.zpowers s ⊔ Subgroup.zpowers g : Subgroup G) := le_sup_right
  have hletter (i : Fin 4) : letter s g i ∈
      (Subgroup.zpowers s ⊔ Subgroup.zpowers g : Subgroup G) := by
    fin_cases i
    · exact hs (Subgroup.mem_zpowers s)
    · exact hs ((Subgroup.zpowers s).inv_mem (Subgroup.mem_zpowers s))
    · exact hg (Subgroup.mem_zpowers g)
    · exact hg ((Subgroup.zpowers g).inv_mem (Subgroup.mem_zpowers g))
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih => exact Subgroup.mul_mem _ (hletter i) ih

local instance threePrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

variable [Finite G]

def sylow (s : G) (hs : orderOf s = 3)
    (hfactor : (Nat.card G).factorization 3 = 1) : Sylow 3 G :=
  Sylow.ofCard (Subgroup.zpowers s) (by rw [Nat.card_zpowers, hs, hfactor, pow_one])

/-- The finite witness fields needed for one active combined point orbit. -/
structure Certificate (X : Type) [MulAction G X] where
  generator : G
  generator_order : orderOf generator = 3
  group_factorization : (Nat.card G).factorization 3 = 1
  normalizer : G
  normalizes : normalizer ∈ Subgroup.normalizer (Subgroup.zpowers generator : Set G)
  representative : X
  path : X → List (Fin 4)
  covers : ∀ x : X, generator • x = x ∨
    word generator normalizer (path x) • representative = x

/-- Every local epimorphism and faithful binary plane uses the same
retained point certificate, with its actual point stabilizer. -/
theorem Certificate.head_le_two
    {X L V : Type} [MulAction G X] [MulAction.IsPretransitive G X]
    [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (C : Certificate (G := G) X) (x : X)
    (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2 := by
  let P := sylow C.generator C.generator_order C.group_factorization
  have hcover : ∀ z : X, z ∈ MulAction.fixedPoints P X ∨
      ∃ j : Fin 1, z ∈ MulAction.orbit
        ↥((P : Subgroup G) ⊔ Subgroup.zpowers C.normalizer)
        ((fun _ : Fin 1 => C.representative) j) := by
    intro z
    rcases C.covers z with hz | hz
    · left
      have hle : Subgroup.zpowers C.generator ≤ MulAction.stabilizer G z :=
        Subgroup.zpowers_le.mpr hz
      intro p
      exact hle p.2
    · right
      let a : ↥((P : Subgroup G) ⊔ Subgroup.zpowers C.normalizer) :=
        ⟨word C.generator C.normalizer (C.path z), word_mem _ _ _⟩
      refine ⟨0, MulAction.mem_orbit_iff.mpr ⟨a, ?_⟩⟩
      change word C.generator C.normalizer (C.path z) • C.representative = z
      exact hz
  simpa only [Nat.mul_one] using
    BinaryCoinducedNormalizerPointCover.head_le_twice_cover_on_points x P C.normalizer
      C.normalizes (fun _ : Fin 1 => C.representative) hcover f hf rho hL hdim hrho B

end SymmetricSubgroupAsymptotics.CyclicThreeNormalizerPointCertificate

end
