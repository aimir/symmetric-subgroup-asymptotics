import SymmetricSubgroupAsymptotics.BinaryCoinducedNormalizerPointCover
import SymmetricSubgroupAsymptotics.FiniteGroupCertificates

/-! Point-word certificates for a generated Sylow-three subgroup of any
rank. A small checked Cayley table certifies only the selected Sylow;
there is no subgroup or induced-submodule census. -/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.GeneratedSylowNormalizerPointCertificate

variable {G : Type} [Group G] [Finite G] {r n : ℕ}

abbrev generated (s : Fin r → G) : Subgroup G := Subgroup.closure (Set.range s)

def letter (s : Fin r → G) (g : G) : Fin r ⊕ Fin 2 → G
  | .inl j => s j
  | .inr j => if j = 0 then g else g⁻¹

def word (s : Fin r → G) (g : G) (w : List (Fin r ⊕ Fin 2)) : G :=
  (w.map (letter s g)).prod

theorem word_mem (s : Fin r → G) (g : G) (w : List (Fin r ⊕ Fin 2)) :
    word s g w ∈ (generated s ⊔ Subgroup.zpowers g : Subgroup G) := by
  have hs : generated s ≤ (generated s ⊔ Subgroup.zpowers g : Subgroup G) := le_sup_left
  have hg : Subgroup.zpowers g ≤ (generated s ⊔ Subgroup.zpowers g : Subgroup G) := le_sup_right
  apply Subgroup.list_prod_mem
  intro y hy
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
  rcases j with j | j
  · exact hs (Subgroup.subset_closure (Set.mem_range_self j))
  · change (if j = 0 then g else g⁻¹) ∈ _
    split
    · exact hg (Subgroup.mem_zpowers g)
    · exact hg ((Subgroup.zpowers g).inv_mem (Subgroup.mem_zpowers g))

theorem normalizes_of_generators (s : Fin r → G) (g : G)
    (hf : ∀ j, g * s j * g⁻¹ ∈ generated s)
    (hb : ∀ j, g⁻¹ * s j * g ∈ generated s) :
    g ∈ Subgroup.normalizer (generated s : Set G) := by
  have hforward : generated s ≤ (generated s).comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, rfl⟩
    exact hf j
  have hbackward : generated s ≤ (generated s).comap (MulAut.conj g⁻¹).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨j, rfl⟩
    change g⁻¹ * s j * (g⁻¹)⁻¹ ∈ generated s
    simpa only [inv_inv] using hb j
  change ∀ x : G, x ∈ generated s ↔ g * x * g⁻¹ ∈ generated s
  intro x
  constructor
  · exact fun hx => hforward hx
  · intro hx
    have h := hbackward hx
    change g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ ∈ generated s at h
    simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using h

local instance threePrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

structure Certificate (X : Type) [MulAction G X] (r n : ℕ) where
  generators : Fin r → G
  cayley : FiniteCayleyCertificate generators n
  rows_injective : Function.Injective cayley.elements
  group_factorization : n = 3 ^ (Nat.card G).factorization 3
  normalizer : G
  forward : ∀ j, normalizer * generators j * normalizer⁻¹ ∈ generated generators
  backward : ∀ j, normalizer⁻¹ * generators j * normalizer ∈ generated generators
  representative : X
  path : X → List (Fin r ⊕ Fin 2)
  covers : ∀ x : X, (∀ j, generators j • x = x) ∨
    word generators normalizer (path x) • representative = x

theorem Certificate.head_le_two
    {X L V : Type} [MulAction G X] [MulAction.IsPretransitive G X]
    [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (C : Certificate (G := G) X r n) (x : X)
    (f : MulAction.stabilizer G x →* L) (hf : Function.Surjective f)
    (rho : Representation (ZMod 2) L V) (hL : Nat.card L = 3 ∨ Nat.card L = 6)
    (hdim : Module.finrank (ZMod 2) V = 2) (hrho : Function.Injective rho)
    (B : Subrepresentation
      (Representation.coind (MulAction.stabilizer G x).subtype (rho.comp f))) :
    Module.finrank (ZMod 2)
      (B.toRepresentation.IntertwiningMap (Representation.trivial (ZMod 2) G (ZMod 2))) ≤ 2 := by
  let P : Sylow 3 G := Sylow.ofCard (generated C.generators)
    ((C.cayley.card_closure C.rows_injective).trans C.group_factorization)
  have hnormalizer : C.normalizer ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) :=
    normalizes_of_generators C.generators C.normalizer C.forward C.backward
  have hcover : ∀ z : X, z ∈ MulAction.fixedPoints P X ∨
      ∃ j : Fin 1, z ∈ MulAction.orbit
        ↥((P : Subgroup G) ⊔ Subgroup.zpowers C.normalizer)
        ((fun _ : Fin 1 => C.representative) j) := by
    intro z
    rcases C.covers z with hz | hz
    · left
      have hle : generated C.generators ≤ MulAction.stabilizer G z := by
        apply (Subgroup.closure_le _).mpr
        rintro a ⟨j, rfl⟩
        exact hz j
      intro p
      exact hle p.2
    · right
      let a : ↥((P : Subgroup G) ⊔ Subgroup.zpowers C.normalizer) :=
        ⟨word C.generators C.normalizer (C.path z), word_mem _ _ _⟩
      refine ⟨0, MulAction.mem_orbit_iff.mpr ⟨a, ?_⟩⟩
      change word C.generators C.normalizer (C.path z) • C.representative = z
      exact hz
  simpa only [Nat.mul_one] using
    BinaryCoinducedNormalizerPointCover.head_le_twice_cover_on_points x P C.normalizer
      hnormalizer (fun _ : Fin 1 => C.representative) hcover f hf rho hL hdim hrho B

end SymmetricSubgroupAsymptotics.GeneratedSylowNormalizerPointCertificate

end
