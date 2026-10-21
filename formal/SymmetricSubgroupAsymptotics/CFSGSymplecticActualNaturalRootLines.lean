import SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionLines

/-! Natural root lines as actual subgroups of the original elementary
C group. Chosen witnesses are unique by their faithful original matrix
action; all group laws and labels are proved from that action. -/
set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
open CFSGSymplecticSerreMatrices
variable {K : Type} [Field K]

theorem elementary_eq_of_mulVec_eq (r : ℕ) (g h : elementaryRootGroup K r)
    (he : ∀ x : Index r → K, (g.val : Mat K r) *ᵥ x = (h.val : Mat K r) *ᵥ x) : g = h := by
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext_of_mulVec_single
  intro i
  exact he (Pi.single i 1)

theorem exists_elementary_natural_transvection_any (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (a : K) :
    ∃ u : elementaryRootGroup K (r + 1), ∀ x : Index (r + 1) → K,
      (u.val : Mat K (r + 1)) *ᵥ x = transvection (r + 1) v a x := by
  by_cases hv : v = 0
  · subst v
    refine ⟨1, ?_⟩
    intro x
    change (1 : Mat K (r + 1)) *ᵥ x = _
    simp only [Matrix.one_mulVec, transvection_apply, pairing_zero_left,
      mul_zero, zero_smul, add_zero]
  · exact exists_elementary_natural_transvection r hr v hv a

def actualNaturalRootElement (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) (a : K) :
    elementaryRootGroup K (r + 1) :=
  Classical.choose (exists_elementary_natural_transvection_any r hr v a)

theorem actualNaturalRootElement_apply (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (a : K) (x : Index (r + 1) → K) :
    ((actualNaturalRootElement r hr v a).val : Mat K (r + 1)) *ᵥ x =
      transvection (r + 1) v a x :=
  Classical.choose_spec (exists_elementary_natural_transvection_any r hr v a) x

def actualNaturalRootHom (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) :
    Multiplicative K →* elementaryRootGroup K (r + 1) where
  toFun a := actualNaturalRootElement r hr v a.toAdd
  map_one' := by
    apply elementary_eq_of_mulVec_eq
    intro x
    change ((actualNaturalRootElement r hr v 0).val : Mat K (r + 1)) *ᵥ x =
      (1 : Mat K (r + 1)) *ᵥ x
    rw [actualNaturalRootElement_apply, transvection_zero]
    change x = (1 : Mat K (r + 1)) *ᵥ x
    exact (Matrix.one_mulVec x).symm
  map_mul' a b := by
    apply elementary_eq_of_mulVec_eq
    intro x
    change ((actualNaturalRootElement r hr v (a.toAdd + b.toAdd)).val : Mat K (r + 1)) *ᵥ x =
      (((actualNaturalRootElement r hr v a.toAdd).val : Mat K (r + 1)) *
        ((actualNaturalRootElement r hr v b.toAdd).val : Mat K (r + 1))) *ᵥ x
    rw [actualNaturalRootElement_apply, ← Matrix.mulVec_mulVec,
      actualNaturalRootElement_apply, actualNaturalRootElement_apply]
    exact congrArg (fun T : (Index (r + 1) → K) ≃ₗ[K] (Index (r + 1) → K) => T x)
      (transvection_add (r + 1) v a.toAdd b.toAdd)

def actualNaturalRootLine (r : ℕ) (hr : 0 < r) (v : Index (r + 1) → K) :
    Subgroup (elementaryRootGroup K (r + 1)) := (actualNaturalRootHom r hr v).range

theorem actualNaturalRootHom_injective (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    Function.Injective (actualNaturalRootHom r hr v) := by
  intro a b he
  have hT : transvection (r + 1) v a.toAdd = transvection (r + 1) v b.toAdd := by
    apply LinearEquiv.ext
    intro x
    have hx := congrArg (fun g : elementaryRootGroup K (r + 1) => (g.val : Mat K (r + 1)) *ᵥ x) he
    change ((actualNaturalRootElement r hr v a.toAdd).val : Mat K (r + 1)) *ᵥ x =
      ((actualNaturalRootElement r hr v b.toAdd).val : Mat K (r + 1)) *ᵥ x at hx
    rw [actualNaturalRootElement_apply, actualNaturalRootElement_apply] at hx
    exact hx
  exact Multiplicative.toAdd.injective ((transvection_parameter_injective (r + 1) v hv) hT)

def actualNaturalRootLineEquiv (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    Multiplicative K ≃* actualNaturalRootLine r hr v :=
  MonoidHom.ofInjective (actualNaturalRootHom_injective r hr v hv)

theorem actualNaturalRootLine_card (r : ℕ) (hr : 0 < r)
    (v : Index (r + 1) → K) (hv : v ≠ 0) :
    Nat.card (actualNaturalRootLine r hr v) = Nat.card K := by
  calc
    Nat.card (actualNaturalRootLine r hr v) = Nat.card (Multiplicative K) :=
      Nat.card_congr (actualNaturalRootLineEquiv r hr v hv).symm.toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

end SymmetricSubgroupAsymptotics.CFSGSymplecticTransvectionGeometry
