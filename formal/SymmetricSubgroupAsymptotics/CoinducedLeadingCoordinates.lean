import SymmetricSubgroupAsymptotics.OrderedCosetTransversal
import SymmetricSubgroupAsymptotics.RepresentationLeadingAntichain
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual coinduced coordinates for the intrinsic-head antichain argument

Right-coset factorization, uniqueness, and triangular transport are explicit
hypotheses on the actual subgroup and representatives. Coinduced functions
retain their original `ρ(h)` twists. Coordinates are ordered first by coset
row, then by the original fibre basis; only equal fibre labels are compared.

No regular subgroup, splitting, p-group chain, or ambient-coinvariant
substitution is asserted. The final theorem applies to every actual
subrepresentation of this same coinduced representation.
-/

set_option autoImplicit false
noncomputable section

namespace SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates

open RepresentationLeadingAntichain

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {N d : ℕ}

/-- Coset-major, fibre-minor indexing of the full coordinate set. -/
def label (a : Fin N) (i : Fin d) : Fin (N*d) := finProdFinEquiv (a,i)

@[simp] theorem label_val (a : Fin N) (i : Fin d) :
    (label a i).val = i.val+d*a.val := rfl

theorem label_row_lt {a b : Fin N} (hab : a < b) (i j : Fin d) :
    label a i < label b j := by
  have hm : d*(a.val+1) ≤ d*b.val := Nat.mul_le_mul_left d
    (Nat.succ_le_of_lt hab)
  rw [Nat.mul_add, Nat.mul_one] at hm
  have hi := i.isLt
  change i.val+d*a.val < j.val+d*b.val
  omega

theorem label_fibre_lt (a : Fin N) {i j : Fin d} (hij : i < j) :
    label a i < label a j := Nat.add_lt_add_right hij _

theorem label_lt_cases {a b : Fin N} {i j : Fin d}
    (h : label a i < label b j) : a < b ∨ a = b ∧ i < j := by
  rcases lt_trichotomy a b with hab | hab | hba
  · exact Or.inl hab
  · subst b
    exact Or.inr ⟨rfl, (Nat.add_lt_add_iff_right).mp h⟩
  · exact False.elim ((not_lt_of_ge (label_row_lt hba j i).le) h)

/-- Original fibre coefficients evaluated at the actual representatives. -/
def coordinates (H : Subgroup G) (ρ : Representation k H V) (T : Fin N → G)
    (basis : Module.Basis (Fin d) k V) :
    Representation.coindV H.subtype ρ →ₗ[k] (Fin (N*d) → k) where
  toFun f a := basis.equivFun (f.1 (T (finProdFinEquiv.symm a).1))
    (finProdFinEquiv.symm a).2
  map_add' f f' := by
    funext a
    exact congrFun (basis.equivFun.map_add _ _) _
  map_smul' r f := by
    funext a
    exact congrFun (basis.equivFun.map_smul r _) _

@[simp] theorem coordinates_label (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (f : Representation.coindV H.subtype ρ) (a : Fin N) (i : Fin d) :
    coordinates H ρ T basis f (label a i) = basis.equivFun (f.1 (T a)) i := by
  change basis.equivFun
    (f.1 (T (finProdFinEquiv.symm (finProdFinEquiv (a,i))).1))
      (finProdFinEquiv.symm (finProdFinEquiv (a,i))).2 = _
  rw [Equiv.symm_apply_apply]

/-- All fibre twists in the original coinduced function relation remain. -/
theorem fibre_twist (H : Subgroup G) (ρ : Representation k H V)
    (f : Representation.coindV H.subtype ρ) (h : H) (x : G) :
    f.1 ((h:G)*x) = ρ h (f.1 x) := f.2 h x

theorem coordinates_injective (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin N, x=h*T a) :
    Function.Injective (coordinates H ρ T basis) := by
  intro f f' heq
  have hrow : ∀ a : Fin N, f.1 (T a)=f'.1 (T a) := by
    intro a
    apply basis.equivFun.injective
    funext i
    simpa only [coordinates_label] using congrFun heq (label a i)
  apply Subtype.ext
  funext x
  obtain ⟨h, hh, a, rfl⟩ := hfactor x
  change f.1 (H.subtype ⟨h,hh⟩*T a)=f'.1 (H.subtype ⟨h,hh⟩*T a)
  rw [f.2 ⟨h,hh⟩ (T a), f'.2 ⟨h,hh⟩ (T a), hrow]

/-- The actual right translation carrying the old b-row to the c-row. -/
def raisingElement (T : Fin N → G) (b c : Fin N) : G := ((T b)⁻¹*T c)⁻¹

theorem target_row (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (b c : Fin N) (f : Representation.coindV H.subtype ρ) :
    ((Representation.coind H.subtype ρ) (raisingElement T b c) f).1 (T c)=f.1 (T b) := by
  change f.1 (T c*raisingElement T b c)=f.1 (T b)
  exact congrArg f.1 (by dsimp [raisingElement]; group)

/-- Triangularity and uniqueness force a later target row to come from a
later source row. The intervening original H-factor is kept explicitly. -/
theorem source_row_gt (H : Subgroup G) (T : Fin N → G)
    (comparable : Fin N → Fin N → Prop)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htriangular : CosetTriangular H T (· < ·) comparable)
    {b c r a : Fin N} (hbc : comparable b c) (hcr : c<r)
    (h : G) (hh : h∈H) (heq : T r*raisingElement T b c=h*T a) : b<a := by
  by_contra hba
  rcases lt_or_eq_of_le (le_of_not_gt hba) with hab | hab
  · obtain ⟨h', hh', e, hec, he⟩ := htriangular a b c hab hbc
    have hr : T r=(h*h')*T e := by
      calc
        T r = (T r*raisingElement T b c)*(raisingElement T b c)⁻¹ := by group
        _ = (h*T a)*(raisingElement T b c)⁻¹ := by rw [heq]
        _ = h*(T a*(T b)⁻¹*T c) := by dsimp [raisingElement]; group
        _ = (h*h')*T e := by rw [he, mul_assoc]
    have hmem : T r*(T e)⁻¹∈H := by
      rw [hr]
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using H.mul_mem hh hh'
    have hre := hunique r e hmem
    have hrc : r<c := by simpa only [hre] using hec
    exact (not_lt_of_ge hrc.le) hcr
  · subst a
    have hr : T r=h*T c := by
      calc
        T r = (T r*raisingElement T b c)*(raisingElement T b c)⁻¹ := by group
        _ = (h*T b)*(raisingElement T b c)⁻¹ := by rw [heq]
        _ = h*T c := by dsimp [raisingElement]; group
    have hmem : T r*(T c)⁻¹∈H := by
      rw [hr]
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
    exact (ne_of_gt hcr) (hunique r c hmem)

theorem row_zero_of_leading (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    {f : Representation.coindV H.subtype ρ} {b a : Fin N} {i : Fin d}
    (hleading : HasLeading (coordinates H ρ T basis) f (label b i)) (hba : b<a) :
    f.1 (T a)=0 := by
  apply basis.equivFun.injective
  funext j
  simpa only [coordinates_label, map_zero, Pi.zero_apply] using
    hleading.2 (label a j) (label_row_lt hba i j)

theorem later_target_row_zero (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin N, x=h*T a)
    (comparable : Fin N → Fin N → Prop)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htriangular : CosetTriangular H T (· < ·) comparable)
    {f : Representation.coindV H.subtype ρ} {b c r : Fin N} {i : Fin d}
    (hleading : HasLeading (coordinates H ρ T basis) f (label b i))
    (hbc : comparable b c) (hcr : c<r) :
    ((Representation.coind H.subtype ρ) (raisingElement T b c) f).1 (T r)=0 := by
  obtain ⟨h, hh, a, heq⟩ := hfactor (T r*raisingElement T b c)
  have hba := source_row_gt H T comparable hunique htriangular hbc hcr h hh heq
  change f.1 (T r*raisingElement T b c)=0
  rw [heq]
  change f.1 (H.subtype ⟨h,hh⟩*T a)=0
  rw [f.2 ⟨h,hh⟩ (T a), row_zero_of_leading H ρ T basis hleading hba, map_zero]

/-- Actual raising preserves the leading fibre coefficient unchanged;
lower rows may carry arbitrary original fibre twists. -/
theorem raises_leading (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin N, x=h*T a)
    (comparable : Fin N → Fin N → Prop)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htriangular : CosetTriangular H T (· < ·) comparable)
    {f : Representation.coindV H.subtype ρ} {b c : Fin N} {i : Fin d}
    (hleading : HasLeading (coordinates H ρ T basis) f (label b i))
    (hbc : comparable b c) :
    HasLeading (coordinates H ρ T basis)
      ((Representation.coind H.subtype ρ) (raisingElement T b c) f) (label c i) := by
  constructor
  · simpa only [coordinates_label, target_row] using hleading.1
  · intro x hx
    obtain ⟨⟨a,j⟩, rfl⟩ := finProdFinEquiv.surjective x
    change coordinates H ρ T basis
      ((Representation.coind H.subtype ρ) (raisingElement T b c) f) (label a j)=0
    rcases label_lt_cases hx with hca | ⟨hca, hij⟩
    · rw [coordinates_label,
        later_target_row_zero H ρ T basis hfactor comparable hunique htriangular hleading hbc hca,
        map_zero, Pi.zero_apply]
    · subst a
      simpa only [coordinates_label, target_row] using
        hleading.2 (label b j) (label_fibre_lt b hij)

/-- Comparability includes the same original fibre-basis coordinate. -/
def fullComparable (comparable : Fin N → Fin N → Prop)
    (a b : Fin (N*d)) : Prop :=
  (finProdFinEquiv.symm a).2=(finProdFinEquiv.symm b).2 ∧
    comparable (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm b).1

def subrepresentationCoordinates (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (M : Subrepresentation (Representation.coind H.subtype ρ)) :
    M.toSubmodule →ₗ[k] (Fin (N*d) → k) :=
  (coordinates H ρ T basis).comp M.toSubmodule.subtype

theorem subrepresentationCoordinates_injective
    (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin N, x=h*T a)
    (M : Subrepresentation (Representation.coind H.subtype ρ)) :
    Function.Injective (subrepresentationCoordinates H ρ T basis M) :=
  (coordinates_injective H ρ T basis hfactor).comp Subtype.val_injective

/-- Raising is restricted to the actual subrepresentation, whose stability
under the selected actual group element supplies the new lift. -/
theorem subrepresentation_raising
    (H : Subgroup G) (ρ : Representation k H V)
    (T : Fin N → G) (basis : Module.Basis (Fin d) k V)
    (hfactor : ∀ x : G, ∃ h : G, h∈H ∧ ∃ a : Fin N, x=h*T a)
    (comparable : Fin N → Fin N → Prop)
    (hunique : ∀ a b, T a*(T b)⁻¹∈H → a=b)
    (htriangular : CosetTriangular H T (· < ·) comparable)
    (M : Subrepresentation (Representation.coind H.subtype ρ))
    (v : M.toSubmodule) (a b : Fin (N*d))
    (hleading : HasLeading (subrepresentationCoordinates H ρ T basis M) v a)
    (hrelated : fullComparable comparable a b) :
    ∃ g : G, HasLeading (subrepresentationCoordinates H ρ T basis M)
      (M.toRepresentation g v) b := by
  obtain ⟨⟨a,i⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b,j⟩, rfl⟩ := finProdFinEquiv.surjective b
  simp only [fullComparable, Equiv.symm_apply_apply] at hrelated
  obtain ⟨hij, hab⟩ := hrelated
  subst j
  refine ⟨raisingElement T a b, ?_⟩
  change HasLeading (coordinates H ρ T basis)
    ((Representation.coind H.subtype ρ) (raisingElement T a b) v.1) (label b i)
  exact raises_leading H ρ T basis hfactor comparable hunique htriangular hleading hab

/-- Forget the witness vectors only after obtaining the intrinsic quotient
basis by the minimal-leading argument. Keeping this helper abstract avoids
elaborating a quotient-basis coercion on the nested coinduced subtype. -/
theorem coinvariant_labels_of_raising
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    {n : ℕ} (τ : Representation k G W) (C : W →ₗ[k] (Fin n → k))
    (hinjective : Function.Injective C) (R : Fin n → Fin n → Prop)
    (hraising : ∀ (v : W) (a b : Fin n), HasLeading C v a → R a b →
      ∃ g : G, HasLeading C (τ g v) b) :
    ∃ leading : Fin (Module.finrank k τ.Coinvariants) → Fin n,
      Pairwise (fun i j => ¬ R (leading i) (leading j)) := by
  obtain ⟨basis, v, leading, hquotient, hleading, hseparated⟩ :=
    exists_coinvariant_basis_lifts τ C hinjective R hraising
  exact ⟨leading, hseparated⟩

end SymmetricSubgroupAsymptotics.CoinducedLeadingCoordinates
