import SymmetricSubgroupAsymptotics.CFSGSymplecticPolarEquivalence
import SymmetricSubgroupAsymptotics.LinearNonzeroConjugacyCover

/-! The actual elementary symplectic group charges all non-fixed-free
classes to its SAME literal first-vector stabilizer. A genuine finite
code separating fixed-free general-linear conjugacy pays the other
classes. The remaining polynomial multiplicity code is explicit, not
silently treated as a proved numerical bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open scoped Matrix

namespace SymmetricSubgroupAsymptotics.CFSGSymplecticFixedFreeClassCodes
open CFSGSymplecticSerreMatrices CFSGSymplecticPointAffineHom
open CFSGSymplecticNaturalBilinearClassGeometry LinearNonzeroConjugacyCover
open FixedFreeConjugacyClassCover
variable (K : Type) [Field K]

local instance finiteElementary [Finite K] (r : ℕ) : Finite (elementaryRootGroup K r) :=
  Finite.of_injective (fun g : elementaryRootGroup K r => (g.val : Mat K r))
    (by intro g h he; exact Subtype.ext (Units.ext he))

abbrev FixedFreeElement (r : ℕ) :=
  {g : elementaryRootGroup K r //
    ∀ v : Index r → K, naturalLinearHom K r g v = v → v = 0}

def freeRepresentative (r : ℕ) :
    letI := nonzeroAction (naturalLinearHom K r)
    FreeClasses (G := elementaryRootGroup K r) (X := {v : Index r → K // v ≠ 0}) →
      FixedFreeElement K r :=
  fun c => ⟨c.2.choose,
    (fixedFree_iff (naturalLinearHom K r) c.2.choose).mp c.2.choose_spec.2⟩

def freeCode (r : ℕ) {C : Type*} (code : FixedFreeElement K r → C) :
    letI := nonzeroAction (naturalLinearHom K r)
    FreeClasses (G := elementaryRootGroup K r) (X := {v : Index r → K // v ≠ 0}) → C :=
  fun c => code (freeRepresentative K r c)

theorem freeCode_injective [Finite K] [CharP K 2] (r : ℕ) (hr : 0 < r)
    {C : Type*} (code : FixedFreeElement K r → C)
    (hcode : ∀ g h : FixedFreeElement K r, code g = code h →
      IsConj (naturalLinearHom K r g.val) (naturalLinearHom K r h.val)) :
    letI := nonzeroAction (naturalLinearHom K r)
    Function.Injective (freeCode K r code) := by
  letI := nonzeroAction (naturalLinearHom K r)
  intro c d he
  let g := freeRepresentative K r c
  let h := freeRepresentative K r d
  have hg : ConjClasses.mk g.val = c.1 := c.2.choose_spec.1
  have hh : ConjClasses.mk h.val = d.1 := d.2.choose_spec.1
  have hc : IsConj g.val h.val := CFSGSymplecticPolarEquivalence.isConj_of_fixedFree
    K r hr g.val h.val g.property (hcode g h he)
  apply Subtype.ext
  exact hg.symm.trans ((ConjClasses.mk_eq_mk_iff_isConj.mpr hc).trans hh)

theorem class_card_le_point_add_code [Finite K] [CharP K 2] (r : ℕ)
    {C : Type*} [Finite C] (code : FixedFreeElement K (r+1) → C)
    (hcode : ∀ g h : FixedFreeElement K (r+1), code g = code h →
      IsConj (naturalLinearHom K (r+1) g.val) (naturalLinearHom K (r+1) h.val)) :
    Nat.card (ConjClasses (elementaryRootGroup K (r+1))) ≤
      Nat.card (ConjClasses (pointStabilizer K r)) + Nat.card C := by
  let ρ := naturalLinearHom K (r+1)
  letI := BilinearContragredientDuality.naturalAction ρ
  letI := nonzeroAction ρ
  let e : Index (r+1) → K := Pi.single (Sum.inl 0) 1
  have he : e ≠ 0 := by
    intro hz
    have hh := congrFun hz (Sum.inl 0)
    change (1 : K) = 0 at hh
    exact one_ne_zero hh
  have ht (v : Index (r+1) → K) (hv : v ≠ 0) :
      ∃ g : elementaryRootGroup K (r+1), ρ g e = v :=
    exists_map_nonzero K (r+1) (Nat.succ_pos r) e v he hv
  have hcover := LinearNonzeroConjugacyCover.class_card_le ρ e he ht
  have hs : MulAction.stabilizer (elementaryRootGroup K (r+1)) e =
      pointStabilizer K r := rfl
  rw [hs] at hcover
  exact hcover.trans (Nat.add_le_add_left
    (Nat.card_le_card_of_injective (freeCode K (r+1) code)
      (freeCode_injective K (r+1) (Nat.succ_pos r) code hcode)) _)

end SymmetricSubgroupAsymptotics.CFSGSymplecticFixedFreeClassCodes
