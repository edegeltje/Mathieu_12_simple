import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic


open ZMod
open GaloisField
open Module


@[ext]
structure F₄ where
  x0: ZMod 2
  x1: ZMod 2
namespace F4

section instances
instance : Zero F₄ := ⟨0,0⟩

instance : Add F₄ := ⟨fun a b ↦ ⟨a.x0 + b.x0,a.x1 + b.x1⟩⟩

instance : Neg F₄ := ⟨fun a ↦ a⟩ -- elements are mod 2, and -1=1, so it's id.

instance : One F₄ := ⟨1,1⟩

instance : Mul F₄ := ⟨fun a b ↦
  ⟨(a.x0 * b.x0) + (a.x0 + a.x1) * (b.x0 + b.x1),
  (a.x1 * b.x1) + (a.x0 + a.x1) * (b.x0 + b.x1)⟩
⟩
instance : Inv F₄ := ⟨fun a ↦ ⟨a.x1,a.x0⟩⟩


end instances

section definition_theorems

theorem elem_def (a : F₄) : ∃x y : ZMod 2, a = ⟨x, y⟩ := by
  use a.x0
  use a.x1

theorem zero_def : (0 : F₄) = ⟨0,0⟩ :=
  rfl

theorem add_def (a b :F₄) : a + b = ⟨a.x0 + b.x0, a.x1 + b.x1⟩ :=
  rfl

theorem neg_def (a:F₄) : -a = a := rfl

theorem one_def : (1 : F₄) = ⟨1,1⟩ := rfl

theorem mul_def (a b : F₄) : a * b = ⟨(a.x0 * b.x0) + (a.x0 + a.x1) * (b.x0 + b.x1),
  (a.x1 * b.x1) + (a.x0 + a.x1) * (b.x0 + b.x1)⟩ := rfl

-- theorem div_def (a b : F₄) : a / b = ⟨(a.x0 * b.x1) + (a.x0 + a.x1) * (b.x1 + b.x0),
--   (a.x1 * b.x0) + (a.x0 + a.x1) * (b.x1 + b.x0)⟩ := rfl

theorem inv_def (a : F₄) : a⁻¹ = ⟨a.x1,a.x0⟩ := rfl

end definition_theorems

def ω : F₄ := ⟨1,0⟩

instance: AddSemigroup F₄ where
  add_assoc := by
    intros
    repeat
      rw [add_def]
    group

instance : AddMonoid F₄ where
  zero_add := by
    intro
    rw [zero_def]
    rw [add_def]
    group
  add_zero := by
    intro
    rw [zero_def]
    rw [add_def]
    group

instance : AddCommMonoid F₄ where
  add_comm := by
    intro a b
    repeat
      rw [add_def]
    group

instance : NonUnitalNonAssocSemiring F₄ where
  left_distrib := by
    intro a b c
    repeat
      rw [mul_def]
    repeat
      rw [add_def]
    ring_nf
  right_distrib := by
    intro a b c
    repeat
      rw [mul_def]
    repeat
      rw [add_def]
    ring_nf
  zero_mul := by
    intro a
    rw [zero_def, mul_def]
    ring_nf
  mul_zero := by
    intro a
    rw [zero_def,mul_def]
    ring_nf

instance : NonUnitalSemiring F₄ where
  mul_assoc := by
    intro a b c
    repeat
      rw [mul_def]
    have h: (2:ZMod 2) = (4:ZMod 2)
    . apply refl
    ext
    . ring_nf
      rw [h]
    . ring_nf
      rw [h]

instance : Semiring F₄ where
  one_mul := by
    intro a
    rw [one_def,mul_def]
    ring_nf
    have h1 : (2:ZMod 2) = (0:ZMod 2)
    . apply refl
    have h2 : (3:ZMod 2) = (1:ZMod 2)
    . apply refl
    repeat
      rw [h1,h2]
    ring_nf
  mul_one := by
    intro a
    rw [one_def,mul_def]
    ring_nf
    have h1 : (2:ZMod 2) = (0:ZMod 2)
    . apply refl
    have h2 : (3:ZMod 2) = (1:ZMod 2)
    . apply refl
    rw [h1,h2]
    ring_nf

instance : Ring F₄ where
  sub := (.+.)
  sub_eq_add_neg := by
    intro a b
    rfl
  add_left_neg := by
    intro a
    rw [neg_def,add_def]
    group
    have h:(2:ZMod 2) = (0:ZMod 2)
    . apply rfl
    rw [h]
    rfl

instance : CommRing F₄ where
  mul_comm := by
    intro a b
    rw [mul_def,mul_def]
    ring_nf
instance : Field F₄ where
  div_eq_mul_inv := by
    intro a b
    rw [inv_def]
    rfl
  exists_pair_ne := by
    use 1
    use 0
    intro h
    rw [F₄.ext_iff 1 0] at h
    have h1eq0 := h.left
    rw [one_def,zero_def] at h1eq0
    simp at h1eq0
  mul_inv_cancel := by
    intro a
    intro anonzero
    rw [inv_def]
    rw [mul_def, one_def]
    rw [F₄.ext_iff]
    simp only
    obtain ⟨a₀,a₁⟩ := a
    ring_nf
    suffices hsemifinal : a₀ * a₁ * 3 + a₀ ^ 2 + a₁ ^ 2 = 1
    . apply And.intro hsemifinal hsemifinal
    match a₀ with
      | 1 => simp only [one_mul, one_pow, pow_card]
             ring_nf
             rfl
      | 0 => match a₁ with
               | 1 => ring_nf
               | 0 => contradiction
  inv_zero := by rfl

@[simp]
lemma omega_square_omega_inverse : ω ^ 2 = ω⁻¹ := by
  rfl
end F4
