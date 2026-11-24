module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Rat.Floor

/-!
# Supporting lines on a path of Newton slopes

The first theorem compares adjacent supporting lines and their extreme contacts.
The second proves the cyclic-coordinate lattice inclusion corresponding to
Lau–Nicole–Vasiu, Proposition 5.12, with Lemma 5.16 supplied by the coordinate data.
The third combines it with the slope-block estimate at the explicit exponent
`floor (2*c*d/(c+d))`. These statements concern rational valuation models.
-/

@[expose] public section

open scoped BigOperators

namespace TraversoSlopeGraph

/-- The reference affine lines and the abscissas of their Newton polygon. -/
structure NewtonPath (r h : ℕ) where
  slope : ℕ → ℚ
  intercept : ℕ → ℚ
  cut : ℕ → ℚ
  first_cut : cut 0 = 0
  last_cut : cut r = h
  slope_lt : ∀ j, j + 1 < r → slope j < slope (j + 1)
  meet : ∀ j, j + 1 < r →
    intercept j + slope j * cut (j + 1) = intercept (j + 1) + slope (j + 1) * cut (j + 1)

def NewtonPath.line {r h : ℕ} (P : NewtonPath r h) (j : ℕ) (t : ℚ) : ℚ :=
  P.intercept j + P.slope j * t

/-- The supporting line of the coefficient cloud and its extreme contacts. -/
structure Contacts {h : ℕ} (slope : ℚ) (v : Fin h → WithTop ℚ) where
  offset : ℚ
  left : Fin h
  right : Fin h
  below : ∀ i, ((offset + slope * (i.val : ℚ) : ℚ) : WithTop ℚ) ≤ v i
  hits_left : ((offset + slope * (left.val : ℚ) : ℚ) : WithTop ℚ) = v left
  hits_right : ((offset + slope * (right.val : ℚ) : ℚ) : WithTop ℚ) = v right
  extremes : ∀ i, ((offset + slope * (i.val : ℚ) : ℚ) : WithTop ℚ) = v i →
    left ≤ i ∧ i ≤ right

/-- The algebraic inputs of the cyclic presentation, including the local
no-cancellation criterion of Lemma 5.16. The integer `threshold` is the
valuation of the change of basis from Laurent powers to the integral basis. -/
structure CyclicCoordinates {r h : ℕ} (P : NewtonPath r h) (c : ℕ)
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    (L : AddSubgroup (∀ i, X i)) (w : ∀ i, X i → WithTop ℚ) where
  coeff : (∀ i, X i) → Fin h → WithTop ℚ
  discrete : ∀ x i, coeff x i = ⊤ ∨ ∃ n : ℤ, coeff x i = ((n : ℚ) : WithTop ℚ)
  threshold : Fin h → ℤ
  integral : ∀ x, x ∈ L ↔ ∀ i, ((threshold i : ℚ) : WithTop ℚ) ≤ coeff x i
  covered : ∀ i, ∃ j : Fin r, (threshold i : ℚ) ≤ P.line j i.val
  nonzero_coeff : ∀ x, x ≠ 0 → ∃ i, coeff x i ≠ ⊤
  short_exact : ∀ x (j : Fin r) (contact : Contacts (P.slope j) (coeff x)),
    ((contact.right.val : ℚ) - contact.left.val <
      P.cut (j.val + 1) - P.cut j) →
    w j (x j) = ((contact.offset + P.slope j * (c : ℚ) : ℚ) : WithTop ℚ)

theorem contacts_above_reference {r h : ℕ} (P : NewtonPath r h)
    (v : Fin h → WithTop ℚ) (C : ∀ j : Fin r, Contacts (P.slope j) v) (shift : ℚ)
    (width : ∀ j : Fin r, (C j).offset ≤ P.intercept j - shift →
      P.cut (j.val + 1) - P.cut j ≤ ((C j).right.val : ℚ) - (C j).left.val) :
    ∀ j : Fin r, P.intercept j - shift < (C j).offset := by
  sorry

theorem proposition_5_12_cyclic {r h c : ℕ} {P : NewtonPath r h}
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    {L : AddSubgroup (∀ i, X i)} {w : ∀ i, X i → WithTop ℚ}
    (D : CyclicCoordinates P c L w) (scale : ∀ i, ℤ → X i → X i)
    (hs : ∀ i t x, w i (scale i t x) = w i x + ((t : ℚ) : WithTop ℚ))
    (hinv : ∀ i x, scale i 1 (scale i (-1) x) = x)
    (x : ∀ i, X i) (hx : ∀ j : Fin r, (P.line j c : WithTop ℚ) < w j (x j)) :
    ∃ y ∈ L, (fun j => scale j 1 (y j)) = x := by
  sorry

theorem cyclic_slope_graph_dimension_bound {r c d : ℕ} {P : NewtonPath r (c + d)}
    {X : Fin r → Type*} [∀ i, AddCommGroup (X i)]
    {L : AddSubgroup (∀ i, X i)} {w : ∀ i, X i → WithTop ℚ}
    (D : CyclicCoordinates P c L w)
    (scale frob : ∀ i, ℤ → X i → X i)
    (hs : ∀ i t x, w i (scale i t x) = w i x + ((t : ℚ) : WithTop ℚ))
    (hf : ∀ i t x, w i (frob i t x) = w i x + ((t : ℚ) * P.slope i : ℚ))
    (hzero : ∀ i, w i 0 = ⊤)
    (hout : ∀ x ∈ L, ∀ i, 0 ≤ w i (x i))
    (hpos : 0 < c + d) (hleft : ∀ i : Fin r, P.line i 0 ≤ 0)
    (hright : ∀ i : Fin r, P.line i ((c : ℚ) + d) ≤ d)
    (u : (∀ i, X i) → (∀ i, X i)) (huL : ∀ x ∈ L, u x ∈ L)
    (hus : ∀ i j t x, u (Pi.single j (scale j t x)) i = scale i t (u (Pi.single j x) i))
    (edges : Finset (Fin r × Fin r)) (n : Fin r → Fin r → ℤ)
    (hdir : ∀ i j, (i, j) ∈ edges → 0 ≤ (n i j : ℚ) * (P.slope i - P.slope j))
    (x : ∀ i, X i) (hx : x ∈ L) :
    (∑ e ∈ edges, Pi.single e.1 (scale e.1 ⌊2 * ((c : ℚ) * d / ((c : ℚ) + d))⌋
      (frob e.1 (n e.1 e.2) (u (Pi.single e.2 (frob e.2 (-(n e.1 e.2)) (x e.2))) e.1))))
      ∈ L := by
  sorry

end TraversoSlopeGraph
