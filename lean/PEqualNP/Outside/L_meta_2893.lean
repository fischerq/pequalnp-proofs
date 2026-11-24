import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2893_aux

def sig : Fin 8 → Fin 8 → Fin 8 := ![![1, 0, 4, 7, 5, 2, 6, 3], ![1, 0, 4, 7, 5, 2, 6, 3], ![4, 0, 1, 2, 6, 7, 5, 3], ![4, 6, 2, 1, 0, 7, 3, 5], ![1, 5, 7, 4, 0, 2, 3, 6], ![2, 3, 7, 4, 6, 1, 5, 0], ![2, 6, 4, 7, 3, 1, 0, 5], ![2, 3, 7, 4, 6, 1, 5, 0]]

theorem sigZeroOne : ∀ x1 : Fin 8, sig x1 x1 = 0 ∨ sig x1 x1 = 1 := by decide

set_option maxRecDepth 100000 in
theorem key : ∀ (x1 : Fin 8) (b0 b1 b2 b3 b4 b5 b6 b7 : Bool),         (have x4 : Fin (9 : ℕ) → Bool := Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (![b0, b1, b2, b3, b4, b5, b6, b7] ∘ sig x1);           x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) =           have x4 : Fin (8 : ℕ) → Bool := ![b0, b1, b2, b3, b4, b5, b6, b7];           x4 (0 : Fin (8 : ℕ)) && x4 (1 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (2 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (3 : Fin (8 : ℕ)) || x4 (0 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (5 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (3 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (4 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (5 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (7 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) := by
  decide +kernel

theorem vec (x3 : Fin 8 → Bool) : x3 = ![x3 0, x3 1, x3 2, x3 3, x3 4, x3 5, x3 6, x3 7] := by
  funext i
  fin_cases i <;> rfl

theorem keyFn (x1 : Fin 8) (x3 : Fin 8 → Bool) :         (have x4 : Fin (9 : ℕ) → Bool := Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (x3 ∘ sig x1);           x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) =           have x4 : Fin (8 : ℕ) → Bool := x3;           x4 (0 : Fin (8 : ℕ)) && x4 (1 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (2 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (3 : Fin (8 : ℕ)) || x4 (0 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (5 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (3 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (4 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (5 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (7 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) := by
  rw [vec x3]
  exact key x1 (x3 0) (x3 1) (x3 2) (x3 3) (x3 4) (x3 5) (x3 6) (x3 7)

end PEqualNP.Outside.L_meta_2893_aux

open PEqualNP.Outside.L_meta_2893_aux

theorem PEqualNP.Outside.L_meta_2893 : ∀ (x1 : Fin (8 : ℕ)),   ∃ (x2 : Fin (8 : ℕ) → Fin (8 : ℕ)),     (x2 x1 = (0 : Fin (8 : ℕ)) ∨ x2 x1 = (1 : Fin (8 : ℕ))) ∧       ∀ (x3 : Fin (8 : ℕ) → Bool),         (have x4 : Fin (9 : ℕ) → Bool := Fin.insertNth (6 : Fin (9 : ℕ)) Bool.false (x3 ∘ x2);           x4 (0 : Fin (9 : ℕ)) && x4 (1 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (2 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (3 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (4 : Fin (9 : ℕ)) || x4 (4 : Fin (9 : ℕ)) && x4 (0 : Fin (9 : ℕ)) || x4 (0 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ)) || x4 (1 : Fin (9 : ℕ)) && x4 (6 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (3 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (5 : Fin (9 : ℕ)) && x4 (7 : Fin (9 : ℕ)) || x4 (6 : Fin (9 : ℕ)) && x4 (8 : Fin (9 : ℕ)) || x4 (8 : Fin (9 : ℕ)) && x4 (5 : Fin (9 : ℕ))) =           have x4 : Fin (8 : ℕ) → Bool := x3;           x4 (0 : Fin (8 : ℕ)) && x4 (1 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (2 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (3 : Fin (8 : ℕ)) || x4 (0 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) || x4 (1 : Fin (8 : ℕ)) && x4 (5 : Fin (8 : ℕ)) || x4 (2 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (3 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (4 : Fin (8 : ℕ)) && x4 (6 : Fin (8 : ℕ)) || x4 (5 : Fin (8 : ℕ)) && x4 (7 : Fin (8 : ℕ)) || x4 (7 : Fin (8 : ℕ)) && x4 (4 : Fin (8 : ℕ)) := by
  intro x1
  exact ⟨sig x1, sigZeroOne x1, fun x3 => keyFn x1 x3⟩
