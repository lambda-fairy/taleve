import Taleve.Syntax

namespace Taleve

def pieces : Piece → Fin 4 → Board 4 4
| .I => fun
  | 0 => board
    - - - -
    I I I I
    - - - -
    - - - -
  | 1 => board
    - - I -
    - - I -
    - - I -
    - - I -
  | 2 => board
    - - - -
    - - - -
    I I I I
    - - - -
  | 3 => board
    - I - -
    - I - -
    - I - -
    - I - -
| .J => fun
  | 0 => board
    J - - -
    J J J -
    - - - -
    - - - -
  | 1 => board
    - J J -
    - J - -
    - J - -
    - - - -
  | 2 => board
    - - - -
    J J J -
    - - J -
    - - - -
  | 3 => board
    - J - -
    - J - -
    J J - -
    - - - -
| .L => fun
  | 0 => board
    - - L -
    L L L -
    - - - -
    - - - -
  | 1 => board
    - L - -
    - L - -
    - L L -
    - - - -
  | 2 => board
    - - - -
    L L L -
    L - - -
    - - - -
  | 3 => board
    L L - -
    - L - -
    - L - -
    - - - -
| .O => fun
  | _ => board
    - O O -
    - O O -
    - - - -
    - - - -
| .S => fun
  | 0 => board
    - S S -
    S S - -
    - - - -
    - - - -
  | 1 => board
    - S - -
    - S S -
    - - S -
    - - - -
  | 2 => board
    - - - -
    - S S -
    S S - -
    - - - -
  | 3 => board
    S - - -
    S S - -
    - S - -
    - - - -
| .T => fun
  | 0 => board
    - T - -
    T T T -
    - - - -
    - - - -
  | 1 => board
    - T - -
    - T T -
    - T - -
    - - - -
  | 2 => board
    - - - -
    T T T -
    - T - -
    - - - -
  | 3 => board
    - T - -
    T T - -
    - T - -
    - - - -
| .Z => fun
  | 0 => board
    Z Z - -
    - Z Z -
    - - - -
    - - - -
  | 1 => board
    - - Z -
    - Z Z -
    - Z - -
    - - - -
  | 2 => board
    - - - -
    Z Z - -
    - Z Z -
    - - - -
  | 3 => board
    - Z - -
    Z Z - -
    Z - - -
    - - - -

theorem pieces.valid₁ :
    ∀ p r x y, (pieces p r).get x y = none ∨ (pieces p r).get x y = some (.colored p) := by
  decide

theorem pieces.valid₂ :
    ∀ p r, (∑ (x) (y), if (pieces p r).get x y ≠ none then 1 else 0) = 4 := by
  decide

theorem pieces_injective_of_ne_O {p : Piece} (hp : p ≠ .O) : Function.Injective (pieces p) := by
  cases p
  case «O» => contradiction
  all_goals decide

end Taleve
