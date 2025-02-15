import Taleve.Vector

namespace Taleve

inductive Piece where | I | O | T | S | Z | J | L
deriving DecidableEq, Fintype

inductive Cell where
| empty : Cell
| gray : Cell
| colored (p : Piece) : Cell
deriving DecidableEq, Fintype

namespace Cell

def isFull : Cell → Prop
| .empty => False
| .gray => True
| .colored _ => True

def isFull' : Cell → Bool
| .empty => false
| .gray => true
| .colored _ => true

instance (c : Cell) : Decidable c.isFull :=
  decidable_of_bool c.isFull' (by cases c <;> simp [isFull, isFull'])

end Cell

def Row (w : ℕ) := Vector Cell w

instance (w) : DecidableEq (Row w) := by
  unfold Row
  infer_instance

def Row.mk {w} (row : Vector Cell w) : Row w := row

def Board (w h : ℕ) := Vector (Row w) h

instance (w h) : DecidableEq (Board w h) := by
  unfold Board
  infer_instance

def Board.mk {w h} (board : Vector (Row w) h) : Board w h := board

end Taleve
