import Taleve.Vector

inductive Piece where | I | O | T | S | Z | J | L
deriving DecidableEq, Fintype

inductive Cell where
| empty : Cell
| gray : Cell
| colored (p : Piece) : Cell

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
