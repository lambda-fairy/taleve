import Taleve.Vector

namespace Taleve

inductive Piece where | I | O | T | S | Z | J | L
deriving DecidableEq, Fintype

inductive Mino where
| gray : Mino
| colored (p : Piece) : Mino
deriving DecidableEq, Fintype

abbrev Cell := Option Mino

def Row (w : ℕ) := Vector Cell w

instance (w) : DecidableEq (Row w) := by
  unfold Row
  infer_instance

def Row.mk {w} (row : Vector Cell w) : Row w := row

def Board (w h : ℕ) := Vector (Row w) h

instance (w h) : DecidableEq (Board w h) := by
  unfold Board
  infer_instance

namespace Board

def mk {w h} (board : Vector (Row w) h) : Board w h := board

def paste {w h w' h'} (target : Board w h) (source : Board w' h') (offsetX offsetY : ℕ) :
    Board w h :=
  Vector.pasteGrid target source offsetX offsetY

end Board

end Taleve
