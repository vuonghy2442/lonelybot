import Klondike.State

namespace Klondike

namespace Solitaire

def encode61 (s : Solitaire) : Nat := encode s

def decode61 (n : Nat) : Solitaire := decode n

theorem encode_decode_inverse (s : Solitaire) : decode61 (encode61 s) = s := by sorry

end Solitaire

def SolverTrace := List (Nat × Move)

def traceStates (t : SolverTrace) : List Nat := t.map Prod.fst

def tracesAgree (t1 t2 : SolverTrace) : Bool := traceStates t1 = traceStates t2

end Klondike
