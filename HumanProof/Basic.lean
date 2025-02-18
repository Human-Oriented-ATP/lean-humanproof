import Lean

namespace HumanProof

open Lean

inductive Box : Type where
| forallB (name : Name) (type : Expr) (body : Box)
| metaVariable (name : Name) (type : Expr) (body : Box)
| result (r : Expr)
| and (name : Name) (type : Expr) (inl : Box) (inr : Box)
| or (inl : Box) (inr : Box)
-- | letB (name : Name) (type value : Expr) (body : Box)

namespace Box

end Box

end HumanProof
