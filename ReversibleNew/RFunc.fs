module Reversible.RFunc
open Reversible.RType

type RFunc =
| FPerm of Perm.Perm
| FCPerm of Perm.Perm
| FSym of RFunc
| FCTrace of Perm.Perm
| FCompose of RFunc list
| FSum of RFunc list
| FProd of RFunc list

type RTypedFunc =
| TFPerm of RType * Perm.Perm
| TFCPerm of RType * Perm.Perm
| TFCTrace of RTypedFunc
| TFCompose of RTypedFunc list
| TFSum of RTypedFunc list
| TFProd of RTypedFunc list

type Iso<'a, 'b> = ('a -> 'b) * ('b -> 'a)
