import Std.Data.HashMap.Lemmas

open Std

variable {α β : Type}
variable [BEq α] [Hashable α]

#check HashMap

#check HashMap.contains
#check HashMap.contains_insert
