(** test if the modes work correctly **)

Load Modes.


MetaCoq Run (getMode "mmode" >>= tmPrint).
MetaCoq Run Set mmode.
MetaCoq Run (getMode "mmode" >>= tmPrint).
MetaCoq Run Set mmode.
MetaCoq Run (getMode "mmode" >>= tmPrint).
MetaCoq Run Unset mmode.
MetaCoq Run (getMode "mmode" >>= tmPrint).
MetaCoq Run Set mmode.
MetaCoq Run (getMode "mmode" >>= tmPrint).


