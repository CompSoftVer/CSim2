(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
*)

theory globals_in_record
imports
  "CParser.CTranslation"
begin

external_file "globals_in_record.c"
install_C_file "globals_in_record.c"

record m = f::nat

record n = f::nat

thm m.f_update_def

context globals_in_record
begin
thm stateLocal_ext_def
thm incp_body_def
thm globals.equality
term incp_body
find_theorems "zuzu_'"
thm globals.zuzu_'_def
term global_exn_var_'_update

find_theorems "zozo"

find_theorems "zyzy"
thm zyzy_def

end

end
