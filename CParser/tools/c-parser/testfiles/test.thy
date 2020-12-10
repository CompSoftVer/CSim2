(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory test
imports "CParser.CTranslation"
begin

external_file "test.c"   

install_C_file "test.c"

context test_global_addresses
begin
  thm SpinLock_body_def
  thm main_body_def
end
ML {*
val thy ="test.c"
local
open ProgramAnalysis
in
fun global_details vi = (srcname vi, length (get_vi_attrs vi))

val all_global_details = get_globals #> map global_details
end
*}

ML {*
val results = CalculateState.get_csenv @{theory} "test.c"
  |> the
  |> all_global_details
  |> sort (prod_ord string_ord int_ord)
*}
end
