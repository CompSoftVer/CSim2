(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory test_shifts
imports "CParser.CTranslation"
begin

external_file "test_shifts.c"
install_C_file "test_shifts.c"

print_locale test_shifts

end
