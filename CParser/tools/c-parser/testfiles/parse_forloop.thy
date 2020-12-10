(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory parse_forloop
imports "CParser.CTranslation"
begin

external_file "parse_forloop.c"
install_C_file "parse_forloop.c"

print_locale parse_forloop_global_addresses
thm parse_forloop_global_addresses.f_body_def
thm parse_forloop_global_addresses.g_body_def
thm parse_forloop_global_addresses.h_body_def

end
