(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver440
  imports "CParser.CTranslation"
begin

external_file "jiraver440.c"
install_C_file "jiraver440.c"

context jiraver440
begin

thm f_body_def
thm g_body_def

lemma "f_body = g_body"
by (simp add: f_body_def g_body_def)


end

end
