(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory jiraver473
  imports "CParser.CTranslation"
begin

declare [[munge_info_fname="jiraver473.minfo"]]

external_file "jiraver473.c"
install_C_file "jiraver473.c"

end
