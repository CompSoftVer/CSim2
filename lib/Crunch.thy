(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Crunch
imports
  "Monad_WP/wp/WPSimp"
  Lib
  "ml-helpers/MLUtils"
keywords "crunch" "crunch_ignore" "crunches" :: thy_decl
begin

named_theorems "crunch_def"
named_theorems "crunch_rules"
named_theorems "crunch_param_rules"

ML_file "crunch-cmd.ML"
ML_file "Crunch.ML"

end
