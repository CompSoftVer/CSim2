(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

section "64-Bit Machine Word Setup"

theory Word_Setup_64
imports Word_Enum
begin

text \<open>This theory defines standard platform-specific word size and alignment.\<close>

type_synonym machine_word_len = 64
type_synonym machine_word = "machine_word_len word"

definition word_bits :: nat
where
  "word_bits = LENGTH(machine_word_len)"

text \<open>The following two are numerals so they can be used as nats and words.\<close>
definition word_size_bits :: "'a :: numeral"
where
  "word_size_bits = 3"

definition word_size :: "'a :: numeral"
where
  "word_size = 8"

lemma word_bits_conv[code]:
  "word_bits = 64"
  unfolding word_bits_def by simp

lemma word_size_word_size_bits:
  "(word_size::nat) = 2 ^ word_size_bits"
  unfolding word_size_def word_size_bits_def by simp

lemma word_bits_word_size_conv:
  "word_bits = word_size * 8"
  unfolding word_bits_def word_size_def by simp

end
