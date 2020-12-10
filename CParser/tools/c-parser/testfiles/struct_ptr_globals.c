/*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 */

struct s {
  int fld1;
  int *fld2;
  char x;
};

struct s svar;

struct t {
  int fld1;
  struct t* next;
};

struct t tvar;

