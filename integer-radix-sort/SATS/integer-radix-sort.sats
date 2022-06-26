(*
  Copyright © 2022 Barry Schwartz

  This program is free software: you can redistribute it and/or
  modify it under the terms of the GNU General Public License, as
  published by the Free Software Foundation, either version 3 of the
  License, or (at your option) any later version.

  This program is distributed in the hope that it will be useful, but
  WITHOUT ANY WARRANTY; without even the implied warranty of
  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
  General Public License for more details.

  You should have received copies of the GNU General Public License
  along with this program. If not, see
  <https://www.gnu.org/licenses/>.
*)

#define ATS_PACKNAME "ats2-integer-radix-sort"
#define ATS_EXTERN_PREFIX "ats2_integer_radix_sort_"

%{#
#include "integer-radix-sort/CATS/integer-radix-sort.cats"
%}

(*------------------------------------------------------------------*)

fn {a  : vt@ype}
   {tk : tkind}
g0uint_radix_sort
          {n   : int}
          (arr : &array (a, n) >> _,
           n   : size_t n)
    :<!wrt> void

fn {a  : vt@ype}
   {tk : tkind}
g0uint_radix_sort$key
          {n   : int}
          {i   : nat | i < n}
          (arr : &RD(array (a, n)),
           i   : size_t i)
    :<> g0uint tk

(*------------------------------------------------------------------*)

fn {a        : vt@ype}
   {tki, tku : tkind}
g0int_radix_sort
          {n   : int}
          (arr : &array (a, n) >> _,
           n   : size_t n)
    :<!wrt> void

fn {a   : vt@ype}
   {tki : tkind}
g0int_radix_sort$key
          {n   : int}
          {i   : nat | i < n}
          (arr : &RD(array (a, n)),
           i   : size_t i)
    :<> g0int tki

(*------------------------------------------------------------------*)
