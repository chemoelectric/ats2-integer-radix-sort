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

#define ATS_DYNLOADFLAG 0

(*------------------------------------------------------------------*)

#include "share/atspre_staload.hats"
staload UN = "prelude/SATS/unsafe.sats"
staload "integer-radix-sort/SATS/integer-radix-sort.sats"

extern fn
copy_memory (dst       : ptr,
             src       : ptr,
             num_bytes : size_t)
    :<!wrt> void =
  "mac#%"

(*------------------------------------------------------------------*)

(* The radix is 256. The sort is least significant ‘digit’ first and
   is stable. *)

(* WARNING: Much of the following code does NOT respect the linearity
            of array entries. But this unsafeness is hidden from the
            user. *)

fn {}
bin_sizes_to_indices
          (bin_indices : &array (size_t, 256) >> _)
    :<!wrt> void =
  let
    fun
    loop {i           : int | i <= 256}
         {accum       : int}
         .<256 - i>.
         (bin_indices : &array (size_t, 256) >> _,
          i           : size_t i,
          accum       : size_t accum)
        :<!wrt> void =
      if i <> i2sz 256 then
        let
          prval () = lemma_g1uint_param i
          val elem = bin_indices[i]
        in
          if elem = i2sz 0 then
            loop (bin_indices, succ i, accum)
          else
            begin
              bin_indices[i] := accum;
              loop (bin_indices, succ i, accum + g1ofg0 elem)
            end
        end
  in
    loop (bin_indices, i2sz 0, i2sz 0)
  end

fn {a  : vt@ype}
   {tk : tkind}
count_entries
          {n            : int}
          {shift        : nat}
          (arr          : &RD(array (a, n)),
           n            : size_t n,
           bin_indices  : &array (size_t?, 256)
                          >> array (size_t, 256),
           all_expended : &bool? >> bool,
           shift        : int shift)
    :<!wrt> void =
  let
    fun
    loop {i : int | i <= n}
         .<n - i>.
         (arr          : &RD(array (a, n)),
          bin_indices  : &array (size_t, 256) >> _,
          all_expended : &bool >> bool,
          i            : size_t i)
        :<!wrt> void =
      if i <> n then
        let
          prval () = lemma_g1uint_param i
          val key : g0uint tk = g0uint_radix_sort$key<a><tk> (arr, i)
          val key_shifted = key >> shift
          val digit = ($UN.cast{uint} key_shifted) land 255U
          val [digit : int] digit = g1ofg0 digit
          extern praxi set_range :
            () -<prf> [0 <= digit; digit <= 255] void
          prval () = set_range ()
          val count = bin_indices[digit]
          val () = bin_indices[digit] := succ count
        in
          all_expended := all_expended * iseqz key_shifted;
          loop (arr, bin_indices, all_expended, succ i)
        end

    prval () = lemma_array_param arr
  in
    array_initize_elt<size_t> (bin_indices, i2sz 256, i2sz 0);
    all_expended := true;
    loop (arr, bin_indices, all_expended, i2sz 0)
  end

fn {a  : vt@ype}
   {tk : tkind}
sort_by_digit
          {n            : int}
          {shift        : nat}
          (arr1         : &RD(array (a, n)),
           arr2         : &array (a, n) >> _,
           n            : size_t n,
           all_expended : &bool? >> bool,
           shift        : int shift)
    :<!wrt> void =
  let
    var bin_indices : array (size_t, 256)
  in
    count_entries<a><tk> (arr1, n, bin_indices, all_expended, shift);
    if all_expended then
      ()
    else
      let
        fun
        rearrange {i : int | i <= n}
                  .<n - i>.
                  (arr1        : &RD(array (a, n)),
                   arr2        : &array (a, n) >> _,
                   bin_indices : &array (size_t, 256) >> _,
                   i           : size_t i)
            :<!wrt> void =
          if i <> n then
            let
              prval () = lemma_g1uint_param i
              val key = g0uint_radix_sort$key<a><tk> (arr1, i)
              val key_shifted = key >> shift
              val digit = ($UN.cast{uint} key_shifted) land 255U
              val [digit : int] digit = g1ofg0 digit
              extern praxi set_range :
                () -<prf> [0 <= digit; digit <= 255] void
              prval () = set_range ()
              val [j : int] j = g1ofg0 bin_indices[digit]

              (* One might wish to get rid of this assertion somehow,
                 to eliminate the branch, should it prove a
                 problem. *)
              val () = $effmask_exn assertloc (j < n)

              val p_dst = ptr_add<a> (addr@ arr2, j)
              and p_src = ptr_add<a> (addr@ arr1, i)
              val () = copy_memory (p_dst, p_src, sizeof<a>)
              val () = bin_indices[digit] := succ (g0ofg1 j)
            in
              rearrange (arr1, arr2, bin_indices, succ i)
            end

        prval () = lemma_array_param arr1
      in
        bin_sizes_to_indices<> bin_indices;
        rearrange (arr1, arr2, bin_indices, i2sz 0)
      end
  end

fn {a  : vt@ype}
   {tk : tkind}
g0uint_sort {n    : pos}
            (arr1 : &array (a, n) >> _,
             arr2 : &array (a, n) >> _,
             n    : size_t n)
    :<!wrt> void =
  let
    fun
    loop {idigit_max, idigit : nat | idigit <= idigit_max}
         .<idigit_max - idigit>.
         (arr1       : &array (a, n) >> _,
          arr2       : &array (a, n) >> _,
          from1to2   : bool,
          idigit_max : int idigit_max,
          idigit     : int idigit)
        :<!wrt> void =
      if idigit = idigit_max then
        begin
          if ~from1to2 then
            copy_memory (addr@ arr1, addr@ arr2, sizeof<a> * n)
        end
      else if from1to2 then
        let
          var all_expended : bool
        in
          sort_by_digit<a><tk> (arr1, arr2, n, all_expended,
                                8 * idigit);
          if all_expended then
            ()
          else
            loop (arr1, arr2, false, idigit_max, succ idigit)
        end
      else
        let
          var all_expended : bool
        in
          sort_by_digit<a><tk> (arr2, arr1, n, all_expended,
                                8 * idigit);
          if all_expended then
            copy_memory (addr@ arr1, addr@ arr2, sizeof<a> * n)
          else
            loop (arr1, arr2, true, idigit_max, succ idigit)
        end
  in
    loop (arr1, arr2, true, sz2i sizeof<g1uint tk>, 0)
  end

#define SIZE_THRESHOLD 256

extern praxi
unsafe_cast_array
          {a   : vt@ype}
          {b   : vt@ype}
          {n   : int}
          (arr : &array (b, n) >> array (a, n))
    :<prf> void

implement {a} {tk}
g0uint_radix_sort {n} (arr, n) =
  if n <> 0 then
    let
      prval () = lemma_array_param arr

      fn
      sort {n    : pos}
           (arr1 : &array (a, n) >> _,
            arr2 : &array (a, n) >> _,
            n    : size_t n)
          :<!wrt> void =
        g0uint_sort<a><tk> (arr1, arr2, n)
    in
      if n <= SIZE_THRESHOLD then
        let
          var arr2 : array (a, SIZE_THRESHOLD)
          prval @(pf_left, pf_right) =
            array_v_split {a?} {..} {SIZE_THRESHOLD} {n} (view@ arr2)
          prval () = view@ arr2 := pf_left
          prval () = unsafe_cast_array{a} arr2

          val () = sort (arr, arr2, n)

          prval () = unsafe_cast_array{a?} arr2
          prval () = view@ arr2 :=
            array_v_unsplit (view@ arr2, pf_right)
        in
        end
      else
        let
          val @(pf_arr2, pfgc_arr2 | p_arr2) = array_ptr_alloc<a> n
          macdef arr2 = !p_arr2
          prval () = unsafe_cast_array{a} arr2

          val () = sort (arr, arr2, n)

          prval () = unsafe_cast_array{a?} arr2
          val () = array_ptr_free (pf_arr2, pfgc_arr2 | p_arr2)
        in
        end
    end

(*------------------------------------------------------------------*)

(* The sort for signed integers is done by mapping the key to an
   unsigned key and calling the sort for signed integers. *)

fn {a        : vt@ype}
   {tki, tku : tkind}
g0int_sort {n   : int}
           (arr : &array (a, n) >> _,
            n   : size_t n)
    :<!wrt> void =
  let
    macdef get_key = g0int_radix_sort$key<a><tki>
    prval () = lemma_array_param arr
  in
    if n = 0 then
      ()
    else
      let
        val () = $effmask_exn
          assertloc (sizeof<g0int tki> = sizeof<g0uint tku>)

        fn
        find_least_key (arr : &RD(array (a, n)))
            :<> g0int tki =
          let
            fun
            loop {i : int | i <= n}
                 .<n - i>.
                 (arr       : &RD(array (a, n)),
                  least_key : g0int tki,
                  i         : size_t i)
                :<> g0int tki =
              if i <> n then
                let
                  prval () = lemma_g1uint_param i
                  val key = get_key (arr, i)
                in
                  loop (arr, min (least_key, key), succ i)
                end
              else
                least_key
          in
            if n = 0 then
              get_key (arr, i2sz 0)
            else
              let
                val first_key = get_key (arr, i2sz 0)
              in
                loop (arr, first_key, i2sz 1)
              end
          end

        val least_key = find_least_key arr

        (* The offset is the two's complement of the least key. Thus
           the least key is mapped to zero and the order of keys is
           preserved. (We could use the unsigned image of ~1 as the
           offset, but then keys would be likely to have high bits
           set.) *)
        val offset = succ (lnot ($UN.cast{g1uint tku} least_key))

        implement
        g0uint_radix_sort$key<a><tku> (arr, i) =
          let
            val keyi = get_key (arr, i)
          in
            g0i2u keyi + offset
          end
      in
        g0uint_radix_sort<a><tku> (arr, n)
      end
  end

implement {a} {tki, tku}
g0int_radix_sort (arr, n) =
  g0int_sort<a><tki, tku> (arr, n)

(*------------------------------------------------------------------*)
