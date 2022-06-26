/*
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
*/

#ifndef ATS2_INTEGER_RADIX_SORT_CATS_HEADER_GUARD__
#define ATS2_INTEGER_RADIX_SORT_CATS_HEADER_GUARD__

#include <string.h>

ATSinline() void
ats2_integer_radix_sort_copy_memory (atstype_ptr dst,
                                     atstype_ptr src,
                                     atstype_size num_bytes)
{
#if defined __GNUC__
  (void) __builtin_memcpy (dst, src, num_bytes);
#else
  (void) memcpy (dst, src, num_bytes);
#endif
}

#endif  /* ATS2_INTEGER_RADIX_SORT_CATS_HEADER_GUARD__ */
