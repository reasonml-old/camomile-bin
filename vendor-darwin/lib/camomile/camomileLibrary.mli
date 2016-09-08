# 1 "camomileLibrary.mlip"
(** Camomile's toplevel interface *)
(* Copyright (C) 2010, 2011 Yoriyuki Yamagata *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)


(** Type of configuration parametor *)
  module ConfigInt : sig
# 1 "configInt.mli"
(** Configuration values *)
module type Type = sig
(** Directory of compiled Unicode data *)
val datadir : string 

(** Directory of compiled character mapping tables a la ISO *)
val charmapdir : string 

(** Directory of camomile-style compiled character mapping table *)
val unimapdir : string 

(** Directory of compiled locale data *)
val localedir : string
end
  
# 40 "camomileLibrary.mlip"
  end

(** Default configuration. *)
  module DefaultConfig : ConfigInt.Type

(** Individual modules *)

  module OOChannel : sig
# 1 "public/oOChannel.mli"
(** Object Oriented Channel *)
(* Copyright (C) 2002, 2003, 2010 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Generic input channel
  Have the same interface of Polymorphic input channel of
  http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm 
  the behaviour defined in the recommendation above.
*)
class type ['a] obj_input_channel = 
  object 
    method close_in : unit -> unit
    method get : unit -> 'a 
  end

(** Generic output channel
  Have the same interface of Polymorphic output channel of
  http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm 
  the behaviour defined in the recommendation above.
*)
class type ['a] obj_output_channel = 
  object
    (** If close_oout cannot output all buffered objects, flush raises
      Failure *)
    method close_out : unit -> unit
    (** If flush cannot output all buffered objects, flush raises
      Failure *)
    method flush : unit -> unit
    method put : 'a -> unit
  end

(** Convert stream to obj_input_channel *)
class ['a] channel_of_stream : 'a Stream.t -> ['a] obj_input_channel

(** Convert obj_input_channel to stream *)
val stream_of_channel : 'a #obj_input_channel -> 'a Stream.t

(** Character(byte) input channel.  Have the same interface of octet
  input channel of http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm the
  behaviour defined in the recommendation above.  In addition, all
  channels are assumed to be blocking.  If you supply a non-blocking
  channel to Camomile API, the outcome is undefined.
*)
class type char_input_channel =
  object
    method input : string -> int -> int -> int
    method close_in : unit -> unit
  end

(** Character(byte) output channel.  Have the same interface of octet
  input channel of http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm the
  behaviour defined in the recommendation above.  In addition, all
  channels are assumed to be blocking.  If you supply a non-blocking
  channel to Camomile API, the outcome is undefined.
*)
class type char_output_channel =
  object
    method output : string -> int -> int -> int
    method flush : unit -> unit
    method close_out : unit -> unit
  end

(** Convert a polymorphic input channel to a character input channel *)
class char_input_channel_of : char #obj_input_channel ->
  char_input_channel

(** Convert a character input channel to a polymorphic input channel*)
class char_obj_input_channel_of : char_input_channel -> 
  [char] obj_input_channel

(** Convert a polymorphic output channel to a character output channel *)
class char_output_channel_of : char #obj_output_channel -> char_output_channel

(** Convert a character output channel to a polymorphic output channel *)
class char_obj_output_channel_of : char_output_channel -> 
  [char] obj_output_channel

(** Convert an OCaml input channel to an OO-based character input channel *)
class of_in_channel : Pervasives.in_channel -> char_input_channel

(** Convert an OCaml output channel to an OO-based character output channel *)
class of_out_channel : Pervasives.out_channel -> char_output_channel
    
# 49 "camomileLibrary.mlip"
    end

  module UChar : sig
# 1 "public/uChar.mli"
(** Unicode (ISO-UCS) characters.

   This module implements Unicode (actually ISO-UCS) characters.  All
   31-bit code points are allowed.
*)

(* Copyright (C) 2002, 2003, 2004 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Unicode characters. All 31bit code points are allowed.*) 
type t

exception Out_of_range

(** [char_of u] returns the Latin-1 representation of [u].
   If [u] can not be represented by Latin-1, raises Out_of_range *)
val char_of : t -> char

(** [of_char c] returns the Unicode character of the Latin-1 character [c] *)
val of_char : char -> t

(** [code u] returns the Unicode code number of [u].
   If the value can not be represented by a positive integer,
   raise Out_of_range *)
val code : t -> int

(** [code n] returns the Unicode character with the code number [n]. 
   If n >= 2^32 or n < 0, raises [invalid_arg] *)
val chr : int -> t

(** [uint_code u] returns the Unicode code number of [u].
   The returned int is unsigned, that is, on 32-bits platforms,
   the sign bit is used for storing the 31-th bit of the code number. *)
external uint_code : t -> int = "%identity"

(** [chr_of_uint n] returns the Unicode character of the code number [n].
   [n] is interpreted as unsigned, that is, on 32-bits platforms,
   the sign bit is treated as the 31-th bit of the code number.
   If n exceed 31-bits values, then raise [invalid_arg]. *)
val chr_of_uint : int -> t

(** Equality by code point comparison *)
val eq : t -> t -> bool

(** [compare u1 u2] returns, 
   a value > 0 if [u1] has a larger Unicode code number than [u2], 
   0 if [u1] and [u2] are the same Unicode character,
   a value < 0 if [u1] has a smaller Unicode code number than [u2]. *)
val compare : t -> t -> int

(** Aliases of [type t] *)
type uchar = t

(** Alias of [uint_code] *)
val int_of : uchar -> int

(** Alias of [chr_of_uint] *)
val of_int : int -> uchar
    
# 53 "camomileLibrary.mlip"
    end

  module USet : sig
# 1 "public/uSet.mli"
(** Sets of Unicode characters, implemented as sets of intervals.
   The signature is mostly same to Set.S in stdlib *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

type t
val empty : t
val is_empty : t -> bool
val mem : UChar.t -> t -> bool
val add : UChar.t -> t -> t

(** [add_range u1 u2 s] adds the characters in the range [u1] - [u2]
   to [s].  The range is determined by the code point order. *)
val add_range : UChar.t -> UChar.t -> t -> t

val singleton : UChar.t -> t
val remove : UChar.t -> t -> t

(** [remove_range u1 u2 s] removes the characters in the range [u1] - [u2]
   from [s].  The range is determined by the code point order. *)
val remove_range : UChar.t -> UChar.t -> t -> t

val union : t -> t -> t
val inter : t -> t -> t
val diff : t -> t -> t

(** [compl s] returns the compliment of [s]. *)
val compl : t -> t

val compare : t -> t -> int
val equal : t -> t -> bool
val subset : t -> t -> bool

(** [from u s] returns the set of elements of [s] 
   whose code points are equal or greater than [u]. *)
val from : UChar.t -> t -> t

(** [after u s] returns the set of elements of [s] 
   whose code points are greater than [u]. *)
val after : UChar.t -> t -> t

(** [until u s] returns the set of elements of [s] 
   whose code points are equal or smaller than [u]. *)
val until : UChar.t -> t -> t

(** [until u s] returns the set of elements of [s] 
   whose code points are smaller than [u]. *)
val before : UChar.t -> t -> t

val iter : (UChar.t -> unit) -> t -> unit

(** [iter_range proc s] feeds the intervals contained in [s] to
   [proc] in increasing order.  The intervals given to [proc]
   are always separated by the character not in [s]. *)
val iter_range : (UChar.t -> UChar.t -> unit) -> t -> unit

val fold : (UChar.t -> 'a -> 'a) -> t -> 'a -> 'a

(** [fold_range f s x] is equivalent to 
   [f u_i u_(i+1) (... (f u_3 u_4 (f u_1 u_2 x)))] if [s] is consisted of
   the intervals [u1]-[u2], [u3]-[u4], ..., [u_i]-[u_(i + 1)]
   in increasing order.  The intervals given to [proc]
   are always separated by the character not in [s]. *)
val fold_range : (UChar.t -> UChar.t -> 'a -> 'a) -> t -> 'a -> 'a

val for_all : (UChar.t -> bool) -> t -> bool
val exists : (UChar.t -> bool) -> t -> bool
val filter : (UChar.t -> bool) -> t -> t
val partition : (UChar.t -> bool) -> t -> t * t
val cardinal : t -> int
val elements : t -> UChar.t list

(** The list of the intervals contained in the set.  
   The returned intervals are always separated 
   by the character not in [s]. *)
val ranges : t -> (UChar.t * UChar.t) list

val min_elt : t -> UChar.t
val max_elt : t -> UChar.t

(** Returns a element roughly in the middle of the set. 
   It is not guaranteed to return the same element for 
   the sets with the same elements *)
val choose : t -> UChar.t

val uset_of_iset : ISet.t -> t
val iset_of_uset : t -> ISet.t
    
# 57 "camomileLibrary.mlip"
    end

  module UMap : sig
# 1 "public/uMap.mli"
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Maps over Unicode characters. *) 
type 'a t
val empty : 'a t
val is_empty : 'a t -> bool

(** [add ?eq u v m] returns the new map which is same to [m] 
   except it maps [u] to some value [v'] which satisfies [eq v v']. 
   If [eq] is not supplied, structural equality is used. *)
val add : ?eq:('a -> 'a -> bool) -> UChar.t -> 'a -> 'a t -> 'a t

(** [add ?eq u1 u2 v m] returns the new map which is same to [m] 
   except it maps characters in the range [u1]-[u2] 
   to some value [v'] which satisfies [eq v v']. 
   If [eq] is not supplied, structural equality is used. *)
val add_range : ?eq:('a -> 'a -> bool) -> 
  UChar.t -> UChar.t -> 'a -> 'a t -> 'a t

val find : UChar.t -> 'a t -> 'a
val remove : UChar.t -> 'a t -> 'a t

(** [remove_range u1 u2 m] removes [u1]-[u2] from the domain of [m] *)
val remove_range : UChar.t -> UChar.t -> 'a t -> 'a t

(** [from u m] restricts the domain of [m] to the characters whose
   code points are equal or greater than [u]. *)
val from : UChar.t -> 'a t -> 'a t

(** [after u m] restricts the domain of [m] to the characters whose
   code points are greater than [u]. *)
val after : UChar.t -> 'a t -> 'a t

(** [until u m] restricts the domain of [m] to the characters whose
   code points are equal or smaller than [u]. *)
val until : UChar.t -> 'a t -> 'a t

(** [before u m] restricts the domain of [m] to the characters whose
   code points are smaller than [u]. *)
val before : UChar.t -> 'a t -> 'a t

val mem : UChar.t -> 'a t -> bool
val iter : (UChar.t -> 'a -> unit) -> 'a t -> unit

(** [iter proc m] : For each contingent region [u1]-[u2] 
   that is mapped to a constant [v], [proc u1 u2 v] is called.
   The order of call is determined by increasing order on [u1]. *)
val iter_range : (UChar.t -> UChar.t -> 'a -> unit) -> 'a t -> unit

(** [map ?eq f m] and [mapi ?eq f m] :  Similar to [map] and [mapi] 
   in stdlib Map, but if the map [m'] is returned,  it is only guaranteed 
   that [eq (find u m') (f (find u m ))] is true for [map] and 
   [eq (find u m') (f u (find u m ))] is true for [mapi].  If [eq] is
   not specified, structural equality is used. *)

val map : ?eq:('b -> 'b -> bool) -> ('a -> 'b) -> 'a t -> 'b t
val mapi : ?eq:('b -> 'b -> bool) -> (UChar.t -> 'a -> 'b) -> 'a t -> 'b t

val fold : (UChar.t -> 'b -> 'a -> 'a) -> 'b t -> 'a -> 'a

(** [fold_range f m x] is equivalent to
   [f u_(2n) u_(2n+1) v_n (... (f u_1 u_2 v_1 x))] where all characters in
   the range [u_(2k)]-[u_(2k+1)] are mapped to [v_k] and 
   [u_1] < [u_3] < ... in code point order.  
   For each range [u_(2k)]-[u_(2k+1)] is separated by a character 
   which is not mapped to [v_k]. *)
val fold_range : (UChar.t -> UChar.t -> 'b -> 'a -> 'a) -> 'b t -> 'a -> 'a

(** Constant map.*)
val set_to_map : USet.t -> 'a -> 'a t

(** Domain. *)
val domain : 'a t -> USet.t

(** [map_to_set p m] returns the set of characters which are mapped
   to values satisfying the predicate [p] by [m]. *)
val map_to_set : ('a -> bool) -> 'a t -> USet.t

val umap_of_imap : 'a IMap.t -> 'a t
val imap_of_umap : 'a t -> 'a IMap.t
    
# 61 "camomileLibrary.mlip"
    end

  module UCharTbl : sig
# 1 "public/uCharTbl.mli"
(** Fast lookup tables for Unicode.  Accessible by constant time. *)
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)


(** Fast lookup tables.  Accessible by constant time. *)
  type 'a tbl
  type 'a t = 'a tbl

  val get : 'a tbl -> UChar.t -> 'a

  module type Type = sig
    type elt
    type t = elt tbl
    val get : elt tbl -> UChar.t -> elt

(** [of_map def m] creates the table which has the same value to [m].
   The table returns [def] for the characters for which [m] is undefined. *)
    val of_map : elt -> elt UMap.t -> t
  end

(** Equality and hash are necessary for table generation. *)
  module Make : 
  functor (H : Hashtbl.HashedType) ->  (Type with type elt = H.t)

(** Tables for boolean values. *)
  module Bool : sig
    type t
    val get : t -> UChar.t -> bool
    val of_set : USet.t -> t
  end

(** Tables for small (< 256, >=0) integers *)
  module Bits : sig
    type t
    val of_map : int -> int UMap.t -> t
    val get : t -> UChar.t -> int
  end

(** Tables for integers.  If integers are not span the whole 31-bit or
63-bit values, [Bytes.t] is more space efficient than [int tbl]. *)
  module Bytes : sig
    type t
    val of_map : int -> int UMap.t -> t
    val get : t -> UChar.t -> int
  end

(** Tables for bytes. *)
  module Char : sig
    type t
    val of_map : char -> char UMap.t -> t
    val get : t -> UChar.t -> char
  end
    
# 65 "camomileLibrary.mlip"
    end

  module UnicodeString : sig
# 1 "public/unicodeString.mli"
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Signature for Unicode strings.  
   {!UText}, {!XString}, {!UTF8}, {!UTF16}, {!UCS4}
   have matched signatures to UStorage
   and satisfy the semantics described below.  If users want to supply
   their own Unicode strings, please design the module with the 
   following signature and properties. *)

module type Type = sig
(** The type of string. *)
  type t

(** [get t i] : [i]-th character of the storage.*)
  val get : t -> int -> UChar.t

(** [init len f] creates a new storage.
   the returned storage has length [len], its nth-element is [f n].
   [f] is called with integers [0 ... len - 1], only once for each integer.
   The call is in the increasing order f 0, f 1, f 2, ... *)
  val init : int -> (int -> UChar.t) -> t

(** The number of Unicode characters in the storage *)
  val length : t -> int

(** locations in storages.*)
  type index

(** [look t i] : The character in the location [i] of [t].*)
  val look : t -> index -> UChar.t

(** [nth t n] : the location of the [n]-th character in [t].*)
  val nth : t -> int -> index

(** [next x i, prev x i] :
   The operation is valid if [i] points the valid element, i.e. the
   returned value may point the location beyond valid elements by one.
   If [i] does not point a valid element, the results are unspecified. *)

  val next : t -> index -> index
  val prev : t -> index -> index

(* [out_of_range t i] tests whether [i] is inside of [t]. *)
  val out_of_range : t -> index -> bool
      
  val iter : (UChar.t -> unit) -> t -> unit

(* Code point comparison *)
  val compare : t -> t -> int

(** The location of the first character in the storage. *)
  val first : t -> index

(** The location of the last character in the storage. *)
  val last : t -> index

(** [move t i n] :
   if [n] >= 0, then returns [n]-th character after [i] and
   otherwise returns -[n]-th character before [i].
   If there is no such character, or [i] does not point 
   a valid character, the result is unspecified. *)
  val move : t -> index -> int -> index

(** [compare_index t i j] returns
   a positive integer if [i] is the location placed after [j] in [t],
   0 if [i] and [j] point the same location, and
   a negative integer if [i] is the location placed before [j] in [t]. *)
  val compare_index : t -> index -> index -> int

(** Character buffers.  Similar to Buffer. *)
  module Buf : sig
    type buf

(** [create n] creates the buffer.  [n] is used to determine
   the initial size of the buffer.  The meaning of [n] differs from
   modules to modules. *)
    val create : int -> buf

    val contents : buf -> t
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> t -> unit
    val add_buffer : buf -> buf -> unit
  end
end

    
# 69 "camomileLibrary.mlip"
    end

  module UText : sig
# 1 "public/uText.mli"
(** An implementation of Unicode string. *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** An implementation of Unicode string.  
   Internally, it uses integer array.
   The semantics matches the description of UStorage. *)
  
(** Phantom type for distinguishing mutability *)
  type mutability = [ `Mutable | `Immutable ]

  type 'a text
  type utext = [`Immutable] text
  type ustring = [`Mutable] text
  type t = utext

  val utext_of_ustring : ustring -> utext
  val ustring_of_utext : utext -> ustring
  val get :  'a text -> int -> UChar.t

(** [set s i u] sets the [i]-th character in [s] to [u]. *)
  val set :  ustring -> int -> UChar.t -> unit

  type index

  val look : 'a text -> index -> UChar.t
  val nth : 'a text -> int -> index
  val first : 'a text -> index
  val last : 'a text -> index
  val out_of_range : 'a text -> index -> bool
  val compare_index : 'a text -> index -> index -> int
  val next : 'a text -> index -> index
  val prev : 'a text -> index -> index
  val move : 'a text -> index -> int -> index

  val length : 'a text -> int

(** Conversion from Latin-1 strings. *)
  val of_string : string -> utext

  val init : int -> (int -> UChar.t) -> utext
  val init_ustring : int -> (int -> UChar.t) -> ustring

(** The semantics of these function are similar to 
   the equivalents of string. *)
  val make : int -> UChar.t -> ustring
  val copy : ustring -> ustring
  val sub : 'a text -> int -> int -> 'a text
  val fill : ustring -> int -> int -> UChar.t -> unit
  val blit : 'a text -> int -> ustring -> int -> int -> unit
  val append : 'a text -> 'b text -> 'a text
  val iter : (UChar.t -> unit) -> 'a text -> unit
  val compare : 'a text -> 'b text -> int

  module Buf : sig
    type buf

(** [create n] creates the buffer which initially can contain
   [n] Unicode characters. *)
    val create : int -> buf

    val contents : buf -> t
    val contents_string : buf -> ustring
    val length : buf -> int
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> 'a text -> unit
    val add_buffer : buf -> buf -> unit
  end
    
# 73 "camomileLibrary.mlip"
    end

  module XString : sig
# 1 "public/xString.mli"
(** eXtensible Unicode string.  
   The semantics matches the description of UStorage. 
   The detail may be going to change.*)

(* Copyright 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

  type xstring
  type t = xstring

  val get : xstring -> int -> UChar.t
  val set : xstring -> int -> UChar.t -> unit
  val length : xstring -> int
  val init : int -> (int -> UChar.t) -> xstring

  type index
  val look : xstring -> index -> UChar.t
  val nth : xstring -> int -> index
  val first : xstring -> index
  val last : xstring -> index
  val out_of_range : xstring -> index -> bool
  val next : xstring -> index -> index
  val prev : xstring -> index -> index
  val move : xstring -> index -> int -> index
  val compare_index : xstring -> index -> index -> int

  val make : ?bufsize:int -> int -> UChar.t -> xstring
  val clear : xstring -> unit
  val reset : xstring -> unit
  val copy : xstring -> xstring
  val sub : xstring -> int -> int -> xstring
  val add_char : xstring -> UChar.t -> unit
  val add_text : xstring -> 'a UText.text -> unit
  val add_xstring : xstring -> xstring -> unit
  val shrink : xstring -> int -> unit
  val append : xstring -> xstring -> xstring
  val utext_of : xstring -> UText.t
  val ustring_of : xstring -> UText.ustring
      
  val iter : (UChar.t -> unit) -> xstring -> unit
  val compare : t -> t -> int

  module Buf : sig
    type buf
    val create : int -> buf
    val contents : buf -> t
    val length : buf -> int
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> t -> unit
    val add_buffer : buf -> buf -> unit
  end
    
# 77 "camomileLibrary.mlip"
    end

  module SubText : sig
# 1 "public/subText.mli"
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Sub-texts, parts of original (ur-) texts.  
   The signature and semantics matches those of UStorage. *)
module type Type = sig
  type t

  val get : t -> int -> UChar.t

  val init : int -> (int -> UChar.t) -> t
  val length : t -> int

  type index
  val look : t -> index -> UChar.t
  val nth : t -> int -> index
  val first : t -> index
  val last : t -> index

  val next : t -> index -> index
  val prev : t -> index -> index
  val move : t -> index -> int -> index
  val out_of_range : t -> index -> bool
  val compare_index : t -> index -> index -> int
      
  val iter : (UChar.t -> unit) -> t -> unit
  val compare : t -> t -> int

  module Buf : sig
    type buf
    val create : int -> buf
    val contents : buf -> t
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> t -> unit
    val add_buffer : buf -> buf -> unit
  end      

(** The type of original texts. *)
  type ur_text

(** The type of indexes of original texts. *)
  type ur_index

(** [refer t i j] returns the part of [t] from [i] until [j].
   The character pointed by [j] is not included in the result.
   If [j] is equal to [i] or located before [j], the result is
   an empty string. *)
  val refer : ur_text -> ur_index -> ur_index -> t

(** [excerpt t] copies the contents of [t] as a new ur_text. *)
  val excerpt : t -> ur_text

(** [context t] returns the tuple [(s, i, j)] such that
   [t = refer s i j]. *)
  val context : t -> ur_text * ur_index * ur_index

(** Conversion from indexes of sub-texts to ur_texts. *)
  val ur_index_of : t -> index -> ur_index
end

module Make : functor (Text : UnicodeString.Type) -> 
  (Type with type ur_text = Text.t and type ur_index = Text.index)
    
# 81 "camomileLibrary.mlip"
    end

  module ULine : sig
# 1 "public/uLine.mli"
(** Line IO *) 
(* Copyright (C) 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Line I/O, conversion of line separators. *)
open OOChannel

(** Line separators.  
   - [`CR] specifies carriage return.
   - [`LF] specifies linefeed.
   - [`CRLF] specifies the sequence of carriage return and linefeed.
   - [`NEL] specifies next line (\u0085).
   - [`LS] specifies Unicode line separator (\u2028).
   - [`PS] specifies Unicode paragraph separator (\u2029). *)
type separator =
  [ `CR
  | `LF
  | `CRLF
  | `NEL
  | `LS
  | `PS ]

(** [new input separator input_obj] creates the new input channel object
   {!OOChannel.obj_input_channel} which reads from [input_obj] and
   converts line separators (all of CR, LF, CRLF, NEL, LS, PS) to
   [separator]. *)
class input : separator -> 
  UChar.t #obj_input_channel -> [UChar.t] obj_input_channel

(** [new output separator output_obj] creates the new output channel
   object {!OOChannel.obj_output_channel} which receives Unicode characters 
   and converts line separators (all of CR, LF, CRLF, NEL, LS, PS) to
   [separator]. *)
class output : separator ->
  UChar.t #obj_output_channel -> [UChar.t] obj_output_channel

module type Type = sig

  type text

(** [new input_line input_obj] creates the new input channel object
   {!OOChannel.obj_input_channel} which reads Unicode characters 
   from [input_obj] and output lines.  All of CR, LF, CRLF, NEL, LS, PS, 
   as well as FF (formfeed) are recognised as a line separator. *)
  class input_line : UChar.t #obj_input_channel -> [text] obj_input_channel

(** [new output_line ~sp output_obj] create the new output channel object
   {!OOChannel.obj_output_channel} which output each line to [output_obj]
   using [sp] as a line separator.  
   If [sp] is omitted, linefeed (LF) is used. *)
  class output_line : ?sp:separator ->
      UChar.t #obj_output_channel -> [text] obj_output_channel

end

module Make : functor (Text : UnicodeString.Type) ->
  (Type with type text = Text.t)
    
# 85 "camomileLibrary.mlip"
    end

  module Locale : sig
# 1 "public/locale.mli"
(* Copyright (C) 2003 Yamagata Yoriyuki *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Camomile has a locale system similar to Java.
   A locale is a string with a form as
   "<LANG>_<COUNTRY>_<MODIFIER>..." where <LANG> is 
   a 2-letter ISO 639 language code, <COUNTRY> is a 2-letter ISO 3166
   country code.  Some field may not present. *)

(** Type of locales. *)
type t = string

(** [read root suffix reader locale]
   reads locale information using [reader].  
   Locale data is supposed to reside in [root] directory with 
   the name [locale].[suffix].
   [reader] takes [in_channel] as an argument and read data from in_channel.
   If data is not found, then [reader] should raise Not_found.
   If the file is not found or [reader] raises Not_found, then 
   more generic locales are tried.
   For example, if fr_CA.[suffix] is not found, then [read] tries fr.[suffix].
   If fr.[suffix] is also not found, then the file [root].[suffix] is tried.
   Still the data is not found, then [Not_found] is raised. *)
val read : string -> string -> (in_channel -> 'a) -> string -> 'a

(** [contain loc1 loc2] :
   If [loc1] is contained in [loc2] then true otherwise false.
   For example, "fr" is contained in "fr_CA" while "en_CA" 
   does not contain "fr" *)
val contain : string -> string -> bool
    
# 89 "camomileLibrary.mlip"
    end

  module UTF8 : sig
# 1 "public/uTF8.mli"
(** UTF-8 encoded Unicode strings. The type is normal string. *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki.  *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)


(** UTF-8 encoded Unicode strings. The type is normal string. *)
type t = string

exception Malformed_code

(** [validate s]
   successes if s is valid UTF-8, otherwise raises Malformed_code.
   Other functions assume strings are valid UTF-8, so it is prudent
   to test their validity for strings from untrusted origins. *)
val validate : t -> unit

(* All functions below assume string are valid UTF-8.  If not,
 * the result is unspecified. *)

(** [get s n] returns [n]-th Unicode character of [s].
   The call requires O(n)-time. *)
val get : t -> int -> UChar.t

(** [init len f] 
   returns a new string which contains [len] Unicode characters.
   The i-th Unicode character is initialized by [f i] *)
val init : int -> (int -> UChar.t) -> t

(** [length s] returns the number of Unicode characters contained in s *)
val length : t -> int
    
(** Positions in the string represented by the number of bytes from the head.
   The location of the first character is [0] *)
type index = int

(** [nth s n] returns the position of the [n]-th Unicode character. 
   The call requires O(n)-time *)
val nth : t -> int -> index

(** The position of the head of the first Unicode character. *)
val first : t -> index

(** The position of the head of the last Unicode character. *)
val last : t -> index

(** [look s i]
   returns the Unicode character of the location [i] in the string [s]. *)
val look : t -> index -> UChar.t

(** [out_of_range s i]
   tests whether [i] is a position inside of [s]. *)
val out_of_range : t -> index -> bool

(** [compare_index s i1 i2] returns
   a value < 0 if [i1] is the position located before [i2], 
   0 if [i1] and [i2] points the same location,
   a value > 0 if [i1] is the position located after [i2]. *)
val compare_index : t -> index -> index -> int

(** [next s i]
   returns the position of the head of the Unicode character
   located immediately after [i]. 
   If [i] is inside of [s], the function always successes.
   If [i] is inside of [s] and there is no Unicode character after [i],
   the position outside [s] is returned.  
   If [i] is not inside of [s], the behaviour is unspecified. *)
val next : t -> index -> index

(** [prev s i]
   returns the position of the head of the Unicode character
   located immediately before [i]. 
   If [i] is inside of [s], the function always successes.
   If [i] is inside of [s] and there is no Unicode character before [i],
   the position outside [s] is returned.  
   If [i] is not inside of [s], the behaviour is unspecified. *)
val prev : t -> index -> index

(** [move s i n]
   returns [n]-th Unicode character after [i] if n >= 0,
   [n]-th Unicode character before [i] if n < 0.
   If there is no such character, the result is unspecified. *)
val move : t -> index -> int -> index
    
(** [iter f s]
   applies [f] to all Unicode characters in [s].  
   The order of application is same to the order 
   of the Unicode characters in [s]. *)
val iter : (UChar.t -> unit) -> t -> unit

(** Code point comparison by the lexicographic order.
   [compare s1 s2] returns
   a positive integer if [s1] > [s2],
   0 if [s1] = [s2],
   a negative integer if [s1] < [s2]. *)
val compare : t -> t -> int

(** Buffer module for UTF-8 strings *)
module Buf : sig
  (** Buffers for UTF-8 strings. *) 
  type buf

  (** [create n] creates the buffer with the initial size [n]-bytes. *)   
  val create : int -> buf

  (* The rest of functions is similar to the ones of Buffer in stdlib. *)
  (** [contents buf] returns the contents of the buffer. *)
  val contents : buf -> t

  (** Empty the buffer, 
     but retains the internal storage which was holding the contents *)
  val clear : buf -> unit

  (** Empty the buffer and de-allocate the internal storage. *)
  val reset : buf -> unit

  (** Add one Unicode character to the buffer. *)
  val add_char : buf -> UChar.t -> unit

  (** Add the UTF-8 string to the buffer. *)
  val add_string : buf -> t -> unit

  (** [add_buffer b1 b2] adds the contents of [b2] to [b1].
     The contents of [b2] is not changed. *)
  val add_buffer : buf -> buf -> unit
end with type buf = Buffer.t
    
# 93 "camomileLibrary.mlip"
    end

  module UTF16 : sig
# 1 "public/uTF16.mli"
(* Copyright (C) 2002, 2003, Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** UTF-16 encoded string. the type is the bigarray of 16-bit integers.
   The characters must be 21-bits code points, and not surrogate points,
   0xfffe, 0xffff.
   Bigarray.cma or Bigarray.cmxa must be linked when this module is used. *)
type t = 
    (int, Bigarray.int16_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

exception Malformed_code

(** [validate s]
   If [s] is valid UTF-16 then successes otherwise raises [Malformed_code].
   Other functions assume strings are valid UTF-16, so it is prudent
   to test their validity for strings from untrusted origins. *)
val validate : t -> unit

(** All functions below assume strings are valid UTF-16.  If not,
   the result is unspecified. *)

(** [get s n] returns [n]-th Unicode character of [s].
   The call requires O(n)-time. *)
val get : t -> int -> UChar.t

exception Out_of_range

(** [init len f]
   returns a new string which contains [len] Unicode characters.
   The i-th Unicode character is initialized by [f i] 
   if the character is not representable, raise [Out_of_range]. *)
val init : int -> (int -> UChar.t) -> t

(** [length s] returns the number of Unicode characters contained in s *)
val length : t -> int
    
(** Positions in the string represented by the number of 16-bit unit
   from the head.
   The location of the first character is [0] *)
type index = int

(** [nth s n] returns the position of the [n]-th Unicode character. 
   The call requires O(n)-time *)
val nth : t -> int -> index

(** [first s] : The position of the head of the last Unicode character. *)
val first : t -> index

(** [last s] : The position of the head of the last Unicode character. *)
val last : t -> index

(** [look s i ]
   returns the Unicode character of the location [i] in the string [s]. *)
val look : t -> index -> UChar.t

(** [out_of_range s i] tests whether [i] is inside of [s]. *)
val out_of_range : t -> index -> bool

(** [compare_aux s i1 i2] returns
 - If [i1] is the position located before [i2], a value < 0,
 - If [i1] and [i2] points the same location, 0,
 - If [i1] is the position located after [i2], a value > 0. 

*)
val compare_index : t -> index -> index -> int

(** [next s i]
   returns the position of the head of the Unicode character
   located immediately after [i]. 
 - If [i] is a valid position, the function always success.
 - If [i] is a valid position and there is no Unicode character after [i],
   the position outside [s] is returned.  
 - If [i] is not a valid position, the behaviour is undefined. 
 
*)
val next : t -> index -> index

(** [prev s i]
   returns the position of the head of the Unicode character
   located immediately before [i]. 
   - If [i] is a valid position, the function always success.
   - If [i] is a valid position and there is no Unicode character before [i],
   the position outside [s] is returned.  
   - If [i] is not a valid position, the behaviour is undefined. 

*)
val prev : t -> index -> index

(* [move s i n]
 - If n >= 0, returns [n]-th Unicode character after [i].
 - If n < 0, returns [-n]-th Unicode character before [i].
 0 If there is no such character, the result is unspecified.
 
*)
val move : t -> index -> int -> index
    
(** [iter f s]
   Apply [f] to all Unicode characters in [s].  
   The order of application is same to the order 
   in the Unicode characters in [s]. *)
val iter : (UChar.t -> unit) -> t -> unit

(** Code point comparison *)
val compare : t -> t -> int

(** Buffer module for UTF-16 *)
module Buf : sig
  type buf

  (** create n : creates the buffer with the initial size [n]. *)   
  val create : int -> buf

  (** The rest of functions is similar to the ones of Buffer in stdlib. *)

  val contents : buf -> t
  val clear : buf -> unit
  val reset : buf -> unit

  (** if the character is not representable, raise Out_of_range *)
  val add_char : buf -> UChar.t -> unit

  val add_string : buf -> t -> unit
  val add_buffer : buf -> buf -> unit
end
    
# 97 "camomileLibrary.mlip"
    end

  module UCS4 : sig
# 1 "public/uCS4.mli"
(** UCS4 encoded string. The type is the bigarray of 32-bit integers.
   Bigarray.cma or Bigarray.cmxa must be linked when this module is used. *)

(* Copyright (C) 2002, 2003, 2004 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

type t = 
    (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t

exception Malformed_code

(** [validate s]
   If [s] is valid UCS4 then successes otherwise raises [Malformed_code].
   Other functions assume strings are valid UCS4, so it is prudent
   to test their validity for strings from untrusted origins. *)
val validate : t -> unit

(** All functions below assume strings are valid UCS4.  If not,
   the result is unspecified. *)

(** [get s n] returns [n]-th Unicode character of [s]. *)
val get : t -> int -> UChar.t

(** [init len f]
   returns a new string which contains [len] Unicode characters.
   The i-th Unicode character is initialised by [f i] *)
val init : int -> (int -> UChar.t) -> t

(** [length s] returns the number of Unicode characters contained in [s] *)
val length : t -> int
    
(** Positions in the string represented by the number of characters
   from the head.
   The location of the first character is [0] *)
type index = int

(** [nth s n] returns the position of the [n]-th Unicode character. 
   The call requires O(n)-time *)
val nth : t -> int -> index

(** [first s] : The position of the head of the last Unicode character. *)
val first : t -> index

(** [last s] : The position of the head of the last Unicode character. *)
val last : t -> index

(** [look s i]
   returns the Unicode character of the location [i] in the string [s]. *)
val look : t -> index -> UChar.t

(** [out_of_range s i]
   tests whether [i] points the valid position of [s]. *)
val out_of_range : t -> index -> bool

(** [compare_aux s i1 i2] returns
   If [i1] is the position located before [i2], a value < 0,
   If [i1] and [i2] points the same location, 0,
   If [i1] is the position located after [i2], a value > 0. *)
val compare_index : t -> index -> index -> int

(** [next s i]
   returns the position of the head of the Unicode character
   located immediately after [i]. 
   If [i] is a valid position, the function always success.
   If [i] is a valid position and there is no Unicode character after [i],
   the position outside [s] is returned.  
   If [i] is not a valid position, the behaviour is undefined. *)
val next : t -> index -> index

(** [prev s i]
   returns the position of the head of the Unicode character
   located immediately before [i]. 
   If [i] is a valid position, the function always success.
   If [i] is a valid position and there is no Unicode character before [i],
   the position outside [s] is returned.  
   If [i] is not a valid position, the behaviour is undefined. *)
val prev : t -> index -> index

(** [move s i n] :
   If n >= 0, returns [n]-th Unicode character after [i].
   If n < 0, returns [-n]-th Unicode character before [i].
   If there is no such character, the result is unspecified. *)
val move : t -> index -> int -> index
    
(** [iter f s] :
   Apply [f] to all Unicode characters in [s].  
   The order of application is same to the order 
   in the Unicode characters in [s]. *)
val iter : (UChar.t -> unit) -> t -> unit

(** Code point comparison *)
val compare : t -> t -> int

(** Buffer module for UCS4 *)
module Buf : sig
  type buf
  (** [create n] creates the buffer with the initial size [n]. *)   
  val create : int -> buf

  (** The rest of functions is similar to the ones of Buffer in stdlib. *)

  val contents : buf -> t
  val clear : buf -> unit
  val reset : buf -> unit

  val add_char : buf -> UChar.t -> unit

  val add_string : buf -> t -> unit
  val add_buffer : buf -> buf -> unit
end
    
# 101 "camomileLibrary.mlip"
    end

  module UPervasives : sig
# 1 "public/uPervasives.mli"
(** Functions for toplevel *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

type uchar = UChar.t

(** Aliases for UChar.uint_code, UChar.chr_of_uint *)

val int_of_uchar : uchar -> int
val uchar_of_int : int -> uchar

val escaped_uchar : uchar -> string
val escaped_utf8 : string -> string

val printer_utf8 : Format.formatter -> string -> unit
val printer_uchar : Format.formatter -> uchar -> unit
    
# 105 "camomileLibrary.mlip"
    end

  module URe : sig
# 1 "public/uRe.mli"
(** Regular expression engine. *)

(* Copyright (C) 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Abstract syntax trees of regular expressions. *)
type regexp  =
  [ `Alt of regexp * regexp
  | `Seq of regexp * regexp
  | `Rep of regexp
  | `Repn of regexp * int * int option
  | `After of regexp   
  | `Before of regexp
  | `Epsilon
  | `Group of regexp
  | `OneChar
  | `String of UChar.t list
  | `Set of USet.t
  | `BoS
  | `EoS ]

(** Match semantics. *)
type match_semantics = [ `First | `Shortest | `Longest ]

(** Remove [`Group] from the regular expressions. *)
val no_group : regexp -> regexp

module type Type = sig
  type text
  type index
  type compiled_regexp

  module SubText : 
    SubText.Type with type ur_text = text and type ur_index = index

(** Compile regular expressions. *)
  val compile : regexp -> compiled_regexp

(** [regexp_match ?sem r t i] tries matching [r] and substrings
   of [t] beginning from [i].  If match successes,  [Some g] is 
   returned where [g] is the array containing the matched 
   string of [n]-th group in the [n]-element.  
   The matched string of the whole [r] is stored in the [0]-th element.  
   If matching fails, [None] is returned. *)
  val regexp_match : ?sem:match_semantics ->
    compiled_regexp -> text -> index -> SubText.t option array option

(** [string_match r t i] tests whether [r] can match a substring
   of [t] beginning from [i]. *)
  val string_match : compiled_regexp -> text -> index -> bool

(** [search_forward ?sem r t i] searches a substring of [t]
   matching [r] from [i].  The returned value is similar to 
   {!URe.Type.regexp_match}. *)
  val search_forward : ?sem:match_semantics ->
      compiled_regexp -> text -> index -> SubText.t option array option
end

module Make : functor (Text : UnicodeString.Type) ->
  Type with type text = Text.t and type index = Text.index
    
# 109 "camomileLibrary.mlip"
    end

  module CharEncoding : sig
# 1 "public/charEncoding.mli"
(* Copyright (C) 2001, 2002, 2003, Yamagata Yoriyuki *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

module type Interface = sig
(** Module for character encodings. *)
open OOChannel

exception Malformed_code		(**Failure of decoding*)
exception Out_of_range			(**Failure of encoding*)

(** Type for encodings. *)
type t

(** [automatic name [enc_1; enc_2; ... enc_n] enc]
   creates the new encoding [name]
   doing automatic encoding detection among [enc_1], [enc_2], ..., [enc_n]
   by the given order.   [enc] is used for encoding. *)
val automatic : string -> t list -> t -> t

(** [new_enc name enc] registers the new encoding [enc]
   under the name [name] *)
val new_enc : string -> t -> unit

(** [alias alias name] : Define [alias] as an alias of 
   the encoding with the name [name]. *)
val alias : string -> string -> unit

(** Returns the encoding of the given name.
   Fails if the encoding is unknown.
   Encoding names are the same to codeset names in charmap files for
   the encodings defined by charmap.
   See charmaps directory in the source directory for the available encodings.
   In addition to the encodings via the charmap files, camomile supports
   ISO-2022-CN, ISO-2022-JP, ISO-2022-JP-2, ISO-2022-KR, jauto (Auto 
   detection of Japanese encodings), UTF-8, UTF-16, UTF-16BE, UTF-16LE.
   UTF-32, UTF-32BE, UTF-32LE, UCS-4(Big endian order).
   The encoding also can be referred by "IANA/<IANA name>", if the encoding 
   is supported. *)
val of_name : string -> t

(** Returns the name of the encoding. *)
val name_of : t -> string

(** Shortcuts *)

val ascii : t
val latin1 : t
val utf8 : t
val utf16 : t
val utf16be : t
val utf16le : t
val utf32 : t
val utf32be : t
val utf32le : t
val ucs4 : t

(** [recode_string ~in_enc ~out_enc s] 
   converts the string [s] from [in_enc] to [out_enc]. *)
val recode_string :
   in_enc:t -> out_enc:t -> string -> string

(** [new uchar_input_channel_of enc c_in] creates the new intput
  channel which convert characters to Unicode using encoding
  [enc]. *)
class uchar_input_channel_of : 
  t -> char_input_channel -> [UChar.t] obj_input_channel

(** [new uchar_ouput_channel_of enc c_out] creates the new output
  channel which convert Unicode to its byte representation using
  encoding [enc]. *)
class uchar_output_channel_of :
  t -> char_output_channel -> [UChar.t] obj_output_channel

(** [new convert_uchar_input enc c_in] creates the new channel which
  convert Unicode input to its byte representation using encoding
  [enc]. *)
class convert_uchar_input :
  t -> UChar.t obj_input_channel -> char_input_channel

(** [new convert_uchar_output enc c_in] creates the new channel which
  convert character output to Unicode using encoding [enc]. *)
class convert_uchar_output :
  t -> UChar.t obj_output_channel -> char_output_channel

(** [new convert_input in_enc out_enc c_in] create the new input
  channel using encoding [out_enc] from the input channel using
  encoding [in_enc] *)
class convert_input : 
  in_enc:t -> out_enc:t -> char_input_channel -> char_input_channel

(** [new convert_ouput in_enc out_enc c_in] create the new output
  channel using encoding [in_enc] from the output channel using
  encoding [out_enc] *)
class convert_output :
  in_enc:t -> out_enc:t -> char_output_channel -> char_output_channel

(** [new out_channel enc outchan] creates the output channel object 
  {!OOChannel.obj_output_channel} which
  receives Unicode characters and outputs them to [outchan] using
  the encoding [enc]. *)
class out_channel : t -> Pervasives.out_channel -> [UChar.t] obj_output_channel

(** [new in_channel enc inchan] creates the intput channel object 
   {!OOChannel.obj_input_channel} which
   reads bytes from [inchan] and converts them to Unicode characters. *)
class in_channel : t -> Pervasives.in_channel -> [UChar.t] obj_input_channel

(** [ustream_of enc chars] converts the byte stream [chars] 
   to the Unicode character stream by the encoding [enc]. *)
val ustream_of : t -> char Stream.t -> UChar.t Stream.t

(** [char_stream_of enc uchars] converts the Unicode character stream 
   [uchars] to the byte stream by the encoding [enc] *)
val char_stream_of : t -> UChar.t Stream.t -> char Stream.t

module type Type =
  sig
    type text

   (** [decode enc s] converts the string [s] encoded 
      by the encoding [enc] to the Unicode text. *)
    val decode : t -> string -> text

   (** [encode enc t] converts the Unicode text [t] to the string
      by the encoding [enc].*)
    val encode : t -> text -> string
  end

module Make (Text : UnicodeString.Type) : (Type with type text = Text.t)
end

module Configure (Config : ConfigInt.Type) : Interface
  
# 113 "camomileLibrary.mlip"
  end

  module UCharInfo : sig
# 1 "public/uCharInfo.mli"
(** Unicode character informations *)
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki.*)
(*               2010 Pierre Chambart *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

module type Type = sig

(** Character Information *)

(** Type of Unicode general character categories.  
   Each variant specifies
 - [`Lu] : Letter, Uppercase 
 - [`Ll] : Letter, Lowercase 
 - [`Lt] : Letter, Titlecase 
 - [`Mn] : Mark, Non-Spacing 
 - [`Mc] : Mark, Spacing Combining 
 - [`Me] : Mark, Enclosing 
 - [`Nd] : Number, Decimal Digit 
 - [`Nl] : Number, Letter 
 - [`No] : Number, Other 
 - [`Zs] : Separator, Space 
 - [`Zl] : Separator, Line 
 - [`Zp] : Separator, Paragraph 
 - [`Cc] : Other, Control 
 - [`Cf] : Other, Format 
 - [`Cs] : Other, Surrogate 
 - [`Co] : Other, Private Use 
 - [`Cn] : Other, Not Assigned 
 - [`Lm] : Letter, Modifier 
 - [`Lo] : Letter, Other 
 - [`Pc] : Punctuation, Connector 
 - [`Pd] : Punctuation, Dash 
 - [`Ps] : Punctuation, Open 
 - [`Pe] : Punctuation, Close 
 - [`Pi] : Punctuation, Initial
 - [`Pf] : Punctuation, Final
 - [`Po] : Punctuation, Other 
 - [`Sm] : Symbol, Math 
 - [`Sc] : Symbol, Currency 
 - [`Sk] : Symbol, Modifier 
 - [`So] : Symbol, Other  *)
type general_category_type = 
  [ `Lu		(** Letter, Uppercase *)
  | `Ll		(** Letter, Lowercase *)
  | `Lt		(** Letter, Titlecase *)
  | `Mn		(** Mark, Non-Spacing *)
  | `Mc		(** Mark, Spacing Combining *)
  | `Me		(** Mark, Enclosing *)
  | `Nd		(** Number, Decimal Digit *)
  | `Nl		(** Number, Letter *)
  | `No		(** Number, Other *)
  | `Zs		(** Separator, Space *)
  | `Zl		(** Separator, Line *)
  | `Zp		(** Separator, Paragraph *)
  | `Cc		(** Other, Control *)
  | `Cf		(** Other, Format *)
  | `Cs		(** Other, Surrogate *)
  | `Co		(** Other, Private Use *)
  | `Cn		(** Other, Not Assigned *)
  | `Lm		(** Letter, Modifier *)
  | `Lo		(** Letter, Other *)
  | `Pc		(** Punctuation, Connector *)
  | `Pd		(** Punctuation, Dash *)
  | `Ps		(** Punctuation, Open *)
  | `Pe		(** Punctuation, Close *)
  | `Pi		(** Punctuation, Initial quote  *)
  | `Pf		(** Punctuation, Final quote  *)
  | `Po		(** Punctuation, Other *)
  | `Sm		(** Symbol, Math *)
  | `Sc		(** Symbol, Currency *)
  | `Sk		(** Symbol, Modifier *)
  | `So	        (** Symbol, Other *) ]

val general_category : UChar.t -> general_category_type
val load_general_category_map : unit -> general_category_type UMap.t

(** Type of character properties *)
type character_property_type = [

(**Derived Core Properties*)

    `Math				
  | `Alphabetic
  | `Lowercase
  | `Uppercase
  | `ID_Start
  | `ID_Continue
  | `XID_Start
  | `XID_Continue
  | `Default_Ignorable_Code_Point
  | `Grapheme_Extend
  | `Grapheme_Base

(**Extended Properties*)

  | `Bidi_Control			
  | `White_Space
  | `Hyphen
  | `Quotation_Mark
  | `Terminal_Punctuation
  | `Other_Math
  | `Hex_Digit
  | `Ascii_Hex_Digit
  | `Other_Alphabetic
  | `Ideographic
  | `Diacritic
  | `Extender
  | `Other_Lowercase
  | `Other_Uppercase
  | `Noncharacter_Code_Point
  | `Other_Grapheme_Extend
  | `Grapheme_Link
  | `IDS_Binary_Operator
  | `IDS_Trinary_Operator
  | `Radical
  | `Unified_Ideograph
  | `Other_default_Ignorable_Code_Point
  | `Deprecated
  | `Soft_Dotted
  | `Logical_Order_Exception ]

(** Load the table for the given character type. *)
val load_property_tbl : character_property_type -> UCharTbl.Bool.t

(** Load the table for the given name of the character type.
   The name can be obtained by removing ` from its name of 
   the polymorphic variant tag. *)
val load_property_tbl_by_name : string -> UCharTbl.Bool.t

(** Load the set of characters of the given character type. *)
val load_property_set : character_property_type -> USet.t

(** Load the set of characters of the given name of the character type.
   The name can be obtained by removing ` from its name of 
   the polymorphic variant tag. *)
val load_property_set_by_name : string -> USet.t

(** Type for script type *)
type script_type =
  [ `Common
  | `Inherited
  | `Latin
  | `Greek
  | `Cyrillic
  | `Armenian
  | `Hebrew
  | `Arabic
  | `Syriac
  | `Thaana
  | `Devanagari
  | `Bengali
  | `Gurmukhi
  | `Gujarati
  | `Oriya
  | `Tamil
  | `Telugu
  | `Kannada
  | `Malayalam
  | `Sinhala
  | `Thai
  | `Lao
  | `Tibetan
  | `Myanmar
  | `Georgian
  | `Hangul
  | `Ethiopic
  | `Cherokee
  | `Canadian_Aboriginal
  | `Ogham
  | `Runic
  | `Khmer
  | `Mongolian
  | `Hiragana
  | `Katakana
  | `Bopomofo
  | `Han
  | `Yi
  | `Old_Italic
  | `Gothic
  | `Deseret
  | `Tagalog
  | `Hanunoo
  | `Buhid
  | `Tagbanwa ]

val script : UChar.t -> script_type
val load_script_map : unit -> script_type UMap.t

(** age *)
type version_type =
  [ `Nc		(** undefined code point *)
  | `v1_0
  | `v1_1
  | `v2_0
  | `v2_1
  | `v3_0
  | `v3_1
  | `v3_2 ]

(** [age c] unicode version in wich [c] was introduced *)
val age : UChar.t -> version_type
(** [older v1 v2] is [true] if [v1] is older ( or the same version )
    than [v2]. Everithing is older than [`Nc] *)
val older : version_type -> version_type -> bool

(** casing *)

val load_to_lower1_tbl : unit -> UChar.t UCharTbl.t
val load_to_upper1_tbl : unit -> UChar.t UCharTbl.t
val load_to_title1_tbl : unit -> UChar.t UCharTbl.t

type casemap_condition =
  [ `Locale of string
  | `FinalSigma
  | `AfterSoftDotted
  | `MoreAbove
  | `BeforeDot
  | `Not of casemap_condition ]

type special_casing_property =
  {lower : UChar.t list;
  title : UChar.t list;
  upper : UChar.t list;
  condition : casemap_condition list;} 

val load_conditional_casing_tbl : 
    unit -> special_casing_property list UCharTbl.t

val load_casefolding_tbl : unit -> UChar.t list UCharTbl.t

(** Combined class
   A combined class is an integer of 0 -- 255, showing how this character
   interacts to other combined characters.  *)
val combined_class : UChar.t -> int

(** Decomposition *)

(** Types of decomposition. *)
type decomposition_type =
    [ `Canon | `Font | `NoBreak | `Initial | `Medial | `Final |
    `Isolated | `Circle | `Super | `Sub | `Vertical | `Wide | `Narrow |
    `Small | `Square | `Fraction | `Compat ]

type decomposition_info =
(** Already in the canonical form *)
    [ `Canonform
(** Hangul is treated algotighmically.*)
  | `HangulSyllable
(** [`Composite (dtype, text)]
   means the given character is decomposed into text by dtype
   decomposition. *)
  | `Composite of decomposition_type * UChar.t list ]

val load_decomposition_tbl : unit -> decomposition_info UCharTbl.t

(** Canonical Composition *)

(** The return value [[(u_1, u'_1); ... (u_n, u'_1)]] means
   for the given character [u], [u u_i] forms 
   the canonical composition [u'_i].
   If u is a Hangul jamo, composition returns []. *)
val load_composition_tbl : unit -> (UChar.t * UChar.t) list UCharTbl.t

(** Whether the given composed character is used in NFC or NFKC *)
val load_composition_exclusion_tbl : unit -> UCharTbl.Bool.t

end

module Make (Config : ConfigInt.Type) : Type
  
# 117 "camomileLibrary.mlip"
  end

  module UNF : sig
# 1 "public/uNF.mli"
(** Unicode normal form (NFD, NFKD, NFC, NFKC) as described in UTR #15 *)

(* Copyright (C) 2002 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

module type Type =
sig
  type text

  open OOChannel
  
  class nfd : UChar.t #obj_output_channel -> [UChar.t] obj_output_channel
  class nfc : UChar.t #obj_output_channel -> [UChar.t] obj_output_channel
  class nfkd : UChar.t #obj_output_channel -> [UChar.t] obj_output_channel
  class nfkc : UChar.t #obj_output_channel -> [UChar.t] obj_output_channel

(** Conversion to NFD, NFKD, NFC, NFKC forms. *)

  val nfd : text -> text
  val nfkd : text -> text
  val nfc : text -> text
  val nfkc : text -> text

  module NFCBuf :  sig
    type buf
    val create : int -> buf

    val contents : buf -> text
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> text -> unit
    val add_buffer : buf -> buf -> unit
  end

  val nfc_append : text -> text -> text

(** [put_nfd b t], [put_nfkd b t], [put_nfc b t], [put_nfkc b t]
   clear the contents of [b] and put the NFD, NFKD, NFC, NFKC 
   forms of [t] into [b] respectively. *)

  val put_nfd : XString.t -> text -> unit
  val put_nfkd : XString.t -> text -> unit
  val put_nfc : XString.t -> text -> unit
  val put_nfkc : XString.t -> text -> unit

  type index

  val nfd_inc : 
      text -> index -> 
	([`Inc of UChar.t list * index * 'a lazy_t ] as 'a)

  val canon_compare : text -> text -> int

  val nfd_decompose : UChar.t -> UChar.t list
  val nfkd_decompose : UChar.t -> UChar.t list

end

module Make  (Config : ConfigInt.Type) (Text : UnicodeString.Type) :
  Type with type text = Text.t and type index = Text.index
  
# 121 "camomileLibrary.mlip"
  end

  module UCol : sig
# 1 "public/uCol.mli"
(** Unicode collation algorithm *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** String comparison by collation as described in UTR #10 *)

(** How variables are handled *)
    type variable_option = 
	[ `Blanked 
      | `Non_ignorable 
      | `Shifted
      | `Shift_Trimmed ]
	  
(** Strength of comparison.  For European languages, each strength
    roughly means as
    `Primary : Ignore accents and case
    `Secondary : Ignore case but accents are counted in.
    `Tertiary : Accents and case are counted in.
    For the case of `Shifted, `Shift_Trimmed, there is the fourth strength.
    `Quaternary : Variables such as - (hyphen) are counted in. *)
    type precision = [ `Primary | `Secondary | `Tertiary | `Quaternary ]


module type Type =
  sig


    type text
    type index

	  (** For locale, see {!Locale}.
	      If [locale] is omitted, the standard UCA order is used.
	      If [prec] is omitted, the maximum possible strength is used.
	      If [variable] is omitted, the default of the locale 
	      (usually [`Shifted]) is used.
	      The meaning of the returned value is similar to Pervasives.compare *)
    val compare : 
	?locale:string -> ?prec:precision -> ?variable:variable_option -> 
	  text -> text -> int

	      (** Binary comparison of sort_key gives the same result as [compare]. 
		  i.e.
		  [compare t1 t2 = Pervasives.compare (sort_key t1) (sort_key t2)]
		  If the same texts are repeatedly compared, 
		  pre-computation of sort_key gives better performance. *)
    val sort_key : 
	?locale:string -> ?prec:precision -> ?variable:variable_option ->
	  text -> string

(** Comparison with the sort key. *)
    val compare_with_key :
	?locale: string -> ?prec:precision -> ?variable:variable_option ->
	  string -> text -> int

    val search_with_key :
	?locale: string -> ?prec:precision -> ?variable:variable_option ->
	  string -> text -> index -> (index * index)

    val search :
	?locale: string -> ?prec:precision -> ?variable:variable_option ->
	  text -> text -> index -> (index * index)

  end

module Make (Config : ConfigInt.Type) (Text : UnicodeString.Type) : (Type with type text = Text.t and type index = Text.index)
  
# 125 "camomileLibrary.mlip"
  end

  module CaseMap : sig
# 1 "public/caseMap.mli"
(* Copyright (C) 2002, 2003, 2004 Yamagata Yoriyuki *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)


(** Case mappings as defined in Unicode Technical Report #21 *)

(** For locale, see {!Locale}.
   If locale is omitted, default mapping is used. *)

module type Type =
  sig
    type text

    val lowercase : ?locale:string -> text -> text
    val uppercase : ?locale:string -> text -> text

    (** Capitalize the beginning of words *)
    val titlecase : ?locale:string -> text -> text

    (** Case foldding *)
    val casefolding : text -> text

    (** Caseless comparison *)
    val compare_caseless : text -> text -> int
  end

module Make (Config : ConfigInt.Type) (Text : UnicodeString.Type) :  (Type with type text = Text.t)
  
# 129 "camomileLibrary.mlip"
  end

  module UReStr : sig
# 1 "public/uReStr.mli"
(* Copyright (C) 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Module for a Str-like regular expression syntax.
   The difference can be summarised as follows.
   - Non-ASCII characters can be used if encoded by UTF-8, or
   using the escape syntax \u<code number as hex digits>.
   - Each Unicode character is treated as a single character.
   - Character properties like Lu ({!UCharInfo.general_category_type}),
   White_Space ({!UCharInfo.character_property_type}),
   Ogham ({!UCharInfo.script_type}) can be used in character sets. e.g.
   \[\{Lu & ID_Start\}\]\[\{ID_Continue\}\]* (capitalised identifier),
   \(\[\{Han\}\]+\|\[\{Katakana\}\]+\)\[\{Hiragana\}\]* 
   (Japanese word component).
   Boolean notations as | (or) :, & (and) - (set subtraction) can be used
   in \{...\} notations.  Any is used to denote the set of all characters
   in \{...\} notations.

*)

module type Interface = sig

type regexp = URe.regexp

(** Theses functions are similar to Str. *)

val regexp : string -> regexp
val quote : string -> string
val regexp_string : string -> regexp

module type Type = sig 
  type text
  type index
  type compiled_regexp

  module SubText : 
    SubText.Type with type ur_text = text and type ur_index = index

(** Compile regular expressions. *)
  val compile : regexp -> compiled_regexp

(** [regexp_match ?sem r t i] tries matching [r] and substrings
   of [t] beginning from [i].  If match successes,  [Some g] is 
   returned where [g] is the array containing the matched 
   string of [n]-th group in the [n]-element.  
   The matched string of the whole [r] is stored in the [0]-th element.  
   If matching fails, [None] is returned. *)
  val regexp_match : ?sem:URe.match_semantics ->
    compiled_regexp -> text -> index -> SubText.t option array option

(** [string_match r t i] tests whether [r] can match a substring
   of [t] beginning from [i]. *)
  val string_match : compiled_regexp -> text -> index -> bool

(** [search_forward ?sem r t i] searches a substring of [t]
   matching [r] from [i].  The returned value is similar to 
   {!URe.Type.regexp_match}. *)
  val search_forward : ?sem:URe.match_semantics ->
      compiled_regexp -> text -> index -> SubText.t option array option
end

module Make (Text : UnicodeString.Type) : 
    Type with type text = Text.t and type index = Text.index
end

module Configure (Config : ConfigInt.Type) : Interface
  
# 133 "camomileLibrary.mlip"
  end

  module StringPrep : sig
# 1 "public/stringPrep.mli"
(* Copyright (C) 2010 Pierre Chambart *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

module type Type =
sig
  type text

  exception Prohibited of UChar.t
  exception Bad_bidi

  type profile =
    [ `Nameprep (** RFC 3491 *)
    | `Nodeprep (** RFC 3920, Appendix A *)
    | `Resourceprep (** RFC 3920, Appendix B *)
    | `Saslprep (** RFC 4013 *)
    | `Trace (** for SASL Anonymous, RFC 4505, Section 3 *)
    | `Iscsi (** RFC 3722 *)
    | `Mib (** RFC 4011 *) ]

  val stringprep : profile -> text -> text

end

module Make (Config : ConfigInt.Type) (Text : UnicodeString.Type) :
  Type with type text = Text.t

  
# 137 "camomileLibrary.mlip"
  end

module type Type = sig

  module OOChannel : sig
# 1 "public/oOChannel.mli"
(** Object Oriented Channel *)
(* Copyright (C) 2002, 2003, 2010 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Generic input channel
  Have the same interface of Polymorphic input channel of
  http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm 
  the behaviour defined in the recommendation above.
*)
class type ['a] obj_input_channel = 
  object 
    method close_in : unit -> unit
    method get : unit -> 'a 
  end

(** Generic output channel
  Have the same interface of Polymorphic output channel of
  http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm 
  the behaviour defined in the recommendation above.
*)
class type ['a] obj_output_channel = 
  object
    (** If close_oout cannot output all buffered objects, flush raises
      Failure *)
    method close_out : unit -> unit
    (** If flush cannot output all buffered objects, flush raises
      Failure *)
    method flush : unit -> unit
    method put : 'a -> unit
  end

(** Convert stream to obj_input_channel *)
class ['a] channel_of_stream : 'a Stream.t -> ['a] obj_input_channel

(** Convert obj_input_channel to stream *)
val stream_of_channel : 'a #obj_input_channel -> 'a Stream.t

(** Character(byte) input channel.  Have the same interface of octet
  input channel of http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm the
  behaviour defined in the recommendation above.  In addition, all
  channels are assumed to be blocking.  If you supply a non-blocking
  channel to Camomile API, the outcome is undefined.
*)
class type char_input_channel =
  object
    method input : string -> int -> int -> int
    method close_in : unit -> unit
  end

(** Character(byte) output channel.  Have the same interface of octet
  input channel of http://www.ocaml-programming.de/rec/IO-Classes.html
  All channels of Camomile having this interface must confirm the
  behaviour defined in the recommendation above.  In addition, all
  channels are assumed to be blocking.  If you supply a non-blocking
  channel to Camomile API, the outcome is undefined.
*)
class type char_output_channel =
  object
    method output : string -> int -> int -> int
    method flush : unit -> unit
    method close_out : unit -> unit
  end

(** Convert a polymorphic input channel to a character input channel *)
class char_input_channel_of : char #obj_input_channel ->
  char_input_channel

(** Convert a character input channel to a polymorphic input channel*)
class char_obj_input_channel_of : char_input_channel -> 
  [char] obj_input_channel

(** Convert a polymorphic output channel to a character output channel *)
class char_output_channel_of : char #obj_output_channel -> char_output_channel

(** Convert a character output channel to a polymorphic output channel *)
class char_obj_output_channel_of : char_output_channel -> 
  [char] obj_output_channel

(** Convert an OCaml input channel to an OO-based character input channel *)
class of_in_channel : Pervasives.in_channel -> char_input_channel

(** Convert an OCaml output channel to an OO-based character output channel *)
class of_out_channel : Pervasives.out_channel -> char_output_channel
    
# 143 "camomileLibrary.mlip"
    end

  module UChar : sig
# 1 "public/uChar.mli"
(** Unicode (ISO-UCS) characters.

   This module implements Unicode (actually ISO-UCS) characters.  All
   31-bit code points are allowed.
*)

(* Copyright (C) 2002, 2003, 2004 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Unicode characters. All 31bit code points are allowed.*) 
type t

exception Out_of_range

(** [char_of u] returns the Latin-1 representation of [u].
   If [u] can not be represented by Latin-1, raises Out_of_range *)
val char_of : t -> char

(** [of_char c] returns the Unicode character of the Latin-1 character [c] *)
val of_char : char -> t

(** [code u] returns the Unicode code number of [u].
   If the value can not be represented by a positive integer,
   raise Out_of_range *)
val code : t -> int

(** [code n] returns the Unicode character with the code number [n]. 
   If n >= 2^32 or n < 0, raises [invalid_arg] *)
val chr : int -> t

(** [uint_code u] returns the Unicode code number of [u].
   The returned int is unsigned, that is, on 32-bits platforms,
   the sign bit is used for storing the 31-th bit of the code number. *)
external uint_code : t -> int = "%identity"

(** [chr_of_uint n] returns the Unicode character of the code number [n].
   [n] is interpreted as unsigned, that is, on 32-bits platforms,
   the sign bit is treated as the 31-th bit of the code number.
   If n exceed 31-bits values, then raise [invalid_arg]. *)
val chr_of_uint : int -> t

(** Equality by code point comparison *)
val eq : t -> t -> bool

(** [compare u1 u2] returns, 
   a value > 0 if [u1] has a larger Unicode code number than [u2], 
   0 if [u1] and [u2] are the same Unicode character,
   a value < 0 if [u1] has a smaller Unicode code number than [u2]. *)
val compare : t -> t -> int

(** Aliases of [type t] *)
type uchar = t

(** Alias of [uint_code] *)
val int_of : uchar -> int

(** Alias of [chr_of_uint] *)
val of_int : int -> uchar
    
# 147 "camomileLibrary.mlip"
    end

  module USet : sig
# 1 "public/uSet.mli"
(** Sets of Unicode characters, implemented as sets of intervals.
   The signature is mostly same to Set.S in stdlib *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

type t
val empty : t
val is_empty : t -> bool
val mem : UChar.t -> t -> bool
val add : UChar.t -> t -> t

(** [add_range u1 u2 s] adds the characters in the range [u1] - [u2]
   to [s].  The range is determined by the code point order. *)
val add_range : UChar.t -> UChar.t -> t -> t

val singleton : UChar.t -> t
val remove : UChar.t -> t -> t

(** [remove_range u1 u2 s] removes the characters in the range [u1] - [u2]
   from [s].  The range is determined by the code point order. *)
val remove_range : UChar.t -> UChar.t -> t -> t

val union : t -> t -> t
val inter : t -> t -> t
val diff : t -> t -> t

(** [compl s] returns the compliment of [s]. *)
val compl : t -> t

val compare : t -> t -> int
val equal : t -> t -> bool
val subset : t -> t -> bool

(** [from u s] returns the set of elements of [s] 
   whose code points are equal or greater than [u]. *)
val from : UChar.t -> t -> t

(** [after u s] returns the set of elements of [s] 
   whose code points are greater than [u]. *)
val after : UChar.t -> t -> t

(** [until u s] returns the set of elements of [s] 
   whose code points are equal or smaller than [u]. *)
val until : UChar.t -> t -> t

(** [until u s] returns the set of elements of [s] 
   whose code points are smaller than [u]. *)
val before : UChar.t -> t -> t

val iter : (UChar.t -> unit) -> t -> unit

(** [iter_range proc s] feeds the intervals contained in [s] to
   [proc] in increasing order.  The intervals given to [proc]
   are always separated by the character not in [s]. *)
val iter_range : (UChar.t -> UChar.t -> unit) -> t -> unit

val fold : (UChar.t -> 'a -> 'a) -> t -> 'a -> 'a

(** [fold_range f s x] is equivalent to 
   [f u_i u_(i+1) (... (f u_3 u_4 (f u_1 u_2 x)))] if [s] is consisted of
   the intervals [u1]-[u2], [u3]-[u4], ..., [u_i]-[u_(i + 1)]
   in increasing order.  The intervals given to [proc]
   are always separated by the character not in [s]. *)
val fold_range : (UChar.t -> UChar.t -> 'a -> 'a) -> t -> 'a -> 'a

val for_all : (UChar.t -> bool) -> t -> bool
val exists : (UChar.t -> bool) -> t -> bool
val filter : (UChar.t -> bool) -> t -> t
val partition : (UChar.t -> bool) -> t -> t * t
val cardinal : t -> int
val elements : t -> UChar.t list

(** The list of the intervals contained in the set.  
   The returned intervals are always separated 
   by the character not in [s]. *)
val ranges : t -> (UChar.t * UChar.t) list

val min_elt : t -> UChar.t
val max_elt : t -> UChar.t

(** Returns a element roughly in the middle of the set. 
   It is not guaranteed to return the same element for 
   the sets with the same elements *)
val choose : t -> UChar.t

val uset_of_iset : ISet.t -> t
val iset_of_uset : t -> ISet.t
    
# 151 "camomileLibrary.mlip"
    end

  module UMap : sig
# 1 "public/uMap.mli"
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Maps over Unicode characters. *) 
type 'a t
val empty : 'a t
val is_empty : 'a t -> bool

(** [add ?eq u v m] returns the new map which is same to [m] 
   except it maps [u] to some value [v'] which satisfies [eq v v']. 
   If [eq] is not supplied, structural equality is used. *)
val add : ?eq:('a -> 'a -> bool) -> UChar.t -> 'a -> 'a t -> 'a t

(** [add ?eq u1 u2 v m] returns the new map which is same to [m] 
   except it maps characters in the range [u1]-[u2] 
   to some value [v'] which satisfies [eq v v']. 
   If [eq] is not supplied, structural equality is used. *)
val add_range : ?eq:('a -> 'a -> bool) -> 
  UChar.t -> UChar.t -> 'a -> 'a t -> 'a t

val find : UChar.t -> 'a t -> 'a
val remove : UChar.t -> 'a t -> 'a t

(** [remove_range u1 u2 m] removes [u1]-[u2] from the domain of [m] *)
val remove_range : UChar.t -> UChar.t -> 'a t -> 'a t

(** [from u m] restricts the domain of [m] to the characters whose
   code points are equal or greater than [u]. *)
val from : UChar.t -> 'a t -> 'a t

(** [after u m] restricts the domain of [m] to the characters whose
   code points are greater than [u]. *)
val after : UChar.t -> 'a t -> 'a t

(** [until u m] restricts the domain of [m] to the characters whose
   code points are equal or smaller than [u]. *)
val until : UChar.t -> 'a t -> 'a t

(** [before u m] restricts the domain of [m] to the characters whose
   code points are smaller than [u]. *)
val before : UChar.t -> 'a t -> 'a t

val mem : UChar.t -> 'a t -> bool
val iter : (UChar.t -> 'a -> unit) -> 'a t -> unit

(** [iter proc m] : For each contingent region [u1]-[u2] 
   that is mapped to a constant [v], [proc u1 u2 v] is called.
   The order of call is determined by increasing order on [u1]. *)
val iter_range : (UChar.t -> UChar.t -> 'a -> unit) -> 'a t -> unit

(** [map ?eq f m] and [mapi ?eq f m] :  Similar to [map] and [mapi] 
   in stdlib Map, but if the map [m'] is returned,  it is only guaranteed 
   that [eq (find u m') (f (find u m ))] is true for [map] and 
   [eq (find u m') (f u (find u m ))] is true for [mapi].  If [eq] is
   not specified, structural equality is used. *)

val map : ?eq:('b -> 'b -> bool) -> ('a -> 'b) -> 'a t -> 'b t
val mapi : ?eq:('b -> 'b -> bool) -> (UChar.t -> 'a -> 'b) -> 'a t -> 'b t

val fold : (UChar.t -> 'b -> 'a -> 'a) -> 'b t -> 'a -> 'a

(** [fold_range f m x] is equivalent to
   [f u_(2n) u_(2n+1) v_n (... (f u_1 u_2 v_1 x))] where all characters in
   the range [u_(2k)]-[u_(2k+1)] are mapped to [v_k] and 
   [u_1] < [u_3] < ... in code point order.  
   For each range [u_(2k)]-[u_(2k+1)] is separated by a character 
   which is not mapped to [v_k]. *)
val fold_range : (UChar.t -> UChar.t -> 'b -> 'a -> 'a) -> 'b t -> 'a -> 'a

(** Constant map.*)
val set_to_map : USet.t -> 'a -> 'a t

(** Domain. *)
val domain : 'a t -> USet.t

(** [map_to_set p m] returns the set of characters which are mapped
   to values satisfying the predicate [p] by [m]. *)
val map_to_set : ('a -> bool) -> 'a t -> USet.t

val umap_of_imap : 'a IMap.t -> 'a t
val imap_of_umap : 'a t -> 'a IMap.t
    
# 155 "camomileLibrary.mlip"
    end

  module UCharTbl : sig
# 1 "public/uCharTbl.mli"
(** Fast lookup tables for Unicode.  Accessible by constant time. *)
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)


(** Fast lookup tables.  Accessible by constant time. *)
  type 'a tbl
  type 'a t = 'a tbl

  val get : 'a tbl -> UChar.t -> 'a

  module type Type = sig
    type elt
    type t = elt tbl
    val get : elt tbl -> UChar.t -> elt

(** [of_map def m] creates the table which has the same value to [m].
   The table returns [def] for the characters for which [m] is undefined. *)
    val of_map : elt -> elt UMap.t -> t
  end

(** Equality and hash are necessary for table generation. *)
  module Make : 
  functor (H : Hashtbl.HashedType) ->  (Type with type elt = H.t)

(** Tables for boolean values. *)
  module Bool : sig
    type t
    val get : t -> UChar.t -> bool
    val of_set : USet.t -> t
  end

(** Tables for small (< 256, >=0) integers *)
  module Bits : sig
    type t
    val of_map : int -> int UMap.t -> t
    val get : t -> UChar.t -> int
  end

(** Tables for integers.  If integers are not span the whole 31-bit or
63-bit values, [Bytes.t] is more space efficient than [int tbl]. *)
  module Bytes : sig
    type t
    val of_map : int -> int UMap.t -> t
    val get : t -> UChar.t -> int
  end

(** Tables for bytes. *)
  module Char : sig
    type t
    val of_map : char -> char UMap.t -> t
    val get : t -> UChar.t -> char
  end
    
# 159 "camomileLibrary.mlip"
    end

  module UnicodeString : sig
# 1 "public/unicodeString.mli"
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Signature for Unicode strings.  
   {!UText}, {!XString}, {!UTF8}, {!UTF16}, {!UCS4}
   have matched signatures to UStorage
   and satisfy the semantics described below.  If users want to supply
   their own Unicode strings, please design the module with the 
   following signature and properties. *)

module type Type = sig
(** The type of string. *)
  type t

(** [get t i] : [i]-th character of the storage.*)
  val get : t -> int -> UChar.t

(** [init len f] creates a new storage.
   the returned storage has length [len], its nth-element is [f n].
   [f] is called with integers [0 ... len - 1], only once for each integer.
   The call is in the increasing order f 0, f 1, f 2, ... *)
  val init : int -> (int -> UChar.t) -> t

(** The number of Unicode characters in the storage *)
  val length : t -> int

(** locations in storages.*)
  type index

(** [look t i] : The character in the location [i] of [t].*)
  val look : t -> index -> UChar.t

(** [nth t n] : the location of the [n]-th character in [t].*)
  val nth : t -> int -> index

(** [next x i, prev x i] :
   The operation is valid if [i] points the valid element, i.e. the
   returned value may point the location beyond valid elements by one.
   If [i] does not point a valid element, the results are unspecified. *)

  val next : t -> index -> index
  val prev : t -> index -> index

(* [out_of_range t i] tests whether [i] is inside of [t]. *)
  val out_of_range : t -> index -> bool
      
  val iter : (UChar.t -> unit) -> t -> unit

(* Code point comparison *)
  val compare : t -> t -> int

(** The location of the first character in the storage. *)
  val first : t -> index

(** The location of the last character in the storage. *)
  val last : t -> index

(** [move t i n] :
   if [n] >= 0, then returns [n]-th character after [i] and
   otherwise returns -[n]-th character before [i].
   If there is no such character, or [i] does not point 
   a valid character, the result is unspecified. *)
  val move : t -> index -> int -> index

(** [compare_index t i j] returns
   a positive integer if [i] is the location placed after [j] in [t],
   0 if [i] and [j] point the same location, and
   a negative integer if [i] is the location placed before [j] in [t]. *)
  val compare_index : t -> index -> index -> int

(** Character buffers.  Similar to Buffer. *)
  module Buf : sig
    type buf

(** [create n] creates the buffer.  [n] is used to determine
   the initial size of the buffer.  The meaning of [n] differs from
   modules to modules. *)
    val create : int -> buf

    val contents : buf -> t
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> t -> unit
    val add_buffer : buf -> buf -> unit
  end
end

    
# 163 "camomileLibrary.mlip"
    end

  module UText : sig
# 1 "public/uText.mli"
(** An implementation of Unicode string. *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** An implementation of Unicode string.  
   Internally, it uses integer array.
   The semantics matches the description of UStorage. *)
  
(** Phantom type for distinguishing mutability *)
  type mutability = [ `Mutable | `Immutable ]

  type 'a text
  type utext = [`Immutable] text
  type ustring = [`Mutable] text
  type t = utext

  val utext_of_ustring : ustring -> utext
  val ustring_of_utext : utext -> ustring
  val get :  'a text -> int -> UChar.t

(** [set s i u] sets the [i]-th character in [s] to [u]. *)
  val set :  ustring -> int -> UChar.t -> unit

  type index

  val look : 'a text -> index -> UChar.t
  val nth : 'a text -> int -> index
  val first : 'a text -> index
  val last : 'a text -> index
  val out_of_range : 'a text -> index -> bool
  val compare_index : 'a text -> index -> index -> int
  val next : 'a text -> index -> index
  val prev : 'a text -> index -> index
  val move : 'a text -> index -> int -> index

  val length : 'a text -> int

(** Conversion from Latin-1 strings. *)
  val of_string : string -> utext

  val init : int -> (int -> UChar.t) -> utext
  val init_ustring : int -> (int -> UChar.t) -> ustring

(** The semantics of these function are similar to 
   the equivalents of string. *)
  val make : int -> UChar.t -> ustring
  val copy : ustring -> ustring
  val sub : 'a text -> int -> int -> 'a text
  val fill : ustring -> int -> int -> UChar.t -> unit
  val blit : 'a text -> int -> ustring -> int -> int -> unit
  val append : 'a text -> 'b text -> 'a text
  val iter : (UChar.t -> unit) -> 'a text -> unit
  val compare : 'a text -> 'b text -> int

  module Buf : sig
    type buf

(** [create n] creates the buffer which initially can contain
   [n] Unicode characters. *)
    val create : int -> buf

    val contents : buf -> t
    val contents_string : buf -> ustring
    val length : buf -> int
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> 'a text -> unit
    val add_buffer : buf -> buf -> unit
  end
    
# 167 "camomileLibrary.mlip"
    end

  module XString : sig
# 1 "public/xString.mli"
(** eXtensible Unicode string.  
   The semantics matches the description of UStorage. 
   The detail may be going to change.*)

(* Copyright 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

  type xstring
  type t = xstring

  val get : xstring -> int -> UChar.t
  val set : xstring -> int -> UChar.t -> unit
  val length : xstring -> int
  val init : int -> (int -> UChar.t) -> xstring

  type index
  val look : xstring -> index -> UChar.t
  val nth : xstring -> int -> index
  val first : xstring -> index
  val last : xstring -> index
  val out_of_range : xstring -> index -> bool
  val next : xstring -> index -> index
  val prev : xstring -> index -> index
  val move : xstring -> index -> int -> index
  val compare_index : xstring -> index -> index -> int

  val make : ?bufsize:int -> int -> UChar.t -> xstring
  val clear : xstring -> unit
  val reset : xstring -> unit
  val copy : xstring -> xstring
  val sub : xstring -> int -> int -> xstring
  val add_char : xstring -> UChar.t -> unit
  val add_text : xstring -> 'a UText.text -> unit
  val add_xstring : xstring -> xstring -> unit
  val shrink : xstring -> int -> unit
  val append : xstring -> xstring -> xstring
  val utext_of : xstring -> UText.t
  val ustring_of : xstring -> UText.ustring
      
  val iter : (UChar.t -> unit) -> xstring -> unit
  val compare : t -> t -> int

  module Buf : sig
    type buf
    val create : int -> buf
    val contents : buf -> t
    val length : buf -> int
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> t -> unit
    val add_buffer : buf -> buf -> unit
  end
    
# 171 "camomileLibrary.mlip"
    end

  module SubText : sig
# 1 "public/subText.mli"
(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Sub-texts, parts of original (ur-) texts.  
   The signature and semantics matches those of UStorage. *)
module type Type = sig
  type t

  val get : t -> int -> UChar.t

  val init : int -> (int -> UChar.t) -> t
  val length : t -> int

  type index
  val look : t -> index -> UChar.t
  val nth : t -> int -> index
  val first : t -> index
  val last : t -> index

  val next : t -> index -> index
  val prev : t -> index -> index
  val move : t -> index -> int -> index
  val out_of_range : t -> index -> bool
  val compare_index : t -> index -> index -> int
      
  val iter : (UChar.t -> unit) -> t -> unit
  val compare : t -> t -> int

  module Buf : sig
    type buf
    val create : int -> buf
    val contents : buf -> t
    val clear : buf -> unit
    val reset : buf -> unit
    val add_char : buf -> UChar.t -> unit
    val add_string : buf -> t -> unit
    val add_buffer : buf -> buf -> unit
  end      

(** The type of original texts. *)
  type ur_text

(** The type of indexes of original texts. *)
  type ur_index

(** [refer t i j] returns the part of [t] from [i] until [j].
   The character pointed by [j] is not included in the result.
   If [j] is equal to [i] or located before [j], the result is
   an empty string. *)
  val refer : ur_text -> ur_index -> ur_index -> t

(** [excerpt t] copies the contents of [t] as a new ur_text. *)
  val excerpt : t -> ur_text

(** [context t] returns the tuple [(s, i, j)] such that
   [t = refer s i j]. *)
  val context : t -> ur_text * ur_index * ur_index

(** Conversion from indexes of sub-texts to ur_texts. *)
  val ur_index_of : t -> index -> ur_index
end

module Make : functor (Text : UnicodeString.Type) -> 
  (Type with type ur_text = Text.t and type ur_index = Text.index)
    
# 175 "camomileLibrary.mlip"
    end

  module ULine : sig
# 1 "public/uLine.mli"
(** Line IO *) 
(* Copyright (C) 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Line I/O, conversion of line separators. *)
open OOChannel

(** Line separators.  
   - [`CR] specifies carriage return.
   - [`LF] specifies linefeed.
   - [`CRLF] specifies the sequence of carriage return and linefeed.
   - [`NEL] specifies next line (\u0085).
   - [`LS] specifies Unicode line separator (\u2028).
   - [`PS] specifies Unicode paragraph separator (\u2029). *)
type separator =
  [ `CR
  | `LF
  | `CRLF
  | `NEL
  | `LS
  | `PS ]

(** [new input separator input_obj] creates the new input channel object
   {!OOChannel.obj_input_channel} which reads from [input_obj] and
   converts line separators (all of CR, LF, CRLF, NEL, LS, PS) to
   [separator]. *)
class input : separator -> 
  UChar.t #obj_input_channel -> [UChar.t] obj_input_channel

(** [new output separator output_obj] creates the new output channel
   object {!OOChannel.obj_output_channel} which receives Unicode characters 
   and converts line separators (all of CR, LF, CRLF, NEL, LS, PS) to
   [separator]. *)
class output : separator ->
  UChar.t #obj_output_channel -> [UChar.t] obj_output_channel

module type Type = sig

  type text

(** [new input_line input_obj] creates the new input channel object
   {!OOChannel.obj_input_channel} which reads Unicode characters 
   from [input_obj] and output lines.  All of CR, LF, CRLF, NEL, LS, PS, 
   as well as FF (formfeed) are recognised as a line separator. *)
  class input_line : UChar.t #obj_input_channel -> [text] obj_input_channel

(** [new output_line ~sp output_obj] create the new output channel object
   {!OOChannel.obj_output_channel} which output each line to [output_obj]
   using [sp] as a line separator.  
   If [sp] is omitted, linefeed (LF) is used. *)
  class output_line : ?sp:separator ->
      UChar.t #obj_output_channel -> [text] obj_output_channel

end

module Make : functor (Text : UnicodeString.Type) ->
  (Type with type text = Text.t)
    
# 179 "camomileLibrary.mlip"
    end

  module Locale : sig
# 1 "public/locale.mli"
(* Copyright (C) 2003 Yamagata Yoriyuki *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Camomile has a locale system similar to Java.
   A locale is a string with a form as
   "<LANG>_<COUNTRY>_<MODIFIER>..." where <LANG> is 
   a 2-letter ISO 639 language code, <COUNTRY> is a 2-letter ISO 3166
   country code.  Some field may not present. *)

(** Type of locales. *)
type t = string

(** [read root suffix reader locale]
   reads locale information using [reader].  
   Locale data is supposed to reside in [root] directory with 
   the name [locale].[suffix].
   [reader] takes [in_channel] as an argument and read data from in_channel.
   If data is not found, then [reader] should raise Not_found.
   If the file is not found or [reader] raises Not_found, then 
   more generic locales are tried.
   For example, if fr_CA.[suffix] is not found, then [read] tries fr.[suffix].
   If fr.[suffix] is also not found, then the file [root].[suffix] is tried.
   Still the data is not found, then [Not_found] is raised. *)
val read : string -> string -> (in_channel -> 'a) -> string -> 'a

(** [contain loc1 loc2] :
   If [loc1] is contained in [loc2] then true otherwise false.
   For example, "fr" is contained in "fr_CA" while "en_CA" 
   does not contain "fr" *)
val contain : string -> string -> bool
    
# 183 "camomileLibrary.mlip"
    end

  module CharEncoding : CharEncoding.Interface

  module UTF8 : sig
# 1 "public/uTF8.mli"
(** UTF-8 encoded Unicode strings. The type is normal string. *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki.  *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)


(** UTF-8 encoded Unicode strings. The type is normal string. *)
type t = string

exception Malformed_code

(** [validate s]
   successes if s is valid UTF-8, otherwise raises Malformed_code.
   Other functions assume strings are valid UTF-8, so it is prudent
   to test their validity for strings from untrusted origins. *)
val validate : t -> unit

(* All functions below assume string are valid UTF-8.  If not,
 * the result is unspecified. *)

(** [get s n] returns [n]-th Unicode character of [s].
   The call requires O(n)-time. *)
val get : t -> int -> UChar.t

(** [init len f] 
   returns a new string which contains [len] Unicode characters.
   The i-th Unicode character is initialized by [f i] *)
val init : int -> (int -> UChar.t) -> t

(** [length s] returns the number of Unicode characters contained in s *)
val length : t -> int
    
(** Positions in the string represented by the number of bytes from the head.
   The location of the first character is [0] *)
type index = int

(** [nth s n] returns the position of the [n]-th Unicode character. 
   The call requires O(n)-time *)
val nth : t -> int -> index

(** The position of the head of the first Unicode character. *)
val first : t -> index

(** The position of the head of the last Unicode character. *)
val last : t -> index

(** [look s i]
   returns the Unicode character of the location [i] in the string [s]. *)
val look : t -> index -> UChar.t

(** [out_of_range s i]
   tests whether [i] is a position inside of [s]. *)
val out_of_range : t -> index -> bool

(** [compare_index s i1 i2] returns
   a value < 0 if [i1] is the position located before [i2], 
   0 if [i1] and [i2] points the same location,
   a value > 0 if [i1] is the position located after [i2]. *)
val compare_index : t -> index -> index -> int

(** [next s i]
   returns the position of the head of the Unicode character
   located immediately after [i]. 
   If [i] is inside of [s], the function always successes.
   If [i] is inside of [s] and there is no Unicode character after [i],
   the position outside [s] is returned.  
   If [i] is not inside of [s], the behaviour is unspecified. *)
val next : t -> index -> index

(** [prev s i]
   returns the position of the head of the Unicode character
   located immediately before [i]. 
   If [i] is inside of [s], the function always successes.
   If [i] is inside of [s] and there is no Unicode character before [i],
   the position outside [s] is returned.  
   If [i] is not inside of [s], the behaviour is unspecified. *)
val prev : t -> index -> index

(** [move s i n]
   returns [n]-th Unicode character after [i] if n >= 0,
   [n]-th Unicode character before [i] if n < 0.
   If there is no such character, the result is unspecified. *)
val move : t -> index -> int -> index
    
(** [iter f s]
   applies [f] to all Unicode characters in [s].  
   The order of application is same to the order 
   of the Unicode characters in [s]. *)
val iter : (UChar.t -> unit) -> t -> unit

(** Code point comparison by the lexicographic order.
   [compare s1 s2] returns
   a positive integer if [s1] > [s2],
   0 if [s1] = [s2],
   a negative integer if [s1] < [s2]. *)
val compare : t -> t -> int

(** Buffer module for UTF-8 strings *)
module Buf : sig
  (** Buffers for UTF-8 strings. *) 
  type buf

  (** [create n] creates the buffer with the initial size [n]-bytes. *)   
  val create : int -> buf

  (* The rest of functions is similar to the ones of Buffer in stdlib. *)
  (** [contents buf] returns the contents of the buffer. *)
  val contents : buf -> t

  (** Empty the buffer, 
     but retains the internal storage which was holding the contents *)
  val clear : buf -> unit

  (** Empty the buffer and de-allocate the internal storage. *)
  val reset : buf -> unit

  (** Add one Unicode character to the buffer. *)
  val add_char : buf -> UChar.t -> unit

  (** Add the UTF-8 string to the buffer. *)
  val add_string : buf -> t -> unit

  (** [add_buffer b1 b2] adds the contents of [b2] to [b1].
     The contents of [b2] is not changed. *)
  val add_buffer : buf -> buf -> unit
end with type buf = Buffer.t
    
# 189 "camomileLibrary.mlip"
    end

  module UTF16 : sig
# 1 "public/uTF16.mli"
(* Copyright (C) 2002, 2003, Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** UTF-16 encoded string. the type is the bigarray of 16-bit integers.
   The characters must be 21-bits code points, and not surrogate points,
   0xfffe, 0xffff.
   Bigarray.cma or Bigarray.cmxa must be linked when this module is used. *)
type t = 
    (int, Bigarray.int16_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

exception Malformed_code

(** [validate s]
   If [s] is valid UTF-16 then successes otherwise raises [Malformed_code].
   Other functions assume strings are valid UTF-16, so it is prudent
   to test their validity for strings from untrusted origins. *)
val validate : t -> unit

(** All functions below assume strings are valid UTF-16.  If not,
   the result is unspecified. *)

(** [get s n] returns [n]-th Unicode character of [s].
   The call requires O(n)-time. *)
val get : t -> int -> UChar.t

exception Out_of_range

(** [init len f]
   returns a new string which contains [len] Unicode characters.
   The i-th Unicode character is initialized by [f i] 
   if the character is not representable, raise [Out_of_range]. *)
val init : int -> (int -> UChar.t) -> t

(** [length s] returns the number of Unicode characters contained in s *)
val length : t -> int
    
(** Positions in the string represented by the number of 16-bit unit
   from the head.
   The location of the first character is [0] *)
type index = int

(** [nth s n] returns the position of the [n]-th Unicode character. 
   The call requires O(n)-time *)
val nth : t -> int -> index

(** [first s] : The position of the head of the last Unicode character. *)
val first : t -> index

(** [last s] : The position of the head of the last Unicode character. *)
val last : t -> index

(** [look s i ]
   returns the Unicode character of the location [i] in the string [s]. *)
val look : t -> index -> UChar.t

(** [out_of_range s i] tests whether [i] is inside of [s]. *)
val out_of_range : t -> index -> bool

(** [compare_aux s i1 i2] returns
 - If [i1] is the position located before [i2], a value < 0,
 - If [i1] and [i2] points the same location, 0,
 - If [i1] is the position located after [i2], a value > 0. 

*)
val compare_index : t -> index -> index -> int

(** [next s i]
   returns the position of the head of the Unicode character
   located immediately after [i]. 
 - If [i] is a valid position, the function always success.
 - If [i] is a valid position and there is no Unicode character after [i],
   the position outside [s] is returned.  
 - If [i] is not a valid position, the behaviour is undefined. 
 
*)
val next : t -> index -> index

(** [prev s i]
   returns the position of the head of the Unicode character
   located immediately before [i]. 
   - If [i] is a valid position, the function always success.
   - If [i] is a valid position and there is no Unicode character before [i],
   the position outside [s] is returned.  
   - If [i] is not a valid position, the behaviour is undefined. 

*)
val prev : t -> index -> index

(* [move s i n]
 - If n >= 0, returns [n]-th Unicode character after [i].
 - If n < 0, returns [-n]-th Unicode character before [i].
 0 If there is no such character, the result is unspecified.
 
*)
val move : t -> index -> int -> index
    
(** [iter f s]
   Apply [f] to all Unicode characters in [s].  
   The order of application is same to the order 
   in the Unicode characters in [s]. *)
val iter : (UChar.t -> unit) -> t -> unit

(** Code point comparison *)
val compare : t -> t -> int

(** Buffer module for UTF-16 *)
module Buf : sig
  type buf

  (** create n : creates the buffer with the initial size [n]. *)   
  val create : int -> buf

  (** The rest of functions is similar to the ones of Buffer in stdlib. *)

  val contents : buf -> t
  val clear : buf -> unit
  val reset : buf -> unit

  (** if the character is not representable, raise Out_of_range *)
  val add_char : buf -> UChar.t -> unit

  val add_string : buf -> t -> unit
  val add_buffer : buf -> buf -> unit
end
    
# 193 "camomileLibrary.mlip"
    end

  module UCS4 : sig
# 1 "public/uCS4.mli"
(** UCS4 encoded string. The type is the bigarray of 32-bit integers.
   Bigarray.cma or Bigarray.cmxa must be linked when this module is used. *)

(* Copyright (C) 2002, 2003, 2004 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

type t = 
    (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t

exception Malformed_code

(** [validate s]
   If [s] is valid UCS4 then successes otherwise raises [Malformed_code].
   Other functions assume strings are valid UCS4, so it is prudent
   to test their validity for strings from untrusted origins. *)
val validate : t -> unit

(** All functions below assume strings are valid UCS4.  If not,
   the result is unspecified. *)

(** [get s n] returns [n]-th Unicode character of [s]. *)
val get : t -> int -> UChar.t

(** [init len f]
   returns a new string which contains [len] Unicode characters.
   The i-th Unicode character is initialised by [f i] *)
val init : int -> (int -> UChar.t) -> t

(** [length s] returns the number of Unicode characters contained in [s] *)
val length : t -> int
    
(** Positions in the string represented by the number of characters
   from the head.
   The location of the first character is [0] *)
type index = int

(** [nth s n] returns the position of the [n]-th Unicode character. 
   The call requires O(n)-time *)
val nth : t -> int -> index

(** [first s] : The position of the head of the last Unicode character. *)
val first : t -> index

(** [last s] : The position of the head of the last Unicode character. *)
val last : t -> index

(** [look s i]
   returns the Unicode character of the location [i] in the string [s]. *)
val look : t -> index -> UChar.t

(** [out_of_range s i]
   tests whether [i] points the valid position of [s]. *)
val out_of_range : t -> index -> bool

(** [compare_aux s i1 i2] returns
   If [i1] is the position located before [i2], a value < 0,
   If [i1] and [i2] points the same location, 0,
   If [i1] is the position located after [i2], a value > 0. *)
val compare_index : t -> index -> index -> int

(** [next s i]
   returns the position of the head of the Unicode character
   located immediately after [i]. 
   If [i] is a valid position, the function always success.
   If [i] is a valid position and there is no Unicode character after [i],
   the position outside [s] is returned.  
   If [i] is not a valid position, the behaviour is undefined. *)
val next : t -> index -> index

(** [prev s i]
   returns the position of the head of the Unicode character
   located immediately before [i]. 
   If [i] is a valid position, the function always success.
   If [i] is a valid position and there is no Unicode character before [i],
   the position outside [s] is returned.  
   If [i] is not a valid position, the behaviour is undefined. *)
val prev : t -> index -> index

(** [move s i n] :
   If n >= 0, returns [n]-th Unicode character after [i].
   If n < 0, returns [-n]-th Unicode character before [i].
   If there is no such character, the result is unspecified. *)
val move : t -> index -> int -> index
    
(** [iter f s] :
   Apply [f] to all Unicode characters in [s].  
   The order of application is same to the order 
   in the Unicode characters in [s]. *)
val iter : (UChar.t -> unit) -> t -> unit

(** Code point comparison *)
val compare : t -> t -> int

(** Buffer module for UCS4 *)
module Buf : sig
  type buf
  (** [create n] creates the buffer with the initial size [n]. *)   
  val create : int -> buf

  (** The rest of functions is similar to the ones of Buffer in stdlib. *)

  val contents : buf -> t
  val clear : buf -> unit
  val reset : buf -> unit

  val add_char : buf -> UChar.t -> unit

  val add_string : buf -> t -> unit
  val add_buffer : buf -> buf -> unit
end
    
# 197 "camomileLibrary.mlip"
    end

  module UPervasives : sig
# 1 "public/uPervasives.mli"
(** Functions for toplevel *)

(* Copyright (C) 2002, 2003 Yamagata Yoriyuki. *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

type uchar = UChar.t

(** Aliases for UChar.uint_code, UChar.chr_of_uint *)

val int_of_uchar : uchar -> int
val uchar_of_int : int -> uchar

val escaped_uchar : uchar -> string
val escaped_utf8 : string -> string

val printer_utf8 : Format.formatter -> string -> unit
val printer_uchar : Format.formatter -> uchar -> unit
    
# 201 "camomileLibrary.mlip"
    end

  module URe : sig
# 1 "public/uRe.mli"
(** Regular expression engine. *)

(* Copyright (C) 2003 Yamagata Yoriyuki. distributed with LGPL *)

(* This library is free software; you can redistribute it and/or *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2 of *)
(* the License, or (at your option) any later version. *)

(* As a special exception to the GNU Library General Public License, you *)
(* may link, statically or dynamically, a "work that uses this library" *)
(* with a publicly distributed version of this library to produce an *)
(* executable file containing portions of this library, and distribute *)
(* that executable file under terms of your choice, without any of the *)
(* additional requirements listed in clause 6 of the GNU Library General *)
(* Public License. By "a publicly distributed version of this library", *)
(* we mean either the unmodified Library as distributed by the authors, *)
(* or a modified version of this library that is distributed under the *)
(* conditions defined in clause 3 of the GNU Library General Public *)
(* License. This exception does not however invalidate any other reasons *)
(* why the executable file might be covered by the GNU Library General *)
(* Public License . *)

(* This library is distributed in the hope that it will be useful, *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307 *)
(* USA *)

(* You can contact the authour by sending email to *)
(* yori@users.sourceforge.net *)

(** Abstract syntax trees of regular expressions. *)
type regexp  =
  [ `Alt of regexp * regexp
  | `Seq of regexp * regexp
  | `Rep of regexp
  | `Repn of regexp * int * int option
  | `After of regexp   
  | `Before of regexp
  | `Epsilon
  | `Group of regexp
  | `OneChar
  | `String of UChar.t list
  | `Set of USet.t
  | `BoS
  | `EoS ]

(** Match semantics. *)
type match_semantics = [ `First | `Shortest | `Longest ]

(** Remove [`Group] from the regular expressions. *)
val no_group : regexp -> regexp

module type Type = sig
  type text
  type index
  type compiled_regexp

  module SubText : 
    SubText.Type with type ur_text = text and type ur_index = index

(** Compile regular expressions. *)
  val compile : regexp -> compiled_regexp

(** [regexp_match ?sem r t i] tries matching [r] and substrings
   of [t] beginning from [i].  If match successes,  [Some g] is 
   returned where [g] is the array containing the matched 
   string of [n]-th group in the [n]-element.  
   The matched string of the whole [r] is stored in the [0]-th element.  
   If matching fails, [None] is returned. *)
  val regexp_match : ?sem:match_semantics ->
    compiled_regexp -> text -> index -> SubText.t option array option

(** [string_match r t i] tests whether [r] can match a substring
   of [t] beginning from [i]. *)
  val string_match : compiled_regexp -> text -> index -> bool

(** [search_forward ?sem r t i] searches a substring of [t]
   matching [r] from [i].  The returned value is similar to 
   {!URe.Type.regexp_match}. *)
  val search_forward : ?sem:match_semantics ->
      compiled_regexp -> text -> index -> SubText.t option array option
end

module Make : functor (Text : UnicodeString.Type) ->
  Type with type text = Text.t and type index = Text.index
    
# 205 "camomileLibrary.mlip"
    end

  module UCharInfo : UCharInfo.Type
  
  module UNF : sig
    module type Type = UNF.Type
    module Make (Text : UnicodeString.Type) :
	Type with type text = Text.t and type index = Text.index
  end

  module UCol : sig
(** How variables are handled *)
    type variable_option = 
	[ `Blanked 
      | `Non_ignorable 
      | `Shifted
      | `Shift_Trimmed ]
	  
(** Strength of comparison.  For European languages, each strength
    roughly means as
    `Primary : Ignore accents and case
    `Secondary : Ignore case but accents are counted in.
    `Tertiary : Accents and case are counted in.
    For the case of `Shifted, `Shift_Trimmed, there is the fourth strength.
    `Quaternary : Variables such as - (hyphen) are counted in. *)
    type precision = [ `Primary | `Secondary | `Tertiary | `Quaternary ]

    module type Type = UCol.Type
    module Make (Text : UnicodeString.Type) :
	Type with type text = Text.t and type index = Text.index
  end

  module CaseMap : sig
    module type Type = CaseMap.Type
    module Make  (Text : UnicodeString.Type) : (Type with type text = Text.t)
  end

  module UReStr : UReStr.Interface

  module StringPrep : sig
    module type Type = StringPrep.Type
    module Make (Text : UnicodeString.Type) : (Type with type text = Text.t)
  end
end

(** All-in-one, configure once modules*)
module Make (Config : ConfigInt.Type) : Type with
      module OOChannel = OOChannel and
      module UChar = UChar and
      module USet = USet and
      module UMap = UMap and
      module UCharTbl = UCharTbl and
      module UnicodeString = UnicodeString and
      module UText = UText and
      module XString = XString and
      module SubText = SubText and
      module ULine = ULine and
      module Locale = Locale and
      module CharEncoding = CharEncoding.Configure(Config) and
      module UTF8 = UTF8 and
      module UTF16 = UTF16 and
      module UCS4 = UCS4 and
      module UPervasives = UPervasives and
      module URe = URe and
      module UCharInfo = UCharInfo.Make(Config) and
      module UNF.Make = UNF.Make(Config) and
      module UCol.Make = UCol.Make(Config) and
      module CaseMap.Make = CaseMap.Make(Config) and
      module UReStr = UReStr.Configure(Config) and
      module StringPrep.Make = StringPrep.Make(Config)
      
