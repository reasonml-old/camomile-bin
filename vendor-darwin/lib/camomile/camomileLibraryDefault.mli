(** modules with default configuration. *)
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

open CamomileLibrary

module Config : ConfigInt.Type

module Camomile : Type with
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
