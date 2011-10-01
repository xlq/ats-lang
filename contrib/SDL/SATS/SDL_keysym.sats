(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS - Unleashing the Potential of Types!
** Copyright (C) 2002-2010 Hongwei Xi, Boston University
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
** Free Software Foundation; either version 2.1, or (at your option)  any
** later version.
** 
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
** 
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

// Author of the file: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
// Starting time: January, 2010

(* ****** ****** *)

abst@ype SDLKey = $extype"SDLKey"
//
castfn int_of_SDLKey (x: SDLKey):<> int
fun eq_SDLKey_SDLKey (x1: SDLKey, x2: SDLKey):<> bool
  = "atsctrb_eq_SDLKey_SDLKey"
overload = with eq_SDLKey_SDLKey
//
macdef SDLK_UNKNOWN = $extval (SDLKey, "SDLK_UNKNOWN")
macdef SDLK_FIRST = $extval (SDLKey, "SDLK_FIRST")
macdef SDLK_BACKSPACE = $extval (SDLKey, "SDLK_BACKSPACE")
macdef SDLK_TAB = $extval (SDLKey, "SDLK_TAB")
macdef SDLK_CLEAR = $extval (SDLKey, "SDLK_CLEAR")
macdef SDLK_RETURN = $extval (SDLKey, "SDLK_RETURN")
macdef SDLK_PAUSE = $extval (SDLKey, "SDLK_PAUSE")
macdef SDLK_ESCAPE = $extval (SDLKey, "SDLK_ESCAPE")
macdef SDLK_SPACE = $extval (SDLKey, "SDLK_SPACE")
macdef SDLK_EXCLAIM = $extval (SDLKey, "SDLK_EXCLAIM")
macdef SDLK_QUOTEDBL = $extval (SDLKey, "SDLK_QUOTEDBL")
macdef SDLK_HASH = $extval (SDLKey, "SDLK_HASH")
macdef SDLK_DOLLAR = $extval (SDLKey, "SDLK_DOLLAR")
macdef SDLK_AMPERSAND = $extval (SDLKey, "SDLK_AMPERSAND")
macdef SDLK_QUOTE = $extval (SDLKey, "SDLK_QUOTE")
macdef SDLK_LEFTPAREN = $extval (SDLKey, "SDLK_LEFTPAREN")
macdef SDLK_RIGHTPAREN = $extval (SDLKey, "SDLK_RIGHTPAREN")
macdef SDLK_ASTERISK = $extval (SDLKey, "SDLK_ASTERISK")
macdef SDLK_PLUS = $extval (SDLKey, "SDLK_PLUS")
macdef SDLK_COMMA = $extval (SDLKey, "SDLK_COMMA")
macdef SDLK_MINUS = $extval (SDLKey, "SDLK_MINUS")
macdef SDLK_PERIOD = $extval (SDLKey, "SDLK_PERIOD")
macdef SDLK_SLASH = $extval (SDLKey, "SDLK_SLASH")
macdef SDLK_0 = $extval (SDLKey, "SDLK_0")
macdef SDLK_1 = $extval (SDLKey, "SDLK_1")
macdef SDLK_2 = $extval (SDLKey, "SDLK_2")
macdef SDLK_3 = $extval (SDLKey, "SDLK_3")
macdef SDLK_4 = $extval (SDLKey, "SDLK_4")
macdef SDLK_5 = $extval (SDLKey, "SDLK_5")
macdef SDLK_6 = $extval (SDLKey, "SDLK_6")
macdef SDLK_7 = $extval (SDLKey, "SDLK_7")
macdef SDLK_8 = $extval (SDLKey, "SDLK_8")
macdef SDLK_9 = $extval (SDLKey, "SDLK_9")
macdef SDLK_COLON = $extval (SDLKey, "SDLK_COLON")
macdef SDLK_SEMICOLON = $extval (SDLKey, "SDLK_SEMICOLON")
macdef SDLK_LESS = $extval (SDLKey, "SDLK_LESS")
macdef SDLK_EQUALS = $extval (SDLKey, "SDLK_EQUALS")
macdef SDLK_GREATER = $extval (SDLKey, "SDLK_GREATER")
macdef SDLK_QUESTION = $extval (SDLKey, "SDLK_QUESTION")
macdef SDLK_AT = $extval (SDLKey, "SDLK_AT")
//
macdef SDLK_LEFTBRACKET = $extval (SDLKey, "SDLK_LEFTBRACKET")
macdef SDLK_BACKSLASH = $extval (SDLKey, "SDLK_BACKSLASH")
macdef SDLK_RIGHTBRACKET = $extval (SDLKey, "SDLK_RIGHTBRACKET")
macdef SDLK_CARET = $extval (SDLKey, "SDLK_CARET")
macdef SDLK_UNDERSCORE = $extval (SDLKey, "SDLK_UNDERSCORE")
macdef SDLK_BACKQUOTE = $extval (SDLKey, "SDLK_BACKQUOTE")
macdef SDLK_a = $extval (SDLKey, "SDLK_a")
macdef SDLK_b = $extval (SDLKey, "SDLK_b")
macdef SDLK_c = $extval (SDLKey, "SDLK_c")
macdef SDLK_d = $extval (SDLKey, "SDLK_d")
macdef SDLK_e = $extval (SDLKey, "SDLK_e")
macdef SDLK_f = $extval (SDLKey, "SDLK_f")
macdef SDLK_g = $extval (SDLKey, "SDLK_g")
macdef SDLK_h = $extval (SDLKey, "SDLK_h")
macdef SDLK_i = $extval (SDLKey, "SDLK_i")
macdef SDLK_j = $extval (SDLKey, "SDLK_j")
macdef SDLK_k = $extval (SDLKey, "SDLK_k")
macdef SDLK_l = $extval (SDLKey, "SDLK_l")
macdef SDLK_m = $extval (SDLKey, "SDLK_m")
macdef SDLK_n = $extval (SDLKey, "SDLK_n")
macdef SDLK_o = $extval (SDLKey, "SDLK_o")
macdef SDLK_p = $extval (SDLKey, "SDLK_p")
macdef SDLK_q = $extval (SDLKey, "SDLK_q")
macdef SDLK_r = $extval (SDLKey, "SDLK_r")
macdef SDLK_s = $extval (SDLKey, "SDLK_s")
macdef SDLK_t = $extval (SDLKey, "SDLK_t")
macdef SDLK_u = $extval (SDLKey, "SDLK_u")
macdef SDLK_v = $extval (SDLKey, "SDLK_v")
macdef SDLK_w = $extval (SDLKey, "SDLK_w")
macdef SDLK_x = $extval (SDLKey, "SDLK_x")
macdef SDLK_y = $extval (SDLKey, "SDLK_y")
macdef SDLK_z = $extval (SDLKey, "SDLK_z")
macdef SDLK_DELETE = $extval (SDLKey, "SDLK_DELETE")
//
macdef SDLK_WORLD_0 = $extval (SDLKey, "SDLK_WORLD_0")
macdef SDLK_WORLD_1 = $extval (SDLKey, "SDLK_WORLD_1")
macdef SDLK_WORLD_2 = $extval (SDLKey, "SDLK_WORLD_2")
macdef SDLK_WORLD_3 = $extval (SDLKey, "SDLK_WORLD_3")
macdef SDLK_WORLD_4 = $extval (SDLKey, "SDLK_WORLD_4")
macdef SDLK_WORLD_5 = $extval (SDLKey, "SDLK_WORLD_5")
macdef SDLK_WORLD_6 = $extval (SDLKey, "SDLK_WORLD_6")
macdef SDLK_WORLD_7 = $extval (SDLKey, "SDLK_WORLD_7")
macdef SDLK_WORLD_8 = $extval (SDLKey, "SDLK_WORLD_8")
macdef SDLK_WORLD_9 = $extval (SDLKey, "SDLK_WORLD_9")
macdef SDLK_WORLD_10 = $extval (SDLKey, "SDLK_WORLD_10")
macdef SDLK_WORLD_11 = $extval (SDLKey, "SDLK_WORLD_11")
macdef SDLK_WORLD_12 = $extval (SDLKey, "SDLK_WORLD_12")
macdef SDLK_WORLD_13 = $extval (SDLKey, "SDLK_WORLD_13")
macdef SDLK_WORLD_14 = $extval (SDLKey, "SDLK_WORLD_14")
macdef SDLK_WORLD_15 = $extval (SDLKey, "SDLK_WORLD_15")
macdef SDLK_WORLD_16 = $extval (SDLKey, "SDLK_WORLD_16")
macdef SDLK_WORLD_17 = $extval (SDLKey, "SDLK_WORLD_17")
macdef SDLK_WORLD_18 = $extval (SDLKey, "SDLK_WORLD_18")
macdef SDLK_WORLD_19 = $extval (SDLKey, "SDLK_WORLD_19")
macdef SDLK_WORLD_20 = $extval (SDLKey, "SDLK_WORLD_20")
macdef SDLK_WORLD_21 = $extval (SDLKey, "SDLK_WORLD_21")
macdef SDLK_WORLD_22 = $extval (SDLKey, "SDLK_WORLD_22")
macdef SDLK_WORLD_23 = $extval (SDLKey, "SDLK_WORLD_23")
macdef SDLK_WORLD_24 = $extval (SDLKey, "SDLK_WORLD_24")
macdef SDLK_WORLD_25 = $extval (SDLKey, "SDLK_WORLD_25")
macdef SDLK_WORLD_26 = $extval (SDLKey, "SDLK_WORLD_26")
macdef SDLK_WORLD_27 = $extval (SDLKey, "SDLK_WORLD_27")
macdef SDLK_WORLD_28 = $extval (SDLKey, "SDLK_WORLD_28")
macdef SDLK_WORLD_29 = $extval (SDLKey, "SDLK_WORLD_29")
macdef SDLK_WORLD_30 = $extval (SDLKey, "SDLK_WORLD_30")
macdef SDLK_WORLD_31 = $extval (SDLKey, "SDLK_WORLD_31")
macdef SDLK_WORLD_32 = $extval (SDLKey, "SDLK_WORLD_32")
macdef SDLK_WORLD_33 = $extval (SDLKey, "SDLK_WORLD_33")
macdef SDLK_WORLD_34 = $extval (SDLKey, "SDLK_WORLD_34")
macdef SDLK_WORLD_35 = $extval (SDLKey, "SDLK_WORLD_35")
macdef SDLK_WORLD_36 = $extval (SDLKey, "SDLK_WORLD_36")
macdef SDLK_WORLD_37 = $extval (SDLKey, "SDLK_WORLD_37")
macdef SDLK_WORLD_38 = $extval (SDLKey, "SDLK_WORLD_38")
macdef SDLK_WORLD_39 = $extval (SDLKey, "SDLK_WORLD_39")
macdef SDLK_WORLD_40 = $extval (SDLKey, "SDLK_WORLD_40")
macdef SDLK_WORLD_41 = $extval (SDLKey, "SDLK_WORLD_41")
macdef SDLK_WORLD_42 = $extval (SDLKey, "SDLK_WORLD_42")
macdef SDLK_WORLD_43 = $extval (SDLKey, "SDLK_WORLD_43")
macdef SDLK_WORLD_44 = $extval (SDLKey, "SDLK_WORLD_44")
macdef SDLK_WORLD_45 = $extval (SDLKey, "SDLK_WORLD_45")
macdef SDLK_WORLD_46 = $extval (SDLKey, "SDLK_WORLD_46")
macdef SDLK_WORLD_47 = $extval (SDLKey, "SDLK_WORLD_47")
macdef SDLK_WORLD_48 = $extval (SDLKey, "SDLK_WORLD_48")
macdef SDLK_WORLD_49 = $extval (SDLKey, "SDLK_WORLD_49")
macdef SDLK_WORLD_50 = $extval (SDLKey, "SDLK_WORLD_50")
macdef SDLK_WORLD_51 = $extval (SDLKey, "SDLK_WORLD_51")
macdef SDLK_WORLD_52 = $extval (SDLKey, "SDLK_WORLD_52")
macdef SDLK_WORLD_53 = $extval (SDLKey, "SDLK_WORLD_53")
macdef SDLK_WORLD_54 = $extval (SDLKey, "SDLK_WORLD_54")
macdef SDLK_WORLD_55 = $extval (SDLKey, "SDLK_WORLD_55")
macdef SDLK_WORLD_56 = $extval (SDLKey, "SDLK_WORLD_56")
macdef SDLK_WORLD_57 = $extval (SDLKey, "SDLK_WORLD_57")
macdef SDLK_WORLD_58 = $extval (SDLKey, "SDLK_WORLD_58")
macdef SDLK_WORLD_59 = $extval (SDLKey, "SDLK_WORLD_59")
macdef SDLK_WORLD_60 = $extval (SDLKey, "SDLK_WORLD_60")
macdef SDLK_WORLD_61 = $extval (SDLKey, "SDLK_WORLD_61")
macdef SDLK_WORLD_62 = $extval (SDLKey, "SDLK_WORLD_62")
macdef SDLK_WORLD_63 = $extval (SDLKey, "SDLK_WORLD_63")
macdef SDLK_WORLD_64 = $extval (SDLKey, "SDLK_WORLD_64")
macdef SDLK_WORLD_65 = $extval (SDLKey, "SDLK_WORLD_65")
macdef SDLK_WORLD_66 = $extval (SDLKey, "SDLK_WORLD_66")
macdef SDLK_WORLD_67 = $extval (SDLKey, "SDLK_WORLD_67")
macdef SDLK_WORLD_68 = $extval (SDLKey, "SDLK_WORLD_68")
macdef SDLK_WORLD_69 = $extval (SDLKey, "SDLK_WORLD_69")
macdef SDLK_WORLD_70 = $extval (SDLKey, "SDLK_WORLD_70")
macdef SDLK_WORLD_71 = $extval (SDLKey, "SDLK_WORLD_71")
macdef SDLK_WORLD_72 = $extval (SDLKey, "SDLK_WORLD_72")
macdef SDLK_WORLD_73 = $extval (SDLKey, "SDLK_WORLD_73")
macdef SDLK_WORLD_74 = $extval (SDLKey, "SDLK_WORLD_74")
macdef SDLK_WORLD_75 = $extval (SDLKey, "SDLK_WORLD_75")
macdef SDLK_WORLD_76 = $extval (SDLKey, "SDLK_WORLD_76")
macdef SDLK_WORLD_77 = $extval (SDLKey, "SDLK_WORLD_77")
macdef SDLK_WORLD_78 = $extval (SDLKey, "SDLK_WORLD_78")
macdef SDLK_WORLD_79 = $extval (SDLKey, "SDLK_WORLD_79")
macdef SDLK_WORLD_80 = $extval (SDLKey, "SDLK_WORLD_80")
macdef SDLK_WORLD_81 = $extval (SDLKey, "SDLK_WORLD_81")
macdef SDLK_WORLD_82 = $extval (SDLKey, "SDLK_WORLD_82")
macdef SDLK_WORLD_83 = $extval (SDLKey, "SDLK_WORLD_83")
macdef SDLK_WORLD_84 = $extval (SDLKey, "SDLK_WORLD_84")
macdef SDLK_WORLD_85 = $extval (SDLKey, "SDLK_WORLD_85")
macdef SDLK_WORLD_86 = $extval (SDLKey, "SDLK_WORLD_86")
macdef SDLK_WORLD_87 = $extval (SDLKey, "SDLK_WORLD_87")
macdef SDLK_WORLD_88 = $extval (SDLKey, "SDLK_WORLD_88")
macdef SDLK_WORLD_89 = $extval (SDLKey, "SDLK_WORLD_89")
macdef SDLK_WORLD_90 = $extval (SDLKey, "SDLK_WORLD_90")
macdef SDLK_WORLD_91 = $extval (SDLKey, "SDLK_WORLD_91")
macdef SDLK_WORLD_92 = $extval (SDLKey, "SDLK_WORLD_92")
macdef SDLK_WORLD_93 = $extval (SDLKey, "SDLK_WORLD_93")
macdef SDLK_WORLD_94 = $extval (SDLKey, "SDLK_WORLD_94")
macdef SDLK_WORLD_95 = $extval (SDLKey, "SDLK_WORLD_95")
//
macdef SDLK_KP0 = $extval (SDLKey, "SDLK_KP0")
macdef SDLK_KP1 = $extval (SDLKey, "SDLK_KP1")
macdef SDLK_KP2 = $extval (SDLKey, "SDLK_KP2")
macdef SDLK_KP3 = $extval (SDLKey, "SDLK_KP3")
macdef SDLK_KP4 = $extval (SDLKey, "SDLK_KP4")
macdef SDLK_KP5 = $extval (SDLKey, "SDLK_KP5")
macdef SDLK_KP6 = $extval (SDLKey, "SDLK_KP6")
macdef SDLK_KP7 = $extval (SDLKey, "SDLK_KP7")
macdef SDLK_KP8 = $extval (SDLKey, "SDLK_KP8")
macdef SDLK_KP9 = $extval (SDLKey, "SDLK_KP9")
macdef SDLK_KP_PERIOD = $extval (SDLKey, "SDLK_KP_PERIOD")
macdef SDLK_KP_DIVIDE = $extval (SDLKey, "SDLK_KP_DIVIDE")
macdef SDLK_KP_MULTIPLY = $extval (SDLKey, "SDLK_KP_MULTIPLY")
macdef SDLK_KP_MINUS = $extval (SDLKey, "SDLK_KP_MINUS")
macdef SDLK_KP_PLUS = $extval (SDLKey, "SDLK_KP_PLUS")
macdef SDLK_KP_ENTER = $extval (SDLKey, "SDLK_KP_ENTER")
macdef SDLK_KP_EQUALS = $extval (SDLKey, "SDLK_KP_EQUALS")
//
macdef SDLK_UP = $extval (SDLKey, "SDLK_UP")
macdef SDLK_DOWN = $extval (SDLKey, "SDLK_DOWN")
macdef SDLK_RIGHT = $extval (SDLKey, "SDLK_RIGHT")
macdef SDLK_LEFT = $extval (SDLKey, "SDLK_LEFT")
macdef SDLK_INSERT = $extval (SDLKey, "SDLK_INSERT")
macdef SDLK_HOME = $extval (SDLKey, "SDLK_HOME")
macdef SDLK_END = $extval (SDLKey, "SDLK_END")
macdef SDLK_PAGEUP = $extval (SDLKey, "SDLK_PAGEUP")
macdef SDLK_PAGEDOWN = $extval (SDLKey, "SDLK_PAGEDOWN")
//
macdef SDLK_F1 = $extval (SDLKey, "SDLK_F1")
macdef SDLK_F2 = $extval (SDLKey, "SDLK_F2")
macdef SDLK_F3 = $extval (SDLKey, "SDLK_F3")
macdef SDLK_F4 = $extval (SDLKey, "SDLK_F4")
macdef SDLK_F5 = $extval (SDLKey, "SDLK_F5")
macdef SDLK_F6 = $extval (SDLKey, "SDLK_F6")
macdef SDLK_F7 = $extval (SDLKey, "SDLK_F7")
macdef SDLK_F8 = $extval (SDLKey, "SDLK_F8")
macdef SDLK_F9 = $extval (SDLKey, "SDLK_F9")
macdef SDLK_F10 = $extval (SDLKey, "SDLK_F10")
macdef SDLK_F11 = $extval (SDLKey, "SDLK_F11")
macdef SDLK_F12 = $extval (SDLKey, "SDLK_F12")
macdef SDLK_F13 = $extval (SDLKey, "SDLK_F13")
macdef SDLK_F14 = $extval (SDLKey, "SDLK_F14")
macdef SDLK_F15 = $extval (SDLKey, "SDLK_F15")
//
macdef SDLK_NUMLOCK = $extval (SDLKey, "SDLK_NUMLOCK")
macdef SDLK_CAPSLOCK = $extval (SDLKey, "SDLK_CAPSLOCK")
macdef SDLK_SCROLLOCK = $extval (SDLKey, "SDLK_SCROLLOCK")
macdef SDLK_RSHIFT = $extval (SDLKey, "SDLK_RSHIFT")
macdef SDLK_LSHIFT = $extval (SDLKey, "SDLK_LSHIFT")
macdef SDLK_RCTRL = $extval (SDLKey, "SDLK_RCTRL")
macdef SDLK_LCTRL = $extval (SDLKey, "SDLK_LCTRL")
macdef SDLK_RALT = $extval (SDLKey, "SDLK_RALT")
macdef SDLK_LALT = $extval (SDLKey, "SDLK_LALT")
macdef SDLK_RMETA = $extval (SDLKey, "SDLK_RMETA")
macdef SDLK_LMETA = $extval (SDLKey, "SDLK_LMETA")
macdef SDLK_LSUPER = $extval (SDLKey, "SDLK_LSUPER")
macdef SDLK_RSUPER = $extval (SDLKey, "SDLK_RSUPER")
macdef SDLK_MODE = $extval (SDLKey, "SDLK_MODE")
macdef SDLK_COMPOSE = $extval (SDLKey, "SDLK_COMPOSE")
macdef SDLK_HELP = $extval (SDLKey, "SDLK_HELP")
macdef SDLK_PRINT = $extval (SDLKey, "SDLK_PRINT")
macdef SDLK_SYSREQ = $extval (SDLKey, "SDLK_SYSREQ")
macdef SDLK_BREAK = $extval (SDLKey, "SDLK_BREAK")
macdef SDLK_MENU = $extval (SDLKey, "SDLK_MENU")
macdef SDLK_POWER = $extval (SDLKey, "SDLK_POWER")
macdef SDLK_EURO = $extval (SDLKey, "SDLK_EURO")
macdef SDLK_UNDO = $extval (SDLKey, "SDLK_UNDO")
//
macdef SDLK_LAST = $extval (SDLKey, "SDLK_LAST")

(* ****** ****** *)

abst@ype SDLMod = $extype"SDLMod"
//
macdef KMOD_NONE = $extval (SDLMod, "KMOD_NONE")
macdef KMOD_LSHIFT = $extval (SDLMod, "KMOD_LSHIFT")
macdef KMOD_RSHIFT = $extval (SDLMod, "KMOD_RSHIFT")
macdef KMOD_LCTRL = $extval (SDLMod, "KMOD_LCTRL")
macdef KMOD_RCTRL = $extval (SDLMod, "KMOD_RCTRL")
macdef KMOD_LALT = $extval (SDLMod, "KMOD_LALT")
macdef KMOD_RALT = $extval (SDLMod, "KMOD_RALT")
macdef KMOD_LMETA = $extval (SDLMod, "KMOD_LMETA")
macdef KMOD_RMETA = $extval (SDLMod, "KMOD_RMETA")
macdef KMOD_NUM = $extval (SDLMod, "KMOD_NUM")
macdef KMOD_CAPS = $extval (SDLMod, "KMOD_CAPS")
macdef KMOD_MODE = $extval (SDLMod, "KMOD_MODE")
macdef KMOD_RESERVED = $extval (SDLMod, "KMOD_RESERVED")
//
macdef KMOD_CTRL = $extval (SDLMod, "KMOD_CTRL")
macdef KMOD_SHIFT = $extval (SDLMod, "KMOD_SHIFT")
macdef KMOD_ALT = $extval (SDLMod, "KMOD_ALT")
macdef KMOD_META = $extval (SDLMod, "KMOD_META")

(* ****** ****** *)

(* end of [SDL_keysym.sats] *)
