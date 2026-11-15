import Diva.AbsInt.Framework
import Diva.AbsInt.SoundItv

/-! # Intervals as a `NumDomain` -/

namespace Diva.AbsInt

instance : NumDomain Itv where
  γ := Itv.mem
  top := Itv.top
  bot := Itv.bot
  leq := Itv.leq
  join := Itv.join
  meet := Itv.meet
  widen := Itv.widen
  const := Itv.singleton
  add := Itv.add
  sub := Itv.sub
  mul := Itv.mul
  div := Itv.div
  mod := Itv.mod
  cmpLt := Itv.cmpLt
  cmpLe := Itv.cmpLe
  cmpEq := Itv.cmpEq
  top_sound := Itv.mem_top
  bot_sound := Itv.mem_bot
  leq_sound := Itv.mem_leq
  join_sound_l := Itv.mem_join_l
  join_sound_r := Itv.mem_join_r
  meet_sound := Itv.mem_meet
  widen_sound_l := Itv.mem_widen_l
  widen_sound_r := Itv.mem_widen_r
  const_sound := Itv.mem_singleton
  add_sound := Itv.mem_add
  sub_sound := Itv.mem_sub
  mul_sound := Itv.mem_mul
  div_sound := Itv.mem_div
  mod_sound := Itv.mem_mod
  cmpLt_sound := Itv.cmpLt_sound
  cmpLe_sound := Itv.cmpLe_sound
  cmpEq_sound := Itv.cmpEq_sound

end Diva.AbsInt
